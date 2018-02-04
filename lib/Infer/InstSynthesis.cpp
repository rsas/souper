// Copyright 2015 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "souper/Extractor/KLEEBuilder.h"
#include "souper/Infer/InstSynthesis.h"

using namespace souper;
using namespace llvm;

namespace {

static cl::opt<unsigned> DebugLevel("souper-synthesis-debug-level",
    cl::desc("Synthesis debug level (default=0). "
    "The larger the number is, the more fine-grained debug "
    "information will be printed"),
    cl::init(0));
static cl::opt<int> CmdMaxCompNum("souper-synthesis-comp-num",
    cl::desc("Maximum number of components (default=all)"),
    cl::init(-1));
static cl::opt<std::string> CmdUserCompKinds("souper-synthesis-comps",
    cl::Hidden,
    cl::desc("Comma-separated list of instruction synthesis component kinds"),
    cl::init(""));
static cl::opt<bool> IgnoreCost("souper-synthesis-ignore-cost",
    cl::Hidden,
    cl::desc("Ignore cand inst cost (default=false)"),
    cl::init(false));
static cl::opt<unsigned> MaxWiringAttempts("souper-synthesis-wiring-iterations",
    cl::Hidden,
    cl::desc("Number of convergence iterations of wirings that contain constants"),
    cl::init(100));

}

namespace souper {

static const std::string BLOCK_PREFIX = "blockpred";
static const std::string INPUT_PREFIX = "in_";
static const std::string OUTPUT_PREFIX = "out_";
static const std::string LOC_PREFIX = "loc_";
static const std::string LOC_SEP = "_";
static const std::string COMP_INPUT_PREFIX = "compin_";
static const std::string CONST_PREFIX = "const_";

std::error_code InstSynthesis::synthesize(SMTLIBSolver *SMTSolver,
                                          const BlockPCs &BPCs,
                                          const std::vector<InstMapping> &PCs,
                                          Inst *TargetLHS, Inst *&RHS,
                                          InstContext &IC, unsigned Timeout) {
  std::error_code EC;

  // init local refs
  LSMTSolver = SMTSolver;
  LBPCs = &BPCs;
  LPCs = &PCs;
  LIC = &IC;
  LTimeout = Timeout;

  TrueConst = IC.getConst(APInt(1, true));
  FalseConst = IC.getConst(APInt(1, false));
  LHS = TargetLHS;
  RHS = 0;

  // The order is important
  initInputVars();
  setCompLibrary();
  filterFixedWidthIntrinsicComps();
  initOutput();
  initComponents();
  initConstComponents();

  N = I.size();

  int LHSCost = cost(LHS);

  if (DebugLevel > 0) {
    llvm::outs() << "; starting synthesis for LHS\n";
    PrintReplacementLHS(llvm::outs(), BPCs, PCs, LHS, Context);
    if (DebugLevel > 2)
      printInitInfo();
  }

  //
  setInvalidWirings();

  // Init a new set of path conditions
  std::vector<InstMapping> WiringPCs;

  // Acyclicity constraint
  WiringPCs.emplace_back(getAcyclicityConstraint(), TrueConst);

  // Location constraints of inputs, components' inputs and outputs
  WiringPCs.emplace_back(getInputLocVarConstraint(), TrueConst);
  WiringPCs.emplace_back(getLocVarConstraint(P, 0, M), TrueConst);
  WiringPCs.emplace_back(getLocVarConstraint(R, N, M), TrueConst);

  // Different constraints
  //WiringPCs.emplace_back(getConstInequalityConstraint(), TrueConst);
  WiringPCs.emplace_back(getComponentConstInputConstraint(), TrueConst);
  WiringPCs.emplace_back(getComponentInputConstraint(), TrueConst);
  WiringPCs.emplace_back(getComponentInputSymmetryConstraint(), TrueConst);
  WiringPCs.emplace_back(getComponentOutputConstraint(), TrueConst);

  // Create the main wiring query (aka connectivity contraint)
  Inst *WiringQuery = getConnectivityConstraint();

  // Initial concrete input set S.
  // With every new input set that proves a synthesised program is invalid,
  // we'll have to copy WiringQuery and replace its inputs with the new
  // concrete values from S
  std::vector<std::map<Inst *, Inst *>> S;
  // Ask the solver for a set of initial concrete inputs.
  EC = getInitialConcreteInputs(S, 2);
  if (EC)
    return EC;

  // Not-working candidate programs that contain constants must be forbidden
  // explicitly because constants are not constrainted by the inputs. Still, it
  // can take many iterations to converge. Therefore, we limit the number
  // of attempts per such a candidate wiring via cmd flag MaxWiringAttempts
  // (default value: 10)
  std::map<ProgramWiring, unsigned> NotWorkingConstWirings;

  // Set the maximum number of components
  int MaxCompNum;
  if (CmdMaxCompNum >= 0)
    MaxCompNum = CmdMaxCompNum;
  else
    MaxCompNum = Comps.size();
  if (!IgnoreCost && MaxCompNum >= LHSCost)
    MaxCompNum = LHSCost-1;
  // MaxCompNum can be negative when e.g. LHSCost is 0
  if (MaxCompNum > (int)Comps.size())
    MaxCompNum = Comps.size();

  // Iterative synthesis loop with increasing number of components
  unsigned TotalRefinements = 0;
  unsigned Refinements = 0;
  for (int J = 1; J <= MaxCompNum; ++J) {
    if (DebugLevel > 1)
      llvm::outs() << "++++++++++++++++++++ "
                   << "synthesizing using " << J << " component(s)"
                   << " ++++++++++++++++++++\n";
    // Init fresh loop PCs
    auto LoopPCs = WiringPCs;
    // Constrain output locaction
    LoopPCs.emplace_back(getLocVarConstraint({O}, N+J-1, N+J-1), TrueConst);

    // --------------------------------------------------------------------------
    // -------------- Counterexample driven synthesis loop ----------------------
    // --------------------------------------------------------------------------
    Refinements = 0;
    while (true) {
      Inst *Query = TrueConst;
      // Put each set of concrete inputs into a separate copy of the WiringQuery
      // Solve the synthesis constraint.
      Query = initConcreteInputWirings(Query, WiringQuery, Refinements, S);

      // Each solution corresponds to a syntactically distinct and well-formed
      // straight-line program obtained by composition of given components
      std::vector<Inst *> ModelInsts;
      std::vector<llvm::APInt> ModelVals;
      InstMapping Mapping(Query, TrueConst);
      // Negate the query to get a SAT model.
      // Don't use original BPCs/PCs, they are useless
      std::string QueryStr = BuildQuery({}, LoopPCs, Mapping,
                                        &ModelInsts, /*Negate=*/true);
      if (QueryStr.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool IsSat;
      if (DebugLevel > 1)
        llvm::outs() << "solving synthesis constraint.. ";
      EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                    &ModelVals, Timeout);
      if (EC)
        return EC;

      // No valid wiring exists for the target comp number
      if (!IsSat) {
        if (DebugLevel > 1)
          llvm::outs() << "UNSAT\n";
        break;
      }

      if (DebugLevel > 1)
        llvm::outs() << "SAT\n";

      ProgramWiring CandWiring;
      std::map<LocVar, llvm::APInt> ConstValMap;
      Inst *Cand = createInstFromModel(std::make_pair(ModelInsts, ModelVals),
                                       CandWiring, ConstValMap);
      if (!Cand)
        report_fatal_error("synthesis bug: creating inst from a model failed");

      if (DebugLevel > 1) {
        llvm::outs() << "candidate:\n";
        PrintReplacementRHS(llvm::outs(), Cand, Context);
      }

      if (!CandSeen.insert(Cand).second)
        report_fatal_error("synthesis bug: candidate has been seen already");

      // The synthesis loop assumes that each component has a cost of one.

      // The synthesis loop assumes that each component has a cost of one.
      // However, this is not the case for all components (e.g., bswap).
      // Moreover, some components can be comprised of two components to meet
      // the DefaultWidth criteria. For example, if the DefaultWidth is 32
      // and the engine uses ule during synthesis, the instantiation of ule
      // would be zext(ule) to 32 and sext(ule) to 32. Therefore, the cost
      // of such a component would be two and not one. To address this issue,
      // we forbid candidates that have no cost benefit and continue to search
      // for others
      int CandCost = cost(Cand);
      int Benefit = LHSCost - CandCost;
      if (!IgnoreCost && Benefit <= 0) {
        if (DebugLevel > 1)
          llvm::outs() << "candidate has no benefit\n";
        forbidInvalidCandWiring(CandWiring, LoopPCs);
        continue;
      }

      // Does the candidate work for all inputs?
      // Use original BPCs/PCs
      ModelInsts.clear();
      ModelVals.clear();
      InstMapping CandMapping(LHS, Cand);
      QueryStr = BuildQuery(BPCs, PCs, CandMapping, &ModelInsts, /*Negate=*/false);
      if (QueryStr.empty())
        return std::make_error_code(std::errc::value_too_large);
      EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                    &ModelVals, Timeout);
      if (EC)
        return EC;

      // Success
      if (!IsSat) {
        if (DebugLevel > 1)
          llvm::outs() << "success:\n";
        if (DebugLevel > 0) {
          PrintReplacementRHS(llvm::outs(), Cand, Context);
          llvm::outs() << "; LHS cost = " << LHSCost
                       << ", RHS cost = " << CandCost
                       << ", benefit = " << (Benefit > 0 ? Benefit : 0)
                       << "\n";
          llvm::outs() << "; comps = " << J
                       << ", cex = " << S.size()
                       << ", iterations = " << TotalRefinements << "\n";
        }
        RHS = Cand;
        return EC;
      }

      Refinements++;
      TotalRefinements++;
      if (DebugLevel > 1)
        llvm::outs() << "didn't work for all inputs "
                     << "(#cex: "<< S.size()+1 << ", "
                     << "refinement: " << Refinements << ")\n";
      // Parse input counterexamples from the model
      std::map<Inst *, Inst *> ValueMap;
      for (unsigned J = 0; J < ModelInsts.size(); ++J) {
        auto Name = ModelInsts[J]->Name;
        if (Name.find(INPUT_PREFIX) != std::string::npos) {
          auto In = ModelInsts[J];
          auto Val = ModelVals[J];
          ValueMap[In] = IC.getConst(Val);
          if (DebugLevel > 2)
            llvm::outs() << "counterexample: " << Name << " = " << Val << "\n";
        }
      }
      
      // Add counterexamples to S
      S.push_back(ValueMap);

      // Constants are not constrained by the inputs, thus, we must explicitly
      // constrain the not-working cand wiring incl. the constants and forbid
      // the wiring completely after MaxWiringAttempts is reached
      if (hasConst(Cand)) {
        constrainConstWiring(Cand, CandWiring, NotWorkingConstWirings,
                             ConstValMap, LoopPCs, WiringPCs);
      }
    }
  }

  if (DebugLevel > 0) {
    llvm::outs() << "; no valid wiring found";
    unsigned Cnt = 0;
    for (auto const &Wiring : NotWorkingConstWirings)
      if (Wiring.second >= MaxWiringAttempts)
        Cnt++;
    if (Cnt)
      llvm::outs() << " (" << Cnt << " wiring(s) with constants reached "
                   << MaxWiringAttempts << " MaxWiringAttempts)";
    llvm::outs() << "\n";
    llvm::outs() << "; failed, comps = " << MaxCompNum
                 << ", cex = " << S.size()
                 << ", iterations = " << TotalRefinements << "\n";
  }

  return EC;
}

void InstSynthesis::setCompLibrary() {
  if (!CmdMaxCompNum)
    return;
  // First, choose which components to use
  std::vector<Component> InitComps, InitConstComps;
  if (CmdUserCompKinds.size()) {
    std::vector<Inst::Kind> Kinds;
    // Parse user-provided component kind strings
    for (auto KindStr : splitString(CmdUserCompKinds.c_str())) {
      Inst::Kind K = Inst::getKind(KindStr);
      if (KindStr == Inst::getKindName(Inst::Const)) // Special case
        InitConstComps.push_back(Component{Inst::Const, 0, {}});
      else if (K == Inst::ZExt || K == Inst::SExt || K == Inst::Trunc)
        report_fatal_error("don't use zext/sext/trunc explicitly");
      else if (K == Inst::None)
        report_fatal_error("unknown instruction: " + KindStr);
      else if (UnsupportedCompKinds.count(K))
        report_fatal_error("unsupported instruction: " + KindStr);
      else
        Kinds.push_back(K);
    }
    for (auto const &Comp : CompLibrary)
      for (auto const &Kind : Kinds)
        if (Comp.Kind == Kind)
          InitComps.push_back(Comp);
  } else {
    InitComps = CompLibrary;
    // one constant per component
    //for (auto const &Comp : CompLibrary)
    //  InitConstComps.push_back(Component{Inst::Const, 0, {}});
    InitConstComps.push_back(Component{Inst::Const, 0, {}});
    InitConstComps.push_back(Component{Inst::Const, 0, {}});
  }
  for (auto const &In : Inputs) {
    if (In->Width == DefaultWidth)
      continue;
    Comps.push_back(Component{Inst::ZExt, DefaultWidth, {In->Width}});
    Comps.push_back(Component{Inst::SExt, DefaultWidth, {In->Width}});
  }
  // Second, for each input/constant create a component of DefaultWidth
  for (auto &Comp : InitComps) {
    if (!Comp.Width)
      Comp.Width = DefaultWidth;
    for (auto &OpWidth : Comp.OpWidths)
      if (!OpWidth)
        OpWidth = DefaultWidth;
    Comps.push_back(Comp);
  }
  for (auto &Const : InitConstComps) {
    if (!Const.Width)
      Const.Width = DefaultWidth;
    ConstComps.push_back(Const);
  }
  // Third, create one trunc comp to match the output width if necessary
  if (LHS->Width < DefaultWidth)
    Comps.push_back(Component{Inst::Trunc, LHS->Width, {DefaultWidth}});
}

void InstSynthesis::initInputVars() {
  std::vector<Inst *> Tmp;
  getInputVars(LHS, Tmp);
  // Remove duplicates
  std::set<Inst *> TmpSet;
  for (auto const &I : Tmp)
    if (TmpSet.insert(I).second)
      Inputs.push_back(I);
  // Set DefaultWidth to the max width of the inputs
  for (auto In : Inputs)
    if (In->Width > DefaultWidth)
      DefaultWidth = In->Width;
  if (!DefaultWidth || DefaultWidth < LHS->Width)
    DefaultWidth = LHS->Width;
  for (unsigned J = 0; J < Inputs.size(); ++J) {
    // Note that location variable 0_0 is not used
    LocVar In = std::make_pair(0, J+1);
    std::string LocVarStr = getLocVarStr(In, LOC_PREFIX);
    Inst *Loc = LIC->createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Add input location to I
    I.emplace_back(In, Loc);
    // Update input name
    LocVarStr = getLocVarStr(In, INPUT_PREFIX);
    Inputs[J]->Name = LocVarStr;
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Update CompInstMap map with concrete Inst
    CompInstMap[In] = Inputs[J];
  }
}

void InstSynthesis::initConstComponents() {
  for (unsigned J = 0; J < ConstComps.size(); ++J) {
    auto const &Comp = ConstComps[J];
    // Treat constant comps as ordinary inputs
    LocVar In = std::make_pair(0, Inputs.size()+J+1);
    std::string LocVarStr = getLocVarStr(In, LOC_PREFIX);
    Inst *Loc = LIC->createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Add constant component location to I
    I.emplace_back(In, Loc);
    // Update name
    LocVarStr = getLocVarStr(In, CONST_PREFIX);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Update CompInstMap map with concrete Inst
    assert(Comp.Width && "const comp width not set");
    Loc = LIC->createVar(Comp.Width, LocVarStr);
    CompInstMap[In] = Loc;
  }
}

void InstSynthesis::filterFixedWidthIntrinsicComps() {
  // CtPop/BSwap/Cttz/Ctlz require specific widths
  for (auto It = Comps.begin(); It != Comps.end();) {
    assert(It->Width && "comp width not set");
    if (It->Kind == Inst::BSwap)
      if (It->Width != 16 && It->Width != 32 && It->Width != 64) {
        It = Comps.erase(It);
        continue;
      }
    if ((It->Kind == Inst::CtPop) || (It->Kind == Inst::Ctlz) ||
        (It->Kind == Inst::Cttz))
      if (It->Width != 8 && It->Width != 16 && It->Width != 32 &&
          It->Width != 64 && It->Width != 256) {
        It = Comps.erase(It);
        continue;
      }
    ++It;
  }
}

void InstSynthesis::initComponents() {
  for (unsigned J = 0; J < Comps.size(); ++J) {
    auto const &Comp = Comps[J];
    std::string LocVarStr;
    // First, init component inputs
    std::vector<Inst *> CompOps;
    std::vector<LocVar> OpsLocVar;
    for (unsigned K = 0; K < Comp.OpWidths.size(); ++K) {
      LocVar In = std::make_pair(J+1, K+1);
      LocVarStr = getLocVarStr(In, LOC_PREFIX);
      Inst *Loc = LIC->createVar(LocInstWidth, LocVarStr);
      LocInstMap[LocVarStr] = std::make_pair(In, Loc);
      // Add component input location to P
      P.emplace_back(In, Loc);
      // Create concrete component input encoded as a fresh variable
      LocVarStr = getLocVarStr(In, COMP_INPUT_PREFIX);
      assert(Comp.OpWidths[K] && "op width not set");
      assert(Comp.OpWidths[K] <= DefaultWidth || Comp.Kind == Inst::Select);
      Inst *OpInst;
      if (Comp.Kind == Inst::ZExt || Comp.Kind == Inst::SExt)
        OpInst = LIC->createVar(Comp.OpWidths[K], LocVarStr);
      else
        OpInst = LIC->createVar(DefaultWidth, LocVarStr);
      LocInstMap[LocVarStr] = std::make_pair(In, OpInst);
      // Update CompInstMap map with concrete Inst
      CompInstMap[In] = OpInst;
      CompOps.push_back(OpInst);
      OpsLocVar.push_back(In);
    }
    // Store all input locations
    CompOpLocVars.push_back(OpsLocVar);

    // Second, init component output
    LocVar Out = std::make_pair(J+1, 0);
    LocVarStr = getLocVarStr(Out, LOC_PREFIX);
    Inst *Loc = LIC->createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(Out, Loc);
    // Add component output to R.
    R.emplace_back(Out, Loc);

    // Third, instantiate the component (aka Inst)
    assert(Comp.Width && "comp width not set");
    Inst *CompInst;
    if (Comp.Kind == Inst::Select) {
      Inst *C = LIC->getInst(Inst::Trunc, 1, {CompOps[0]});
      CompInst = LIC->getInst(Comp.Kind, Comp.Width, {C, CompOps[1], CompOps[2]});
    } else {
      CompInst = LIC->getInst(Comp.Kind, Comp.Width, CompOps);
      if (Comp.Width < DefaultWidth && Comp.Kind != Inst::Trunc)
        CompInst = LIC->getInst(Inst::ZExt, DefaultWidth, {CompInst});
    }
    // Update CompInstMap map with concrete Inst
    CompInstMap[Out] = CompInst;
  }
}

void InstSynthesis::initOutput() {
  LocVar Out = std::make_pair(Comps.size()+1, 0);
  std::string LocVarStr = getLocVarStr(Out, LOC_PREFIX);
  Inst *Loc = LIC->createVar(LocInstWidth, LocVarStr);
  // Set output location O
  O = std::make_pair(Out, Loc);
  LocInstMap[LocVarStr] = O;
  // Update CompInstMap map with concrete Inst
  LocVarStr = getLocVarStr(Out, OUTPUT_PREFIX);
  CompInstMap[Out] = LHS;
}

void InstSynthesis::printInitInfo() {
  llvm::outs() << "inputs: " << Inputs.size() << ", "
               << "inputs range: [0, " << Inputs.size() << ")\n"
               << "constants: " << ConstComps.size() << "\n"
               << "constants range: [" << Inputs.size() << ", " << I.size() << ")\n";
  llvm::outs() << "N: " << N << ", M: " << M << "\n";
  llvm::outs() << "default width: " << DefaultWidth << "\n";
  llvm::outs() << "output width: " << LHS->Width << "\n";
  llvm::outs() << "component library (#" << Comps.size() << "): ";
  for (auto const &Comp : Comps) {
    llvm::outs() << Inst::getKindName(Comp.Kind) << " (" << Comp.Width << ", { ";
    for (auto const &Width : Comp.OpWidths)
      llvm::outs() << Width << " ";
    llvm::outs() << "}); ";
  }
  if (Comps.size())
    llvm::outs() << "\n";
  llvm::outs() << "const components: ";
  for (auto const &Comp : ConstComps)
    llvm::outs() << "const (" << Comp.Width << "); ";
  llvm::outs() << "\n";
  llvm::outs() << "I: ";
  for (auto const &In : I)
    llvm::outs() << getLocVarStr(In.first) << " ";
  llvm::outs() << "\n";
  llvm::outs() << "P: ";
  for (auto const &In : P)
    llvm::outs() << getLocVarStr(In.first) << " ";
  llvm::outs() << "\n";
  llvm::outs() << "R: ";
  for (auto const &In : R)
    llvm::outs() << getLocVarStr(In.first) << " ";
  llvm::outs() << "\n";
  llvm::outs() << "O: " << getLocVarStr(O.first) << "\n";
}

void InstSynthesis::setInvalidWirings() {
  // Forbid width mismatches
  std::vector<LocInst> Tmp(P.begin(), P.end());
  Tmp.push_back(O);
  // -> Compare inputs
  for (auto const &In : I) {
    unsigned Width = CompInstMap[In.first]->Width;
    // with component inputs and the output
    for (auto const &L_x : Tmp) {
      if (Width == CompInstMap[L_x.first]->Width) {
        if (L_x.first.second == 0)
          continue;
        if (Comps[L_x.first.first-1].Kind != Inst::Select)
          continue;
        if (L_x.first.second != 1)
          continue;
      }
      InvalidWirings.insert(std::make_pair(In.first, L_x.first));
    }
  }
  // -> Compare outputs
  for (auto const &L_y : R) {
    unsigned Width = CompInstMap[L_y.first]->Width;
    // with component inputs and the output
    for (auto const &L_x : Tmp) {
      // Don't constrain yourself
      if (L_y.first.first == L_x.first.first)
        continue;
      if (Width == CompInstMap[L_x.first]->Width)
        continue;
      InvalidWirings.insert(std::make_pair(L_y.first, L_x.first));
    }
    // with components' outputs
    for (auto const &L_x : R) {
      // Don't constrain yourself
      if (L_y == L_x)
        continue;
      InvalidWirings.insert(std::make_pair(L_y.first, L_x.first));
    }
  }

  // Don't wire a component's input to its output.
  for (auto const &L_x : P)
    for (auto const &L_y : R)
      if (L_x.first.first == L_y.first.first)
        InvalidWirings.insert(std::make_pair(L_x.first, L_y.first));
  // Don't wire input to a component's output
  for (auto const &L_x : I)
    for (auto const &L_y : R)
      InvalidWirings.insert(std::make_pair(L_x.first, L_y.first));
  // Don't wire a component's input to the output
  for (auto const &L_x : P)
    InvalidWirings.insert(std::make_pair(L_x.first, O.first));
  // Don't wire a component's input(s) to other component
  // input(s) directly. The solver should decide through other
  // wirings if such connections are possible. For example, a solver
  // could find out that 1_1 = 0_ and 1_2 = 0_1 => 1_1 = 1_2, making
  // the explicit wiring test (1_1 = 1_2) redundant.
  for (unsigned J = 0; J < P.size(); ++J)
    for (unsigned K = J+1; K < P.size(); ++K)
      InvalidWirings.insert(std::make_pair(P[J].first, P[K].first));
  // Similarly, don't wire an input with other inputs(s) explicitly
  for (unsigned J = 0; J < I.size(); ++J)
    for (unsigned K = J+1; K < I.size(); ++K)
      InvalidWirings.insert(std::make_pair(I[J].first, I[K].first));
}

Inst *InstSynthesis::getDistinctConstraint(const std::vector<LocInst> &Left,
                                           const std::vector<LocInst> &Right,
                                           const std::string &Desc) {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2) {
    if (Desc != "")
      llvm::outs() << "distinct constraints for " << Desc << ":\n";
    else
      llvm::outs() << "distinct constraints:\n";
  }
  for (unsigned J = 0; J < Left.size(); ++J) {
    auto const &L_x = Left[J];
    unsigned K = 0;
    if (Left == Right)
      K = J+1;
    for (; K < Right.size(); ++K) {
      auto const &L_y = Right[K];
      if (L_x == L_y)
        continue;
      Inst *Ne = LIC->getInst(Inst::Ne, 1, {L_x.second, L_y.second});
      Ret = LIC->getInst(Inst::And, 1, {Ret, Ne});
      if (DebugLevel > 2)
        llvm::outs() << getLocVarStr(L_x.first) << " != "
                     << getLocVarStr(L_y.first) << "\n";
    }
  }

  return Ret;
}

Inst *InstSynthesis::getAcyclicityConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "acyclicity constraints:\n";
  // Component inputs
  for (auto const &L_x : P) {
    // Grab a component's output LocInst
    auto const &L_y = getCompOutLocInst(L_x);
    if (DebugLevel > 2)
      llvm::outs() << getLocVarStr(L_x.first) << " < "
                   << getLocVarStr(L_y.first) << "\n";
    Inst *Ult = LIC->getInst(Inst::Ult, 1, {L_x.second, L_y.second});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Ult});
    //
    Inst *Ult1 = LIC->getInst(Inst::Ult, 1, {L_x.second, O.second});
    Inst *Ult2 = LIC->getInst(Inst::Ule, 1, {L_y.second, O.second});
    Inst *IsZero = LIC->getInst(Inst::Eq, 1, {Ult1, FalseConst});
    Inst *Implies = LIC->getInst(Inst::Or, 1, {IsZero, Ult2});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Implies});
    //
  }

  return Ret;
}

Inst *InstSynthesis::getInputLocVarConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "input location constraints:\n";
  // All inputs
  for (unsigned J = 0; J < N; ++J) {
    auto const &L_x = I[J];
    if (DebugLevel > 2)
      llvm::outs() << getLocVarStr(L_x.first) << " == " << J << "\n";
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, LIC->getConst(APInt(LocInstWidth, J))});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Eq});
  }

  return Ret;
}

Inst *InstSynthesis::getLocVarConstraint(const std::vector<LocInst> &L,
                                         int Begin, int End) {
  Inst *Ret = TrueConst;

  assert(Begin <= End);

  for (const auto &Tmp : L) {
    if (Begin != End) {
      Inst *Ult = LIC->getInst(Inst::Ult, 1,
          {Tmp.second, LIC->getConst(APInt(LocInstWidth, Begin))});
      Inst *Ne = LIC->getInst(Inst::Eq, 1, {Ult, FalseConst});
      if (DebugLevel > 2)
        llvm::outs() << Begin << " <= " << getLocVarStr(Tmp.first);
      Ret = LIC->getInst(Inst::And, 1, {Ret, Ne});

      Ult = LIC->getInst(Inst::Ult, 1,
                         {Tmp.second, LIC->getConst(APInt(LocInstWidth, End))});
      if (DebugLevel > 2)
        llvm::outs() << " < " << End << "\n";

      Ret = LIC->getInst(Inst::And, 1, {Ret, Ult});
    } else {
      if (DebugLevel > 2)
        llvm::outs() << getLocVarStr(Tmp.first) << " == " << End << "\n";;
      Inst *Eq = LIC->getInst(Inst::Eq, 1, {Tmp.second,
                                            LIC->getConst(APInt(LocInstWidth, End))});
      Ret = LIC->getInst(Inst::And, 1, {Ret, Eq});
    }
  }

  return Ret;
}

Inst *InstSynthesis::getConnectivityConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 3)
    llvm::outs() << "possible wirings:\n";
  // inputs -> component inputs
  for (unsigned J = 0; J < I.size(); ++J) {
    for (unsigned K = 0; K < P.size(); ++K) {
      auto const &L_x = I[J];
      auto const &L_y = P[K];
      // Skip invalid wirings
      if (isWiringInvalid(L_x.first, L_y.first))
        continue;
      auto const &X = CompInstMap[L_x.first];
      auto const &Y = CompInstMap[L_y.first];
      if (DebugLevel > 3)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << "\n";
      // (l_x == l_y) => x == y
      Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, L_y.second});
      Eq = LIC->getInst(Inst::And, 1, {Eq, LIC->getInst(Inst::Ult, 1,
                                                        {L_y.second, O.second})});
      Eq = LIC->getInst(Inst::Eq, 1, {Eq, FalseConst});
      Inst *Eq2 = LIC->getInst(Inst::Eq, 1, {X, Y});
      Inst *Implies = LIC->getInst(Inst::Or, 1, {Eq, Eq2});
      Ret = LIC->getInst(Inst::And, 1, {Ret, Implies});
    }
  }
  // component outputs -> component inputs
  for (unsigned J = 0; J < R.size(); ++J) {
    for (unsigned K = 0; K < P.size(); ++K) {
      auto const &L_x = R[J];
      auto const &L_y = P[K];
      // Skip invalid wirings
      if (isWiringInvalid(L_x.first, L_y.first))
        continue;
      if (L_x.first.first == L_y.first.first)
        continue;
      auto const &X = CompInstMap[L_x.first];
      auto const &Y = CompInstMap[L_y.first];
      if (DebugLevel > 3)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << "\n";
      // (l_x == l_y) => x == y
      Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, L_y.second});
      Eq = LIC->getInst(Inst::Eq, 1, {Eq, FalseConst});
      Inst *Eq2 = LIC->getInst(Inst::Eq, 1, {X, Y});
      Inst *Implies = LIC->getInst(Inst::Or, 1, {Eq, Eq2});
      Ret = LIC->getInst(Inst::And, 1, {Ret, Implies});
    }
  }
  // output -> inputs and component outputs
  std::vector<LocInst> Tmp(I.begin(), I.end());
  Tmp.insert(Tmp.end(), R.begin(), R.end());
  for (auto const &L_y : Tmp) {
    auto const &X = CompInstMap[O.first];
    auto const &Y = CompInstMap[L_y.first];
    // Skip invalid wirings
    if (isWiringInvalid(O.first, L_y.first))
      continue;
    if (DebugLevel > 3)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(L_y.first) << "\n";
    // (l_x == l_y) => x == y
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {O.second, L_y.second});
    Eq = LIC->getInst(Inst::Eq, 1, {Eq, FalseConst});
    Inst *Eq2 = LIC->getInst(Inst::Eq, 1, {X, Y});
    Inst *Implies = LIC->getInst(Inst::Or, 1, {Eq, Eq2});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Implies});
  }

  return Ret;
}

Inst *InstSynthesis::getComponentInputConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "component input constraints (implies):\n";
  for (auto const &L_x : P) {
    Inst *Ante = FalseConst;
    // Inputs
    for (auto const &In : I) {
      if (isWiringInvalid(L_x.first, In.first))
        continue;
      Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, In.second});
      Ante = LIC->getInst(Inst::Or, 1, {Ante, Eq});
      if (DebugLevel > 2)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(In.first) << " || ";
    }
    // Component outputs
    for (auto const &L_y : R) {
      // Don't constrain yourself
      if (L_x.first.first == L_y.first.first)
        continue;
      if (isWiringInvalid(L_x.first, L_y.first))
        continue;
      Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, L_y.second});
      Ante = LIC->getInst(Inst::Or, 1, {Ante, Eq});
      if (DebugLevel > 2)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << " || ";
    }
    if (DebugLevel > 2)
      llvm::outs() << "false\n";
    if (Ante == FalseConst)
      report_fatal_error("no input available for " + getLocVarStr(L_x.first));

    // Adding implies
    Inst *Ult1 = LIC->getInst(Inst::Ult, 1, {L_x.second, O.second});
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {Ult1, FalseConst});
    Inst *Implies = LIC->getInst(Inst::Or, 1, {Eq, Ante});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Implies});
    //

    //Ret = LIC->getInst(Inst::And, 1, {Ret, Ante});
  }

  return Ret;
}

Inst *InstSynthesis::getComponentOutputConstraint() {
  Inst *Ret = FalseConst;

  if (DebugLevel > 2)
    llvm::outs() << "component output constraints:\n";
  // Inputs
  for (auto const &In : I) {
    if (isWiringInvalid(In.first, O.first))
      continue;
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {O.second, In.second});
    Ret = LIC->getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugLevel > 2)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(In.first) << " || ";
  }
  // Component outputs
  for (auto const &L_y : R) {
    if (isWiringInvalid(L_y.first, O.first))
      continue;
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {O.second, L_y.second});
    Ret = LIC->getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugLevel > 2)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(L_y.first) << " || ";
  }
  if (DebugLevel > 2)
    llvm::outs() << "false\n";

  return Ret;
}

Inst *InstSynthesis::getConstInequalityConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "const input inequality constraints:\n";

  for (unsigned J = Inputs.size(); J < N; ++J) {
    auto const &L_x = I[J];
    unsigned Width = CompInstMap[L_x.first]->Width;
    for (unsigned K = J+1; K < N; ++K) {
      auto const &L_y = I[K];
      if (Width != CompInstMap[L_y.first]->Width)
        continue;
      auto const &X = CompInstMap[L_x.first];
      auto const &Y = CompInstMap[L_y.first];
      if (DebugLevel > 3)
        llvm::outs() << getLocVarStr(L_x.first) << " != "
                     << getLocVarStr(L_y.first) << "\n";
      Inst *Ne = LIC->getInst(Inst::Ne, 1, {X, Y});
      Ret = LIC->getInst(Inst::And, 1, {Ret, Ne});
    }
  }

  return Ret;
}

#if 0
Inst *InstSynthesis::getComponentConstInputConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "component const input constraints:\n";

  for (auto const &E : CompOpLocVars) {
    Inst *CompAnte = TrueConst;
    for (auto const &CompIn : E) {
      auto LocVarStr = getLocVarStr(CompIn, LOC_PREFIX);
      Inst *ConstRange = getLocVarConstraint({LocInstMap[LocVarStr]}, Inputs.size(), N);
      CompAnte = LIC->getInst(Inst::And, 1, {CompAnte, ConstRange});
    }
    if (DebugLevel > 2)
      llvm::outs() << "=> false\n";
    Inst *Ne = LIC->getInst(Inst::Eq, 1, {CompAnte, FalseConst});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Ne});
  }

  return Ret;
}
#else
Inst *InstSynthesis::getComponentConstInputConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "component const input constraints:\n";

  // Forbid a component's operands to be constants only.
  // An exemplary query that must hold true for a single component
  // with two inputs and two constants:
  // true && (false || (compin_1 == const_1) || (compin_1 == const_2))
  //      && (false || (compin_2 == const_1) || (compin_2 == const_2)) == false
  for (auto const &E : CompOpLocVars) {
    Inst *CompAnte = TrueConst;
    for (auto const &CompIn : E) {
      Inst *Ante = FalseConst;
      auto LocVarStr = getLocVarStr(CompIn, LOC_PREFIX);
      for (auto const &In : I) {
        if (!isInputConst(In.first))
          continue;
        if (isWiringInvalid(CompIn, In.first))
          continue;
        Inst *Eq = LIC->getInst(Inst::Eq, 1, {LocInstMap[LocVarStr].second, In.second});
        Ante = LIC->getInst(Inst::Or, 1, {Ante, Eq});
        if (DebugLevel > 2)
          llvm::outs() << getLocVarStr(CompIn) << " == "
                       << getLocVarStr(In.first) << " || ";
      }
      if (DebugLevel > 2)
        llvm::outs() << "false\n";
      CompAnte = LIC->getInst(Inst::And, 1, {CompAnte, Ante});
    }
    if (DebugLevel > 2)
      llvm::outs() << "false\n";
    Inst *Ne = LIC->getInst(Inst::Eq, 1, {CompAnte, FalseConst});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Ne});
  }

  return Ret;
}
#endif

Inst *InstSynthesis::getComponentInputSymmetryConstraint() {
  Inst *Ret = TrueConst;

  if (DebugLevel > 2)
    llvm::outs() << "component input symmetry constraints:\n";

  for (auto const &E : CompOpLocVars) {
    LocVar OutLocVar = std::make_pair(E[0].first, 0);
    Inst *OutInst = CompInstMap[OutLocVar];
    if (!SymmetricComps.count(OutInst->K))
      continue;
    assert(OutInst->Ops.size() == 2);
    assert(E.size() == 2);
    if (DebugLevel > 3)
      llvm::outs() << getLocVarStr(E[0]) << " < "
                   << getLocVarStr(E[1]) << "\n";
    auto LocVarStrLeft = getLocVarStr(E[0], LOC_PREFIX);
    auto LocVarStrRight = getLocVarStr(E[1], LOC_PREFIX);
    Inst *FirstOp = LocInstMap[LocVarStrLeft].second;
    Inst *SecondOp = LocInstMap[LocVarStrRight].second;

    Inst *Ult = LIC->getInst(Inst::Ult, 1, {FirstOp, SecondOp});
    Ret = LIC->getInst(Inst::And, 1, {Ret, Ult});
  }

  return Ret;
}


Inst *InstSynthesis::getInstCopy(Inst *I,
                                 std::map<Inst *, Inst *> &InstCache,
                                 std::map<Block *, Block *> &BlockCache) {
  std::vector<Inst *> Ops;
  for (auto const &Op : I->Ops)
    Ops.push_back(getInstCopy(Op, InstCache, BlockCache));

  if (I->K == Inst::Var) {
    if (!InstCache.count(I))
      return I;
    // Replace
    return InstCache.at(I);
  } else if (I->K == Inst::Phi) {
    if (!BlockCache.count(I->B)) {
      auto BlockCopy = LIC->createBlock(I->B->Preds);
      std::vector<Inst *> PredVars;
      for (auto &PredVar : I->B->PredVars) {
        if (InstCache.count(PredVar))
          PredVars.emplace_back(InstCache[PredVar]);
        else
          PredVars.emplace_back(PredVar);
      }
      BlockCopy->PredVars = PredVars;
      BlockCache[I->B] = BlockCopy;
      return LIC->getPhi(BlockCopy, Ops);
    } else
      return LIC->getPhi(BlockCache.at(I->B), Ops);
  } else if (I->K == Inst::Const || I->K == Inst::UntypedConst) {
    return I;
  } else {
    return LIC->getInst(I->K, I->Width, Ops);
  }
}

Inst *InstSynthesis::createInstFromModel(const SolverSolution &Solution,
                                         ProgramWiring &CandWiring,
                                         std::map<LocVar, llvm::APInt> &ConstValMap) {
  LineLocVarMap LineWiring;
  LocVar OutLoc = parseWiringModel(Solution, LineWiring, ConstValMap);

  if (DebugLevel > 3) {
    llvm::outs() << "line\tlocations\n";
    for (auto const &E : LineWiring) {
      llvm::outs() << E.first << "\t";
      for (auto const &Loc : E.second)
        llvm::outs() << getLocVarStr(Loc) << " ";
      llvm::outs() << "\n";
    }
  }

  if (!CompInstMap.count(OutLoc))
    report_fatal_error("synthesis bug: output location not wired");
  auto Left = getLocVarStr(O.first, LOC_PREFIX);
  auto Right = getLocVarStr(OutLoc, LOC_PREFIX);
  CandWiring.emplace_back(LocInstMap[Left], LocInstMap[Right]);

  if (DebugLevel > 3)
    llvm::outs() << "found valid wiring, output "
                 << getLocVarStr(OutLoc) << ".\n";

  auto OpLocs = getOpLocs(OutLoc);
  if (DebugLevel > 3) {
    llvm::outs() << "creating program from wiring\n";
    llvm::outs() << "- starting with OutLoc " << getLocVarStr(OutLoc)
                 << ", OpLocs { ";
    for (auto const &OpLoc : OpLocs)
      llvm::outs() << getLocVarStr(OpLoc) << " ";
    llvm::outs() << "}\n";
  }
  Inst *Res = createInstFromWiring(OutLoc, OpLocs, LineWiring,
                                   ConstValMap, CandWiring);
  assert(Res && "creating instruction from wiring failed");

  return Res;
}

Inst *InstSynthesis::createInstFromWiring(
      const LocVar &OutLoc,
      const std::vector<LocVar> &OpLocs,
      const LineLocVarMap &LineWiring,
      const std::map<LocVar, llvm::APInt> &ConstValMap,
      ProgramWiring &CandWiring) {
  std::vector<Inst *> Ops;

  // Create operand instructions recursively
  for (auto const &OpLoc : OpLocs) {
    LocVar Match = getWiringLocVar(OpLoc, LineWiring);
    assert(CompInstMap.count(Match) && "unknown matching location variable");
    if (!CompInstMap.count(Match))
      report_fatal_error("synthesis bug: component input " +
                         getLocVarStr(OpLoc) + " not wired");
    // Store wiring locations
    auto Left = getLocVarStr(OpLoc, LOC_PREFIX);
    auto Right = getLocVarStr(Match, LOC_PREFIX);
    CandWiring.emplace_back(LocInstMap[Left], LocInstMap[Right]);
    // Get operand locations of the wiring location
    auto Res = getOpLocs(Match);
    if (DebugLevel > 3) {
      llvm::outs() << "- continue with OutLoc " << getLocVarStr(Match)
                   << ", OpLocs {";
      for (auto const &R : Res)
        llvm::outs() << getLocVarStr(R) << " ";
      llvm::outs() << "}\n";
    }
    // Recurse
    Inst *Op = createInstFromWiring(Match, Res, LineWiring,
                                    ConstValMap, CandWiring);
    // Store result
    Ops.push_back(Op);
  }

  // It it a constant?
  if (ConstValMap.count(OutLoc)) {
    if (DebugLevel > 3)
      llvm::outs() << "- creating constant inst " << getLocVarStr(OutLoc)
                   << " with value " << ConstValMap.at(OutLoc) << "\n";
    return LIC->getConst(ConstValMap.at(OutLoc));
  }
  // Is it an input?
  if (OutLoc.first == 0) {
    if (DebugLevel > 3)
      llvm::outs() << "- creating input inst " << getLocVarStr(OutLoc) << "\n";
    return CompInstMap[OutLoc];
  }
  // Grab the target component
  Component Comp = Comps[OutLoc.first-1];
  assert(OutLoc.first >= 1 && "invalid component location variable");
  assert((Ops.size() == Comp.OpWidths.size()) && "op num mismatch");
  if (DebugLevel > 3) {
    llvm::outs() << "- creating inst " << Inst::getKindName(Comp.Kind)
                 << ", width " << Comp.Width << "\n";
    llvm::outs() << "before clean-up:\n";
    PrintReplacementRHS(llvm::outs(), LIC->getInst(Comp.Kind, Comp.Width, Ops),
                        Context);
  }
  // Sanity checks
  if (Ops.size() == 2 && Ops[0]->K == Inst::Const && Ops[1]->K == Inst::Const)
    report_fatal_error("inst operands are constants!");
  assert(Comp.Width == 1 || Comp.Width == DefaultWidth ||
         Comp.Width == LHS->Width);
  // Create instruction
  if (Comp.Kind == Inst::Select) {
    Ops[0] = LIC->getInst(Inst::Trunc, 1, {Ops[0]});
    return createCleanInst(Comp.Kind, Comp.Width, Ops);
  } if (Comp.Width < DefaultWidth && Comp.Kind != Inst::Trunc) {
    Inst *Ret = createCleanInst(Comp.Kind, Comp.Width, Ops);
    return LIC->getInst(Inst::ZExt, DefaultWidth, {Ret});
  } else
    return createCleanInst(Comp.Kind, Comp.Width, Ops);
}

LocVar InstSynthesis::parseWiringModel(const SolverSolution &Solution,
                                       LineLocVarMap &LineWiring,
                                       std::map<LocVar, llvm::APInt> &ConstValMap) {
  unsigned Counter = 0;
  LocVar OutLocVar;
  bool OutLocSet = false;
  unsigned OutWidth = CompInstMap[O.first]->Width;

  auto ModelInsts = Solution.first;
  auto ModelVals = Solution.second;
  assert(ModelVals.size() && "there must models to parse");
  for (unsigned J = 0; J < ModelInsts.size(); ++J) {
    auto Name = ModelInsts[J]->Name;
    //llvm::outs() << "Name: " << Name << "\n";
    //llvm::outs() << "Value: " << ModelVals[J].getZExtValue() << "\n";
    // Parse location variable models
    if (Name.find(LOC_PREFIX) != std::string::npos) {
      LocVar Loc = getLocVarFromStr(Name.substr(LOC_PREFIX.size()));
      unsigned Line = (unsigned)ModelVals[J].getZExtValue();
      if (LineWiring.count(Line)) {
        // Look for the output wiring. It can be a component's output or any
        // of the inputs. Note that due to scalability reasons, we haven't
        // encoded width mismatches and other invalid wirings as constraints,
        // thus, we need to perform sanity checks on candidates
        if (!OutLocSet) {
          // Is it output? If yes, there should be only one component output
          // and/or any input on that line
          auto const &VarMap = LineWiring[Line];
          if (Loc == O.first) {
            for (auto const &CandLocVar : VarMap) {
              if (!isWiringInvalid(O.first, CandLocVar)) {
                OutLocVar = CandLocVar;
                OutLocSet = true;
                break;
              }
            }
          // Check if the output is stored already. If yes, then take the new
          // location if the width matches
          } else if (VarMap.count(O.first) && !isWiringInvalid(O.first, Loc)) {
            OutLocVar = Loc;
            OutLocSet = true;
          }
        }
        LineWiring[Line].insert(Loc);
      } else {
        LineWiring[Line] = {Loc};
      }
      Counter++;
    // Parse constant models
    } else if (Name.find(CONST_PREFIX) != std::string::npos) {
      LocVar Loc = getLocVarFromStr(Name.substr(CONST_PREFIX.size()));
      ConstValMap[Loc] = ModelVals[J];
    }
  }
  assert(OutLocSet && "no matching location for the output");
  assert(LineWiring.size() <= M && "the output location must be <= M");
  assert(Counter == L.size() && "invalid number of locations in the model");

  return OutLocVar;
}

LocVar InstSynthesis::getWiringLocVar(const LocVar &OpLoc,
                                      const LineLocVarMap &LineWiring) {
  LocVar Match;
  bool FoundMatch = false;

  if (DebugLevel > 3)
    llvm::outs() << "- looking for OpLoc wiring "
                 << getLocVarStr(OpLoc) << "\n";
  for (auto const &E : LineWiring) {
    if (E.second.count(OpLoc)) {
      if (DebugLevel > 3)
        llvm::outs() << "- found wiring input on line " << E.first << ", taking ";
      for (auto const &In : E.second) {
        // Take either input, constant, or component output of matching width
        if ((In.first == 0 || In.second == 0) && !isWiringInvalid(In, OpLoc)) {
          Match = In;
          if (DebugLevel > 3)
            llvm::outs() << getLocVarStr(Match);
          FoundMatch = true;
          break;
        }
      }
      if (DebugLevel > 3)
        llvm::outs() << "\n";
    }
    if (FoundMatch)
      break;
  }

  return Match;
}

Inst *InstSynthesis::createCleanInst(Inst::Kind Kind, unsigned Width,
                                     std::vector<Inst *> &Ops) {
  switch (Kind) {
  case Inst::Add:
  case Inst::AddNSW:
  case Inst::AddNUW:
  case Inst::AddNW:
    if (Ops[0] == LIC->getConst(APInt(Width, 0)))
      return Ops[1];
    else if (Ops[1] == LIC->getConst(APInt(Width, 0)))
      return Ops[0];
    break;

  case Inst::Sub:
  case Inst::SubNSW:
  case Inst::SubNUW:
  case Inst::SubNW:
    if (Ops[0] == Ops[1])
      return LIC->getConst(APInt(Width, 0));
    else if (Ops[1] == LIC->getConst(APInt(Width, 0)))
      return Ops[0];
    break;

  case Inst::Mul:
  case Inst::MulNSW:
  case Inst::MulNUW:
  case Inst::MulNW:
    if (Ops[0] == LIC->getConst(APInt(Width, 1)))
      return Ops[1];
    else if (Ops[1] == LIC->getConst(APInt(Width, 1)))
      return Ops[0];
    break;

  case Inst::UDiv:
  case Inst::SDiv:
  case Inst::UDivExact:
  case Inst::SDivExact:
    if (Ops[1] == LIC->getConst(APInt(Width, 1)))
      return Ops[0];
    break;

  case Inst::And:
  case Inst::Or:
    if (Ops[0] == Ops[1])
      return Ops[0];
    break;

  case Inst::Xor:
    if (Ops[0] == Ops[1])
      return LIC->getConst(APInt(Width, 0));
    break;

  case Inst::Shl:
  case Inst::ShlNSW:
  case Inst::ShlNUW:
  case Inst::ShlNW:
  case Inst::LShr:
  case Inst::LShrExact:
  case Inst::AShr:
  case Inst::AShrExact:
    if (Ops[1] == LIC->getConst(APInt(Width, 0)))
      return Ops[0];
    break;

  case Inst::Select:
    if (Ops[1] == Ops[2])
      return Ops[1];
    if (Ops[0]->K == Inst::Trunc)
      if (Ops[0]->Ops[0]->K == Inst::ZExt ||
          Ops[0]->Ops[0]->K == Inst::SExt)
        if (Ops[0]->Ops[0]->Ops[0]->Width == 1)
          Ops[0] = Ops[0]->Ops[0]->Ops[0];
    break;

  case Inst::ZExt:
  case Inst::SExt:
  case Inst::Trunc:
    if (Width == Ops[0]->Width)
      return Ops[0];
    if (Ops[0]->K == Inst::Const)
      return LIC->getConst(APInt(Width, Ops[0]->Val.getZExtValue()));
    if (Ops[0]->K == Inst::Const)
      return LIC->getConst(APInt(Width, Ops[0]->Val.getZExtValue()));
    if (Ops[0]->K == Inst::ZExt || Ops[0]->K == Inst::SExt || Ops[0]->K == Inst::Trunc)
      if (Width == Ops[0]->Ops[0]->Width)
        return Ops[0]->Ops[0];
    break;

  case Inst::Eq:
    if (Ops[0] == Ops[1])
      return TrueConst;
    break;

  case Inst::Ne:
    if (Ops[0] == Ops[1])
      return FalseConst;
    break;

  case Inst::Ult:
  case Inst::Slt:
    if (Ops[0] == Ops[1])
      return FalseConst;
    break;

  case Inst::CtPop:
  case Inst::BSwap:
    if (Ops[0] == LIC->getConst(APInt(Width, 0)))
      return LIC->getConst(APInt(Width, 0));
    break;

  case Inst::Cttz:
  case Inst::Ctlz:
    if (Ops[0] == LIC->getConst(APInt(Width, 0)))
      return LIC->getConst(APInt(Width, Width));
    break;

  default:
    break;
  }

  return LIC->getInst(Kind, Width, Ops);
}

void InstSynthesis::getInputVars(Inst *I, std::vector<Inst *> &InputVars) {
  if (I->K == Inst::Var)
    InputVars.push_back(I);
  for (auto Iz : I->orderedOps())
    getInputVars(Iz, InputVars);
}

std::string InstSynthesis::getLocVarStr(const LocVar &Loc,
                                        const std::string Prefix) {
  std::string Post;
  // Print component's name in debug mode
  if (DebugLevel > 0 && Prefix.empty()) {
    std::string Str;
    auto Width = CompInstMap[Loc]->Width;
    if (Loc == O.first) {
      Str = "output";
    } else if (Loc.first == 0 && Loc.second > Inputs.size()) {
      Str = "const";
    } else if (Loc.first == 0) {
      Str = "input";
    } else {
      auto const &Comp = Comps[Loc.first-1];
      if (Comp.Kind != CompInstMap[Loc]->K && Loc.second == 0)
        Str = std::string(Inst::getKindName(CompInstMap[Loc]->K)) + ",";
      Str += std::string(Inst::getKindName(Comp.Kind));
    }
    Post = " (" + Str + ",i" + std::to_string(Width) + ")";
  }

  return Prefix + std::to_string(Loc.first) + LOC_SEP
                + std::to_string(Loc.second) + Post;
}

LocVar InstSynthesis::getLocVarFromStr(const std::string &Str) {
  assert(Str.size() >= 2+LOC_SEP.size());
  size_t Index = Str.find(LOC_SEP);
  assert(Index != std::string::npos);
  assert(Index+1 < Str.size());
  unsigned Left = std::stoi(Str.substr(0, Index));
  unsigned Right = std::stoi(Str.substr(Index+1));
  LocVar Loc = std::make_pair(Left, Right);
  assert(CompInstMap.count(Loc) && "parsed invalid location variable");

  return Loc;
}

std::vector<LocVar> InstSynthesis::getOpLocs(const LocVar &Loc) {
  std::vector<LocVar> Res;

  // Inputs have no operands
  if (Loc.first == 0)
    return Res;
  assert(Loc.first >= 1 && "invalid locatoin variable");
  auto const &Comp = Comps[Loc.first-1];
  for (unsigned J = 0; J < Comp.OpWidths.size(); ++J) {
    LocVar Tmp = std::make_pair(Loc.first, J+1);
    assert(CompInstMap.count(Tmp) && "unknown comp input's location variable");
    Res.push_back(Tmp);
  }

  return Res;
}

LocInst InstSynthesis::getCompOutLocInst(const LocInst &CompIn) {
    // Grab a component's output LocInst
    std::string LocVarStr = LOC_PREFIX + std::to_string(CompIn.first.first)
                                       + LOC_SEP + "0";
    assert(LocInstMap.count(LocVarStr) && "unknown location variable");

    return LocInstMap[LocVarStr];
}

std::vector<std::string> InstSynthesis::splitString(const char *S, char Del) {
  std::vector<std::string> Res;

  do {
    const char *Begin = S;
    while (*S && *S != Del)
      S++;
    Res.push_back(std::string(Begin, S));
  } while (*S++ != 0);

  return Res;
}

bool InstSynthesis::isWiringInvalid(const LocVar &Left, const LocVar &Right) {
  return (InvalidWirings.count(std::make_pair(Left, Right)) ||
          InvalidWirings.count(std::make_pair(Right, Left)));
}

bool InstSynthesis::isInputConst(const LocVar &Loc) {
  if (Loc.first != 0)
    return false;

  return LocInstMap.count(getLocVarStr(Loc, CONST_PREFIX)) != 0;
}

void InstSynthesis::forbidInvalidCandWiring(const ProgramWiring &CandWiring,
                                            std::vector<InstMapping> &LoopPCs) {
  Inst *Ante = TrueConst;
  if (DebugLevel > 2)
    llvm::outs() << "not-working candidate, constraining wiring\n";
  for (auto const &Pair : CandWiring) {
    auto const &L_x = Pair.first;
    auto const &L_y = Pair.second;
    if (DebugLevel > 3)
      llvm::outs() << getLocVarStr(L_x.first) << " == "
                   << getLocVarStr(L_y.first) << "\n";
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, L_y.second});
    Ante = LIC->getInst(Inst::And, 1, {Ante, Eq});
  }
  LoopPCs.emplace_back(Ante, FalseConst);
}

int InstSynthesis::costHelper(Inst *I, std::set<Inst *> &Visited) {
  if (!Visited.insert(I).second)
    return 0;
  int Cost = Inst::getCost(I->K);
  for (auto Op : I->Ops)
    Cost += costHelper(Op, Visited);
  return Cost;
}

int InstSynthesis::cost(Inst *I) {
  std::set<Inst *> Visited;
  return costHelper(I, Visited);
}

bool InstSynthesis::hasConst(Inst *I) {
  if (I->K == Inst::Const)
    return true;
  bool Res = false;
  for (auto Iz : I->orderedOps())
    Res |= hasConst(Iz);
  return Res;
}

std::error_code InstSynthesis::getInitialConcreteInputs(std::vector<std::map<Inst *, Inst *>> &S,
                                                        unsigned NumInputs) {
  std::error_code EC;

  auto InputPCs = *LPCs;
  for (unsigned J = 0; J < NumInputs; ++J) {
    std::vector<Inst *> ModelInsts;
    std::vector<llvm::APInt> ModelVals;
    InstMapping Mapping(LHS, LIC->createVar(LHS->Width, "output"));
    // Negate the query to get a SAT model
    std::string QueryStr = BuildQuery(*LBPCs, InputPCs, Mapping,
                                      &ModelInsts, /*Negate=*/true);
    if (QueryStr.empty())
      return std::make_error_code(std::errc::value_too_large);
    bool IsSat;
    EC = LSMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                   &ModelVals, LTimeout);
    if (EC)
      return EC;

    if (!IsSat)
      break;

    std::map<Inst *, Inst *> ConcreteValues;
    for (unsigned K = 0; K < ModelInsts.size(); ++K) {
      auto Name = ModelInsts[K]->Name;
      if (Name.find(INPUT_PREFIX) != std::string::npos) {
        auto Input = ModelInsts[K];
        ConcreteValues[Input] = LIC->getConst(ModelVals[K]);
        Inst *Ne = LIC->getInst(Inst::Ne, 1, {Input, LIC->getConst(ModelVals[K])});
        InputPCs.emplace_back(Ne, TrueConst);
      } else if (Name.find(BLOCK_PREFIX) != std::string::npos) {
        auto Input = ModelInsts[K];
        ConcreteValues[Input] = LIC->getConst(ModelVals[K]);
      }
    }
    S.push_back(ConcreteValues);
  }

  return EC;
}


std::error_code InstSynthesis::getConcreteLHSOutput(std::map<Inst *, Inst *> &ConcreteInputs,
                                                    llvm::APInt &Result) {

  std::error_code EC;

  std::vector<Inst *> ModelInsts;
  std::vector<llvm::APInt> ModelVals;
  std::map<Block *, Block *> BlockCache;
  Inst *Copy = getInstCopy(LHS, ConcreteInputs, BlockCache);
  InstMapping Mapping(Copy, LIC->createVar(LHS->Width, "output"));
  // Negate the query to get a SAT model
  std::string QueryStr = BuildQuery(*LBPCs, *LPCs, Mapping,
                                    &ModelInsts, /*Negate=*/true);
  if (QueryStr.empty())
    return std::make_error_code(std::errc::value_too_large);
  bool IsSat;
  EC = LSMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                 &ModelVals, LTimeout);
  if (EC || !IsSat)
    return EC;

  for (unsigned K = 0; K < ModelInsts.size(); ++K) {
    auto Name = ModelInsts[K]->Name;
    if (Name.find("output") != std::string::npos) {
      Result = ModelVals[K];
      break;
    }
  }

  return EC;
}

Inst *InstSynthesis::initConcreteInputWirings(Inst *Query, Inst *WiringQuery,
                                              unsigned Refinements,
                                              std::vector<std::map<Inst *, Inst *>> &S) {
  for (unsigned K = 0; K < S.size(); ++K) {
    auto &ValueMap = S[K];
    if (DebugLevel > 2) {
      for (auto const &Value : ValueMap) {
        if (Value.first->Name.find(COMP_INPUT_PREFIX) != std::string::npos)
          continue;
        llvm::outs() << "setting " << Value.first->Name
                     << " to " << Value.second->Val << "\n";
      }
    }
    if (K > 0) {
      // Starting with the second concrete input set,
      // copy component input variables for query separation
      for (auto const &E : LocInstMap) {
        if (E.first.find(COMP_INPUT_PREFIX) != std::string::npos) {
          auto In = E.second.second;
          std::string Name = E.first + LOC_SEP + std::to_string(Refinements);
          ValueMap[In] = LIC->createVar(In->Width, Name);
        }
      }
    }
    std::map<Block *, Block *> BlockCache;
    Inst *Copy = getInstCopy(WiringQuery, ValueMap, BlockCache);
    Query = LIC->getInst(Inst::And, 1, {Query, Copy});
    Query->DemandedBits = APInt::getAllOnesValue(Query->Width);
  }

  return Query;
}

void InstSynthesis::constrainConstWiring(const Inst *Cand,
                                         const ProgramWiring &CandWiring,
                                         std::map<ProgramWiring, unsigned> &NotWorkingConstWirings,
                                         const std::map<LocVar, llvm::APInt> &ConstValMap,
                                         std::vector<InstMapping> &LoopPCs,
                                         std::vector<InstMapping> &WiringPCs) {
  Inst *Ante = TrueConst;

  unsigned Cnt = 1;
  auto WI = NotWorkingConstWirings.find(CandWiring);
  if (WI == NotWorkingConstWirings.end()) {
    NotWorkingConstWirings[CandWiring] = Cnt;
  } else {
    WI->second++;
    Cnt = WI->second;
  }
  if (DebugLevel > 2) {
    llvm::outs() << "cand with constants, constraining wiring\n";
    if (WI->second == MaxWiringAttempts)
      llvm::outs() << "cand reached MaxWiringAttempts "
        << "(" << MaxWiringAttempts << "), forbidding\n";
  }
  for (auto const &Pair : CandWiring) {
    auto const &L_x = Pair.first;
    auto const &L_y = Pair.second;
    if (DebugLevel > 3)
      llvm::outs() << getLocVarStr(L_x.first) << " == "
        << getLocVarStr(L_y.first) << "\n";
    // Constrain the wiring
    Inst *Eq = LIC->getInst(Inst::Eq, 1, {L_x.second, L_y.second});
    Ante = LIC->getInst(Inst::And, 1, {Ante, Eq});
    // If the cand is a constant, forbid the wiring immediately
    if (Cand->K == Inst::Const)
      continue;
    // Otherwise, constrain the wiring with constants as long as
    // MaxWiringAttempts is not reached. Afterwards, the wiring
    // will be banned (without constants)
    if (Cnt < MaxWiringAttempts) {
      auto CI = ConstValMap.find(L_y.first);
      if (CI == ConstValMap.end())
        continue;
      auto const &Cons = CompInstMap[L_y.first];
      if (DebugLevel > 2)
        llvm::outs() << "with constant " << getLocVarStr(L_y.first)
          << " == " << CI->second << "\n";
      Eq = LIC->getInst(Inst::Eq, 1, {Cons, LIC->getConst(CI->second)});
      Ante = LIC->getInst(Inst::And, 1, {Ante, Eq});
    }
  }
  LoopPCs.emplace_back(Ante, FalseConst);
  WiringPCs.emplace_back(Ante, FalseConst);
}

}
