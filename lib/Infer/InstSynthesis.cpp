// Copyright 2014 The Souper Authors. All rights reserved.
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

static cl::opt<bool> DebugSynthesis("souper-debug-synthesis",
    cl::desc("Debug instruction synthesis (default=false)"),
    cl::init(false));
static cl::opt<int> CmdMaxComps("souper-synthesis-comp-num",
    cl::Hidden,
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

}

namespace souper {

static const std::string INPUT_PREFIX = "in_";
static const std::string LOC_PREFIX = "loc_";
static const std::string LOC_SEP = "_";
static const std::string COMP_INPUT_PREFIX = "compin_";
static const std::string CONST_PREFIX = "const_";

InstSynthesis::InstSynthesis()
      : MaxCompNum(CmdMaxComps >= 0 ? CmdMaxComps : -1) {
}

std::error_code InstSynthesis::synthesize(SMTLIBSolver *SMTSolver,
                                          const BlockPCs &BPCs,
                                          const std::vector<InstMapping> &PCs,
                                          Inst *LHS, Inst *&RHS, InstContext &IC,
                                          unsigned Timeout) {
  // Default return values
  std::error_code EC;
  RHS = 0;

  // LHS cost
  int LHSCost = cost(LHS);

  // Set component library
  setCompLibrary();

  // Prepare inputs
  initInputVars(LHS, IC);
  // Prepare the output
  initOutput(LHS, IC);
  // Prepare components
  initComponents(IC);
  // Init locations L
  initLocations();

  if (DebugSynthesis)
    printInitInfo();

  setInvalidWirings();

  // Init a new set of path conditions.
  std::vector<InstMapping> NewPCs;
  addConstraints(NewPCs, IC);

  // Create the main wiring query (aka connectivity contraint)
  Inst *WiringQuery = getConnectivityConstraint(IC);

  // Initial concrete input set S.
  // With every new input set that proves a synthesised program is invalid,
  // we'll have to copy WiringQuery and replace its inputs with the new
  // concrete values from S
  std::vector<std::map<Inst *, Inst *>> S;
  // A maping from a var's string to the actual instruction.
  // This mapping is required during model parsing
  std::map<std::string, Inst *> InputNameMap;
  std::map<Inst *, Inst *> InitialInputs;
  // Create initial inputs by asking a solver for an arbitrary solution
  // that satisfies BPCs/PCs
  std::vector<Inst *> ModelInsts;
  std::vector<llvm::APInt> ModelVals;
  InstMapping Mapping(LHS, IC.createVar(LHS->Width, "foo"));
  // Negate the query to get a SAT model
  std::string QueryStr = BuildQuery(BPCs, PCs, Mapping,
                                    &ModelInsts, /*Negate=*/true);
  bool IsSat;
  EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                &ModelVals, Timeout);
  if (EC || !IsSat)
    return EC;

  for (unsigned J = 0; J != ModelInsts.size(); ++J) {
    auto Name = ModelInsts[J]->Name;
    if (Name.find(INPUT_PREFIX) != std::string::npos) {
      auto Input = ModelInsts[J];
      InputNameMap[Name] = Input;
      InitialInputs[Input] = IC.getConst(ModelVals[J]);
    }
  }
  S.push_back(InitialInputs);

  // --------------------------------------------------------------------------
  // -------------- Counterexample driven synthesis loop ----------------------
  // --------------------------------------------------------------------------
  if (DebugSynthesis)
    llvm::outs() << "starting synthesis\n";
  unsigned Rounds = 0;
  while (true) {
    Inst *Query = IC.getConst(APInt(1, true));
    // Each set of concrete inputs is used in a separate copy of the
    // main WiringQuery. For correct separation of these copies, we must
    // copy all component input variables that encode data-flow in the
    // program too (starting with the second concrete input set, see below)
    for (auto const &InputMap : S) {
      if (DebugSynthesis) {
        for (auto const &Input : InputMap) {
          if (Input.first->Name.find(COMP_INPUT_PREFIX) != std::string::npos)
            continue;
          llvm::outs() << "setting input " << Input.first->Name
                       << " to " << Input.second->Val << "\n";
        }
        llvm::outs() << "----\n";
      }
      Inst *Copy = getInstCopy(WiringQuery, IC, InputMap);
      Query = IC.getInst(Inst::And, 1, {Query, Copy});
    }
    // Solve the synthesis constraint.
    // Each solution corresponds to a syntactically distinct and well-formed
    // straight-line program obtained by composition of given components
    ModelInsts.clear();
    ModelVals.clear();
    InstMapping Mapping(Query, IC.getConst(APInt(1, true)));
    // Negate the query to get a SAT model.
    // Don't use original BPCs/PCs, they are useless
    QueryStr = BuildQuery({}, NewPCs, Mapping, &ModelInsts, /*Negate=*/true);
    EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                  &ModelVals, Timeout);
    // Fail on error or when no valid wiring exists
    if (EC || !IsSat)
      return EC;

    if (DebugSynthesis)
      llvm::outs() << "round: " << Rounds << "\n";
    Rounds++;

    std::vector<std::pair<LocInst, LocInst>> Wiring;
    Inst *Cand = createInstFromModel(std::make_pair(ModelInsts, ModelVals),
                                     Wiring, IC);
    if (!Cand) {
      llvm::errs() << "synthesis bug: creating inst from a model failed\n";
      return EC;
    }

    // Is it worth it to check this candidate at all?
    if ((LHSCost - cost(Cand) < 1) && !IgnoreCost) {
      if (DebugSynthesis)
        llvm::outs() << "Cand is too expensive " << cost(Cand)
                     << " >= " << LHSCost << "\n";
      Inst *Ante = IC.getConst(APInt(1, true));
      for (auto const &Pair : Wiring) {
        auto const &L_x = Pair.first;
        auto const &L_y = Pair.second;
        Inst *Ne = IC.getInst(Inst::Ne, 1, {L_x.second, L_y.second});
        Ante = IC.getInst(Inst::And, 1, {Ante, Ne});
      }
      NewPCs.emplace_back(Ante, IC.getConst(APInt(1, true)));
      continue;
    }

    if (DebugSynthesis) {
      llvm::outs() << "candidate:\n";
      ReplacementContext Context;
      PrintReplacementRHS(llvm::outs(), Cand, Context);
    }

    // Does the candidate work for all inputs?
    // Use original BPCs/PCs
    ModelInsts.clear();
    ModelVals.clear();
    InstMapping CandMapping(LHS, Cand);
    QueryStr = BuildQuery(BPCs, PCs, CandMapping, &ModelInsts, /*Negate=*/false);
    EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                  &ModelVals, Timeout);
    if (EC)
      return EC;

    // Success
    if (!IsSat) {
      if (DebugSynthesis)
        llvm::outs() << "synthesis succeeded\n";
      RHS = Cand;
      return EC;
    }

    // Constants are not constrained by the inputs, thus, we must forbid the
    // invalid locations explicitly. Similarly, if an input is wired to the output
    // and is identified as invalid, we must skip it's location in the future too.
    // However, some constants result from junk-removal, don't forbid these
    if ((Cand->K == Inst::Const && LocInstMap.count(Cand->Name)) ||
        Cand->K == Inst::Var) {
      assert(LocInstMap.count(Cand->Name) && "unknown var candidate location");
      Inst *Ne = IC.getInst(Inst::Ne, 1, {LocInstMap[Cand->Name].second, O.second});
      NewPCs.emplace_back(Ne, IC.getConst(APInt(1, true)));
    }

    if (DebugSynthesis)
      llvm::outs() << "didn't work for all inputs, counterexample(s):\n";
    // Parse input counterexamples from the model
    std::map<Inst *, Inst *> Replacements;
    for (unsigned J = 0; J != ModelInsts.size(); ++J) {
      auto Name = ModelInsts[J]->Name;
      if (InputNameMap.count(Name)) {
        auto In = InputNameMap[Name];
        auto Val = ModelVals[J];
        Replacements[In] = IC.getConst(Val);
        if (DebugSynthesis)
          llvm::outs() << Name << " = " << Val << "\n";
      }
    }
    // Copy component input variables for query separation
    for (auto const &E : LocInstMap) {
      if (E.first.find(COMP_INPUT_PREFIX) != std::string::npos) {
        auto In = E.second.second;
        std::string Name = E.first + LOC_SEP + std::to_string(Rounds);
        Replacements[In] = IC.createVar(In->Width, Name);
      }
    }
    // Add replacements to S
    S.push_back(Replacements);
  }
  assert(0 && "unreachable");

  return EC;
}

void InstSynthesis::setCompLibrary() {
  if (!MaxCompNum)
    return;
  if (CmdUserCompKinds.size()) {
    std::vector<Inst::Kind> Kinds;
    // Parse user-provided component kind strings
    for (auto KindStr : splitString(CmdUserCompKinds.c_str())) {
      Inst::Kind K = Inst::getKind(KindStr);
      if (KindStr == Inst::getKindName(Inst::Const)) // Special case
        Kinds.push_back(Inst::Const);
      else if (K == Inst::Kind(~0))
        report_fatal_error("unknown instruction: " + KindStr + "\n");
      else if (UnsupportedCompKinds.count(K))
        report_fatal_error("unsupported instruction: " + KindStr + "\n");
      else
        Kinds.push_back(K);
    }
    for (auto const &Comp : CompLibrary)
      for (auto const &Kind : Kinds)
        if (Comp.Kind == Kind)
          Comps.push_back(Comp);
  } else {
    llvm::outs() << "WARNING: using all " << CompLibrary.size()
                 << " components, synthesis will probably take long time"
                 << " or run out of memory\n";
    Comps = CompLibrary;
  }
  // Adjust the maximum number of components to use
  if (MaxCompNum > Comps.size())
    MaxCompNum = Comps.size();
}

void InstSynthesis::getInputVars(Inst *I, std::vector<Inst *> &InputVars) {
  if (I->K == Inst::Var)
    InputVars.push_back(I);
  for (auto I : I->orderedOps())
    getInputVars(I, InputVars);
}

void InstSynthesis::initInputVars(Inst *LHS, InstContext &IC) {
  std::vector<Inst *> Tmp;
  getInputVars(LHS, Tmp);
  // Remove duplicates
  std::set<Inst *> TmpSet;
  std::vector<Inst *> Inputs;
  for (auto I : Tmp)
    if (TmpSet.insert(I).second)
      Inputs.push_back(I);
  for (unsigned J = 0; J < Inputs.size(); ++J) {
    // Note that location variable 0_0 is not used
    LocVar In = std::make_pair(0, J+1);
    std::string LocVarStr = getLocVarStr(In, LOC_PREFIX);
    Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Add input location to I
    I.emplace_back(In, Loc);
    // Update input name
    LocVarStr = getLocVarStr(In, INPUT_PREFIX);
    Inputs[J]->Name = LocVarStr;
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Update CompInstMap map with concrete Inst
    CompInstMap[In] = Inputs[J];
    // Set the DefaultInstWidth of component instances to the max width
    // seen in input variables
    if (Inputs[J]->Width > DefaultInstWidth)
      DefaultInstWidth = Inputs[J]->Width;
  }
  // No inputs, use output width
  if (!DefaultInstWidth)
    DefaultInstWidth = LHS->Width;
  N = I.size();
  M = Comps.size() + N;
}

void InstSynthesis::initComponents(InstContext &IC) {
  for (unsigned J = 0; J < Comps.size(); ++J) {
    auto &Comp = Comps[J];
    std::string LocVarStr;
    // First, init component inputs
    std::vector<Inst *> CompOps;
    for (unsigned K = 0; K < Comp.OpNum; ++K) {
      LocVar In = std::make_pair(J+1, K+1);
      LocVarStr = getLocVarStr(In, LOC_PREFIX);
      Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
      LocInstMap[LocVarStr] = std::make_pair(In, Loc);
      // Add component input location to P
      P.emplace_back(In, Loc);
      // Create concrete component input encoded as a fresh variable
      LocVarStr = getLocVarStr(In, COMP_INPUT_PREFIX);
      // Set op width for some special instructions.
      // Inst::Select's first op always has width 1
      if (Comp.Kind == Inst::Select && K == 0)
        Loc = IC.createVar(1, LocVarStr);
      // ZExt/SExt: extension from i1 only
      else if (Comp.Kind == Inst::ZExt || Comp.Kind == Inst::SExt)
        Loc = IC.createVar(1, LocVarStr);
      else
        Loc = IC.createVar(DefaultInstWidth, LocVarStr);
      LocInstMap[LocVarStr] = std::make_pair(In, Loc);
      // Update CompInstMap map with concrete Inst
      CompInstMap[In] = Loc;
      CompOps.push_back(Loc);
    }

    // Second, init component output
    LocVar Out = std::make_pair(J+1, 0);
    LocVarStr = getLocVarStr(Out, LOC_PREFIX);
    Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(Out, Loc);
    // Add component output to R.
    R.emplace_back(Out, Loc);

    // Third, instantiate the component (aka Inst)
    if (!Comp.Width)
      Comp.Width = DefaultInstWidth;
    if (Comp.Kind == Inst::Const) {
      LocVarStr = getLocVarStr(Out, CONST_PREFIX);
      // Special case: create one Const component with width
      // that matches the output width
      if (Comp.Width == ~0)
        Comp.Width = CompInstMap[O.first]->Width;
      Loc = IC.createVar(Comp.Width, LocVarStr);
    } else {
      Loc = IC.getInst(Comp.Kind, Comp.Width, CompOps);
    }
    // Update CompInstMap map with concrete Inst
    CompInstMap[Out] = Loc;
  }
}

void InstSynthesis::initOutput(Inst *LHS, InstContext &IC) {
  LocVar Out = std::make_pair(Comps.size()+1, 0);
  std::string LocVarStr = getLocVarStr(Out, LOC_PREFIX);
  Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
  // Set output location O
  O = std::make_pair(Out, Loc);
  LocInstMap[LocVarStr] = O;
  // Update CompInstMap map with concrete Inst
  CompInstMap[Out] = LHS;
}

void InstSynthesis::initLocations() {
  // We must add I and {O} to L too (not mentioned in the paper)
  L.insert(L.end(), I.begin(), I.end());
  L.insert(L.end(), P.begin(), P.end());
  L.insert(L.end(), R.begin(), R.end());
  L.push_back(O);
}

void InstSynthesis::printInitInfo() {
  llvm::outs() << "number of inputs (N): " << N << ", M = " << M << "\n";
  if (MaxCompNum >= 0)
    llvm::outs() << "number of components to use: " << MaxCompNum << "\n";
  else
    llvm::outs() << "number of components to use: " << Comps.size() << "\n";
  llvm::outs() << "default instruction width: " << DefaultInstWidth << "\n";
  llvm::outs() << "component library: ";
  for (auto const &Comp : Comps)
    llvm::outs() << Inst::getKindName(Comp.Kind)
                 << " (" << Comp.Width << ", " << Comp.OpNum << "); ";
  llvm::outs() << "\n";
  llvm::outs() << "instantiated components (unordered): ";
  for (auto const &E : CompInstMap) {
    if (E.first.second != 0 || E.first.first == Comps.size()+1)
      continue;
    llvm::outs() << Inst::getKindName(E.second->K)
                 << " (" << E.second->Width << ", { ";
    for (auto const &Op : E.second->orderedOps())
      llvm::outs() << Op->Width << " ";
    llvm::outs() << "}); ";
  }
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
  llvm::outs() << "L: ";
  for (auto const &In : L)
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
      if (Width == CompInstMap[L_x.first]->Width)
        continue;
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

Inst *InstSynthesis::getConsistencyConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis)
    llvm::outs() << "consistency constraints:\n";
  // Don't wire the outputs of two components
  for (unsigned J = 0; J < R.size(); ++J) {
    auto const &L_x = R[J];
    for (unsigned K = J+1; K < R.size(); ++K) {
      auto const &L_y = R[K];
      InvalidWirings.insert(std::make_pair(L_x.first, L_y.first));
      Inst *Ne = IC.getInst(Inst::Ne, 1, {L_x.second, L_y.second});
      Ret = IC.getInst(Inst::And, 1, {Ret, Ne});
      if (DebugSynthesis)
        llvm::outs() << getLocVarStr(L_x.first) << " != "
                     << getLocVarStr(L_y.first) << "\n";
    }
  }

  return Ret;
}


void InstSynthesis::addConstraints(std::vector<InstMapping> &PCs,
                                   InstContext &IC) {
  Inst *C = getConsistencyConstraint(IC);
  PCs.emplace_back(C, IC.getConst(APInt(1, true)));
  C = getAcyclicityConstraint(IC);
  PCs.emplace_back(C, IC.getConst(APInt(1, true)));
  C = getLocVarConstraint(IC);
  PCs.emplace_back(C, IC.getConst(APInt(1, true)));
  C = getInputDefinednessConstraint(IC);
  PCs.emplace_back(C, IC.getConst(APInt(1, true)));
  C = getOutputDefinednessConstraint(IC);
  PCs.emplace_back(C, IC.getConst(APInt(1, true)));
}

Inst *InstSynthesis::getAcyclicityConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis)
    llvm::outs() << "acyclicity constraints:\n";
  // Component inputs
  for (auto const &L_x : P) {
    // Grab a component's output LocInst
    std::string LocVarStr = LOC_PREFIX + std::to_string(L_x.first.first)
                                       + LOC_SEP + "0";
    assert(LocInstMap.count(LocVarStr) && "unknown location variable");
    auto const &L_y = LocInstMap[LocVarStr];
    if (DebugSynthesis)
      llvm::outs() << getLocVarStr(L_x.first) << " < "
                   << L_x.first.first << LOC_SEP << "0" << "\n";
    Inst *Ult = IC.getInst(Inst::Ult, 1, {L_x.second, L_y.second});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ult});
  }

  return Ret;
}

Inst *InstSynthesis::getLocVarConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis)
    llvm::outs() << "location variable constraints:\n";
  std::vector<LocInst> Tmp(P.begin(), P.end());
  Tmp.insert(Tmp.end(), I.begin(), I.end());
  // All inputs
  for (auto const &L_x : Tmp) {
    if (DebugSynthesis)
      llvm::outs() << "0 <= " << getLocVarStr(L_x.first)
                   << " < " << M << "\n";
    Inst *Ult =
      IC.getInst(Inst::Ult, 1,
                 {L_x.second, IC.getConst(APInt(L_x.second->Width, 0))});
    Inst *Ne = IC.getInst(Inst::Eq, 1, {Ult, IC.getConst(APInt(1, false))});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ne});
    Ult = IC.getInst(Inst::Ult, 1,
                     {L_x.second, IC.getConst(APInt(L_x.second->Width, M))});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ult});
  }

  // All outputs
  Tmp.clear();
  Tmp.insert(Tmp.end(), R.begin(), R.end());
  Tmp.push_back(O);
  for (auto const &L_x : Tmp) {
    Inst *Ult = 0;
    if (L_x == O) {
      Ult = IC.getInst(Inst::Ult, 1,
                       {L_x.second, IC.getConst(APInt(L_x.second->Width, 0))});
      if (DebugSynthesis)
        llvm::outs() << "0 <= " << getLocVarStr(L_x.first);
    } else {
      Ult = IC.getInst(Inst::Ult, 1,
                       {L_x.second, IC.getConst(APInt(L_x.second->Width, N))});
      if (DebugSynthesis)
        llvm::outs() << N << " <= " << getLocVarStr(L_x.first);
    }
    Inst *Ne = IC.getInst(Inst::Eq, 1, {Ult, IC.getConst(APInt(1, false))});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ne});
    if (MaxCompNum >= 0 && L_x == O) {
      Ult = IC.getInst(Inst::Ult, 1, {L_x.second,
                                      IC.getConst(APInt(L_x.second->Width,
                                                  N+MaxCompNum))});
      if (DebugSynthesis)
        llvm::outs() << " < " << N+MaxCompNum << "\n";
    } else {
      Ult = IC.getInst(Inst::Ult, 1, {L_x.second,
                                      IC.getConst(APInt(L_x.second->Width,
                                                  M))});
      if (DebugSynthesis)
        llvm::outs() << " < " << M << "\n";
    }
    Ret = IC.getInst(Inst::And, 1, {Ret, Ult});
  }

  return Ret;
}

Inst *InstSynthesis::getConnectivityConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis)
    llvm::outs() << "possible wirings:\n";
  for (unsigned J = 0; J < L.size(); ++J) {
    for (unsigned K = J+1; K < L.size(); ++K) {
      auto const &L_x = L[J];
      auto const &L_y = L[K];
      // Skip invalid wirings
      if (isWiringInvalid(L_x.first, L_y.first))
        continue;
      auto const &X = CompInstMap[L_x.first];
      auto const &Y = CompInstMap[L_y.first];
      if (DebugSynthesis)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << "\n";
      // (l_x = l_y) => x = y
      Inst *Eq = IC.getInst(Inst::Eq, 1, {L_x.second, L_y.second});
      Eq = IC.getInst(Inst::Eq, 1, {Eq, IC.getConst(APInt(1, false))});
      Inst *Eq2 = IC.getInst(Inst::Eq, 1, {X, Y});
      Inst *Implies = IC.getInst(Inst::Or, 1, {Eq, Eq2});
      Ret = IC.getInst(Inst::And, 1, {Ret, Implies});
    }
  }

  return Ret;
}

Inst *InstSynthesis::getInputDefinednessConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis)
    llvm::outs() << "input-definedness constraints:\n";
  for (auto const &L_x : P) {
    unsigned Width = CompInstMap[L_x.first]->Width;
    Inst *Ante = IC.getConst(APInt(1, false));
    // Inputs
    for (auto const &In : I) {
      if (isWiringInvalid(L_x.first, In.first))
        continue;
      Inst *Eq = IC.getInst(Inst::Eq, 1, {L_x.second, In.second});
      Ante = IC.getInst(Inst::Or, 1, {Ante, Eq});
      if (DebugSynthesis)
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
      Inst *Eq = IC.getInst(Inst::Eq, 1, {L_x.second, L_y.second});
      Ante = IC.getInst(Inst::Or, 1, {Ante, Eq});
      if (DebugSynthesis)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << " || ";
    }
    if (DebugSynthesis)
      llvm::outs() << "false\n";
    // Add to result
    Ret = IC.getInst(Inst::And, 1, {Ret, Ante});
  }

  return Ret;
}

Inst *InstSynthesis::getOutputDefinednessConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, false));

  if (DebugSynthesis)
    llvm::outs() << "output-definedness constraints:\n";
  unsigned Width = CompInstMap[O.first]->Width;
  // Inputs
  for (auto const &In : I) {
    if (isWiringInvalid(In.first, O.first))
      continue;
    Inst *Eq = IC.getInst(Inst::Eq, 1, {O.second, In.second});
    Ret = IC.getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugSynthesis)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(In.first) << " || ";
  }
  // Component outputs
  for (auto const &L_y : R) {
    if (isWiringInvalid(L_y.first, O.first))
      continue;
    Inst *Eq = IC.getInst(Inst::Eq, 1, {O.second, L_y.second});
    Ret = IC.getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugSynthesis)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(L_y.first) << " || ";
  }
  if (DebugSynthesis)
    llvm::outs() << "false\n";

  return Ret;
}

Inst *InstSynthesis::getInstCopy(Inst *I, InstContext &IC,
                                 const std::map<Inst *, Inst *> &Replacements) {
  std::vector<Inst *> Ops;
  for (auto const &Op : I->Ops)
    Ops.push_back(getInstCopy(Op, IC, Replacements));

  if (I->K == Inst::Var) {
    if (!Replacements.count(I))
      return I;
    // Replace
    return Replacements.at(I);
  } else if (I->K == Inst::Phi) {
    return IC.getPhi(I->B, Ops);
  } else if (I->K == Inst::Const || I->K == Inst::UntypedConst) {
    return I;
  } else {
    return IC.getInst(I->K, I->Width, Ops);
  }
}

Inst *InstSynthesis::createInstFromModel(const SolverSolution &Solution,
                                         std::vector<std::pair<LocInst, LocInst>> &Wiring,
                                         InstContext &IC) {
  LineLocVarMap ProgramWiring;
  std::map<LocVar, llvm::APInt> ConstValMap;

  LocVar OutLoc = parseWiringModel(Solution, ProgramWiring, ConstValMap);
  auto Left = getLocVarStr(O.first, LOC_PREFIX);
  auto Right = getLocVarStr(OutLoc, LOC_PREFIX);
  Wiring.emplace_back(LocInstMap[Left], LocInstMap[Right]);

  if (DebugSynthesis) {
    llvm::outs() << "found valid wiring, output "
                 << getLocVarStr(OutLoc) << ".\n";
    llvm::outs() << "line\tlocations\n";
    for (auto const &E : ProgramWiring) {
      llvm::outs() << E.first << "\t";
      for (auto const &Loc : E.second)
        llvm::outs() << getLocVarStr(Loc) << " ";
      llvm::outs() << "\n";
    }
  }

  if (!CompInstMap.count(OutLoc)) {
    llvm::errs() << "synthesis bug: output not wired\n";
    return 0;
  }

  auto OpLocs = getOpLocs(OutLoc);
  if (DebugSynthesis) {
    llvm::outs() << "creating program from wiring\n";
    llvm::outs() << "- starting with OutLoc " << getLocVarStr(OutLoc)
                 << ", OpLocs { ";
    for (auto const &OpLoc : OpLocs)
      llvm::outs() << getLocVarStr(OpLoc) << " ";
    llvm::outs() << "}\n";
  }
  Inst *Res = createInstFromWiring(OutLoc, OpLocs, ProgramWiring,
                                   ConstValMap, Wiring, IC);
  assert(Res && "creating instruction from wiring failed");

  return Res;
}

Inst *InstSynthesis::createInstFromWiring(
      const LocVar &OutLoc,
      const std::vector<LocVar> &OpLocs,
      const LineLocVarMap &ProgramWiring,
      const std::map<LocVar, llvm::APInt> &ConstValMap,
      std::vector<std::pair<LocInst, LocInst>> &Wiring,
      InstContext &IC) {
  std::vector<Inst *> Ops;

  // Create operand instructions recursively
  for (auto const &OpLoc : OpLocs) {
    LocVar Match = getWiringLocVar(OpLoc, ProgramWiring);
    assert(CompInstMap.count(Match) && "unknown matching location variable");
    if (!CompInstMap.count(Match)) {
      llvm::errs() << "synthesis bug: component input "
                   << getLocVarStr(OpLoc) << " not wired\n";
      return 0;
    }
    // Store wiring locations
    auto Left = getLocVarStr(OpLoc, LOC_PREFIX);
    auto Right = getLocVarStr(Match, LOC_PREFIX);
    Wiring.emplace_back(LocInstMap[Left], LocInstMap[Right]);
    // Get operand locations of the wiring location
    auto Res = getOpLocs(Match);
    if (DebugSynthesis) {
      llvm::outs() << "- continue with OutLoc " << getLocVarStr(Match)
                   << ", OpLocs {";
      for (auto const &R : Res)
        llvm::outs() << getLocVarStr(R) << " ";
      llvm::outs() << "}\n";
    }
    // Recurse
    Inst *Op = createInstFromWiring(Match, Res, ProgramWiring,
                                    ConstValMap, Wiring, IC);
    // Store result
    Ops.push_back(Op);
  }

  // Is it an input?
  if (OutLoc.first == 0) {
    if (DebugSynthesis)
      llvm::outs() << "- creating input inst " << getLocVarStr(OutLoc) << "\n";
    return CompInstMap[OutLoc];
  }
  // It it a constant?
  if (ConstValMap.count(OutLoc)) {
    if (DebugSynthesis)
      llvm::outs() << "- creating constant inst " << getLocVarStr(OutLoc)
                   << " with value " << ConstValMap.at(OutLoc) << "\n";
    Inst *Const = IC.getConst(ConstValMap.at(OutLoc));
    // Find const comp's output location
    LocInst Loc;
    for (const auto &L_x : R) {
      if (L_x.first == OutLoc) {
        Loc = L_x;
        break;
      }
    }
    assert(Loc.first.first != 0 || Loc.first.second != 0 &&
           "unknown const comp's output location");
    // Update const inst's name
    std::string LocVarStr = getLocVarStr(OutLoc, CONST_PREFIX);
    Const->Name = LocVarStr;
    LocInstMap[LocVarStr] = Loc;
    return Const;
  }
  // Grab the target component
  Component Comp = Comps[OutLoc.first-1];
  assert(OutLoc.first >= 1 && "invalid component location variable");
  assert((Ops.size() == Comp.OpNum) && "op num mismatch");
  if (DebugSynthesis)
    llvm::outs() << "- creating inst " << Inst::getKindName(Comp.Kind)
                 << ", width " << Comp.Width << "\n";

  return createJunkFreeInst(Comp.Kind, Comp.Width, Ops, IC);
}

LocVar InstSynthesis::parseWiringModel(const SolverSolution &Solution,
                                       LineLocVarMap &ProgramWiring,
                                       std::map<LocVar, llvm::APInt> &ConstValMap) {
  unsigned Counter = 0;
  LocVar OutLocVar;
  bool OutLocSet = false;
  unsigned OutWidth = CompInstMap[O.first]->Width;

  auto ModelInsts = Solution.first;
  auto ModelVals = Solution.second;
  assert(ModelVals.size() && "there must models to parse");
  for (unsigned J = 0; J != ModelInsts.size(); ++J) {
    auto Name = ModelInsts[J]->Name;
    // Parse location variable models
    if (Name.find(LOC_PREFIX) != std::string::npos) {
      LocVar Loc = getLocVarFromStr(Name.substr(LOC_PREFIX.size()));
      unsigned Line = (unsigned)ModelVals[J].getZExtValue();
      if (ProgramWiring.count(Line)) {
        // Look for the output wiring. It can be a component's output or any
        // of the inputs. Note that due to scalability reasons, we haven't
        // encoded width mismatches and other invalid wirings as constraints,
        // thus, we need to perform sanity checks on candidates
        if (!OutLocSet) {
          // Is it output? If yes, there should be only one component output
          // and/or any input on that line
          auto const &VarMap = ProgramWiring[Line];
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
        ProgramWiring[Line].insert(Loc);
      } else {
        ProgramWiring[Line] = {Loc};
      }
      Counter++;
    // Parse constant models
    } else if (Name.find(CONST_PREFIX) != std::string::npos) {
      LocVar Loc = getLocVarFromStr(Name.substr(CONST_PREFIX.size()));
      ConstValMap[Loc] = ModelVals[J];
    }
  }
  assert(OutLocSet && "no matching location for the output");
  assert(ProgramWiring.size() <= M && "the output location must be <= M");
  assert(Counter == L.size() && "invalid number of locations in the model");

  return OutLocVar;
}

LocVar InstSynthesis::getWiringLocVar(const LocVar &OpLoc,
                                      const LineLocVarMap &ProgramWiring) {
  LocVar Match;
  bool FoundMatch = false;

  if (DebugSynthesis)
    llvm::outs() << "- looking for OpLoc wiring "
                 << getLocVarStr(OpLoc) << "\n";
  for (auto const &E : ProgramWiring) {
    if (E.second.count(OpLoc)) {
      if (DebugSynthesis)
        llvm::outs() << "- found wiring input on line " << E.first << ", taking ";
      for (auto const &In : E.second) {
        // Take either input or component output
        if (In.first == 0 || In.second == 0) {
          Match = In;
          if (DebugSynthesis)
            llvm::outs() << getLocVarStr(Match);
          FoundMatch = true;
          break;
        }
      }
      if (DebugSynthesis)
        llvm::outs() << "\n";
    }
    if (FoundMatch)
      break;
  }

  return Match;
}

Inst *InstSynthesis::createJunkFreeInst(Inst::Kind Kind, unsigned Width,
                                        std::vector<Inst *> &Ops,
                                        InstContext &IC) {
  switch (Kind) {
  case Inst::Add:
  case Inst::AddNSW:
  case Inst::AddNUW:
  case Inst::AddNW: {
    if (Ops[0] == IC.getConst(APInt(Width, 0)))
      return Ops[1];
    else if (Ops[1] == IC.getConst(APInt(Width, 0)))
      return Ops[0];
    break;
  }

  case Inst::Sub:
  case Inst::SubNSW:
  case Inst::SubNUW:
  case Inst::SubNW: {
    if (Ops[1] == IC.getConst(APInt(Width, 0)))
      return Ops[0];
    break;
  }

  case Inst::Mul:
  case Inst::MulNSW:
  case Inst::MulNUW:
  case Inst::MulNW: {
    if (Ops[0] == IC.getConst(APInt(Width, 1)))
      return Ops[1];
    else if (Ops[1] == IC.getConst(APInt(Width, 1)))
      return Ops[0];
    break;
  }

  case Inst::UDiv:
  case Inst::SDiv:
  case Inst::UDivExact:
  case Inst::SDivExact: {
    if (Ops[1] == IC.getConst(APInt(Width, 1)))
      return Ops[0];
    break;
  }

  case Inst::And:
  case Inst::Or: {
    if (Ops[0] == Ops[1])
      return Ops[0];
    break;
  }

  case Inst::Xor: {
    if (Ops[0] == Ops[1])
      return IC.getConst(APInt(Width, 0));
    break;
  }

  case Inst::Shl:
  case Inst::ShlNSW:
  case Inst::ShlNUW:
  case Inst::ShlNW:
  case Inst::LShr:
  case Inst::LShrExact:
  case Inst::AShr:
  case Inst::AShrExact: {
    if (Ops[1] == IC.getConst(APInt(Width, 0)))
      return Ops[0];
    break;
  }

  case Inst::Select: {
    if (Ops[1] == Ops[2])
      return Ops[1];
    break;
  }

  case Inst::ZExt:
  case Inst::SExt:
  case Inst::Trunc: {
    if (Width == Ops[0]->Width)
      return Ops[0];
    break;
  }

  case Inst::Eq: {
    if (Ops[0] == Ops[1])
      return IC.getConst(APInt(1, true));
    break;
  }

  case Inst::Ne: {
    if (Ops[0] == Ops[1])
      return IC.getConst(APInt(1, false));
    break;
  }

  case Inst::Ult:
  case Inst::Slt: {
    if (Ops[0] == Ops[1])
      return IC.getConst(APInt(1, false));
    break;
  }

  case Inst::CtPop:
  case Inst::BSwap: {
    if (Ops[0] == IC.getConst(APInt(Width, 0)))
      return IC.getConst(APInt(Width, 0));
    break;
  }

  case Inst::Cttz:
  case Inst::Ctlz: {
    if (Ops[0] == IC.getConst(APInt(Width, 0)))
      return IC.getConst(APInt(Width, Width));
    break;
  }

  default:
    break;
  }

  return IC.getInst(Kind, Width, Ops);
}

std::string InstSynthesis::getLocVarStr(const LocVar &Loc,
                                        const std::string Prefix) {
  std::string Post = "";
  // Print component's name in debug mode
  if (DebugSynthesis && Prefix == "") {
    std::string Str;
    unsigned Width;
    if (Loc == O.first) {
      Str = "output";
      Width = CompInstMap[Loc]->Width;
    } else if (Loc.first == 0) {
      Str = "input";
      Width = CompInstMap[Loc]->Width;
    } else {
      auto const &Comp = Comps[Loc.first-1];
      Str = std::string(Inst::getKindName(Comp.Kind));
      Width = Comp.Width;
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
  for (unsigned J = 0; J < Comp.OpNum; ++J) {
    LocVar Tmp = std::make_pair(Loc.first, J+1);
    assert(CompInstMap.count(Tmp) && "unknown comp input's location variable");
    Res.push_back(Tmp);
  }

  return Res;
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

}
