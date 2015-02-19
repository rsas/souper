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

static cl::opt<bool> DebugSynthesis("souper-synthesis-debug",
    cl::desc("Synthesis debug (default=false)"),
    cl::init(false));
static cl::opt<unsigned> DebugLevel("souper-synthesis-debug-level",
    cl::Hidden,
    cl::desc("Synthesis debug level (default=1). "
    "The larger the number is, the more fine-grained debug "
    "information will be printed."),
    cl::init(1));
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

}

namespace souper {

static const std::string INPUT_PREFIX = "in_";
static const std::string LOC_PREFIX = "loc_";
static const std::string LOC_SEP = "_";
static const std::string COMP_INPUT_PREFIX = "compin_";
static const std::string CONST_PREFIX = "const_";

std::error_code InstSynthesis::synthesize(SMTLIBSolver *SMTSolver,
                                          const BlockPCs &BPCs,
                                          const std::vector<InstMapping> &PCs,
                                          Inst *LHS, Inst *&RHS, InstContext &IC,
                                          unsigned Timeout) {
  std::error_code EC;
  RHS = 0;

  // The order is important
  setCompLibrary();
  initInputVars(LHS, IC);
  setDefaultWidth(LHS);
  addZSTComps(LHS);
  initOutput(LHS, IC);
  initComponents(IC);
  initConstComponents(IC);
  initLocations();

  N = I.size();
  M = Comps.size() + N;

  int LHSCost = cost(LHS);

  if (DebugSynthesis && DebugLevel > 1)
    printInitInfo();

  setInvalidWirings();

  // Init a new set of path conditions
  std::vector<InstMapping> WiringPCs;
  addConstraints(WiringPCs, IC);

  // Create the main wiring query (aka connectivity contraint)
  Inst *WiringQuery = getConnectivityConstraint(IC);

  // Initial concrete input set S.
  // With every new input set that proves a synthesised program is invalid,
  // we'll have to copy WiringQuery and replace its inputs with the new
  // concrete values from S
  std::vector<std::map<Inst *, Inst *>> S;

  // Not-working candidate programs that contain constants must be forbidden
  // explicitly because constants are not constrainted by the inputs. Still, it
  // can take many iterations to converge. Therefore, we limit the number
  // of attempts per such a candidate wiring using MaxWiringAttempts set to 10
  // (number seen in papers)
  std::map<ProgramWiring, unsigned> NotWorkingConstWirings;
  const unsigned MaxWiringAttempts = 10;

  // Ask the solver for four initial concrete inputs.
  // This number was derived experimentally giving a good overall speed-up
  // for both small and big synthesis queries
  unsigned InitialInputNum = 4;
  auto InputPCs = PCs;
  for (; InitialInputNum > 0; InitialInputNum--) {
    std::vector<Inst *> ModelInsts;
    std::vector<llvm::APInt> ModelVals;
    InstMapping Mapping(LHS, IC.createVar(LHS->Width, "output"));
    // Negate the query to get a SAT model
    std::string QueryStr = BuildQuery(BPCs, InputPCs, Mapping,
                                      &ModelInsts, /*Negate=*/true);
    bool IsSat;
    EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                  &ModelVals, Timeout);
    if (EC)
      return EC;

    if (!IsSat)
      break;

    std::map<Inst *, Inst *> ConcreteInputs;
    for (unsigned J = 0; J < ModelInsts.size(); ++J) {
      auto Name = ModelInsts[J]->Name;
      if (Name.find(INPUT_PREFIX) != std::string::npos) {
        auto Input = ModelInsts[J];
        ConcreteInputs[Input] = IC.getConst(ModelVals[J]);
        Inst *Ne = IC.getInst(Inst::Ne, 1, {Input, IC.getConst(ModelVals[J])});
        InputPCs.emplace_back(Ne, IC.getConst(APInt(1, true)));
      }
    }
    S.push_back(ConcreteInputs);
  }

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

  if (DebugSynthesis && DebugLevel > 0) {
    llvm::outs() << "starting synthesis for LHS:\n";
    ReplacementContext Context;
    PrintReplacementRHS(llvm::outs(), LHS, Context);
  }

  // Iterative synthesis loop with increasing number of components
  for (int J = 0; J <= MaxCompNum; ++J) {
    Inst *CompConstraint;
    if (DebugSynthesis && DebugLevel > 0)
      llvm::outs() << "synthesizing using " << J << " component(s)\n";
    // If synthesis using 0 components failed (aka nop synthesis),
    // don't subsequently wire the output to the input(s)
    if (J == 0)
      CompConstraint = getOutputLocVarConstraint(0, N, IC);
    else {
      CompConstraint = getOutputLocVarConstraint(N, N+J, IC);
    }
    // Init fresh loop PCs
    auto LoopPCs = WiringPCs;
    LoopPCs.emplace_back(CompConstraint, IC.getConst(APInt(1, true)));

    // --------------------------------------------------------------------------
    // -------------- Counterexample driven synthesis loop ----------------------
    // --------------------------------------------------------------------------
    unsigned Refinements = 0;
    while (true) {
      Inst *Query = IC.getConst(APInt(1, true));
      // Put each set of concrete inputs into a separate copy of the WiringQuery
      for (unsigned J = 0; J < S.size(); ++J) {
        auto InputMap = S[J];
        if (DebugSynthesis && DebugLevel > 1) {
          for (auto const &Input : InputMap) {
            if (Input.first->Name.find(COMP_INPUT_PREFIX) != std::string::npos)
              continue;
            llvm::outs() << "setting input " << Input.first->Name
                         << " to " << Input.second->Val << "\n";
          }
        }
        if (J > 0) {
          // Starting with the second concrete input set,
          // copy component input variables for query separation
          for (auto const &E : LocInstMap) {
            if (E.first.find(COMP_INPUT_PREFIX) != std::string::npos) {
              auto In = E.second.second;
              std::string Name = E.first + LOC_SEP + std::to_string(Refinements);
              InputMap[In] = IC.createVar(In->Width, Name);
            }
          }
        }
        Inst *Copy = getInstCopy(WiringQuery, IC, InputMap);
        Query = IC.getInst(Inst::And, 1, {Query, Copy});
      }
      // Solve the synthesis constraint.
      // Each solution corresponds to a syntactically distinct and well-formed
      // straight-line program obtained by composition of given components
      std::vector<Inst *> ModelInsts;
      std::vector<llvm::APInt> ModelVals;
      InstMapping Mapping(Query, IC.getConst(APInt(1, true)));
      // Negate the query to get a SAT model.
      // Don't use original BPCs/PCs, they are useless
      std::string QueryStr = BuildQuery({}, LoopPCs, Mapping,
                                        &ModelInsts, /*Negate=*/true);
      bool IsSat;
      if (DebugSynthesis && DebugLevel > 0)
        llvm::outs() << "solving synthesis constraint.. ";
      EC = SMTSolver->isSatisfiable(QueryStr, IsSat, ModelInsts.size(),
                                    &ModelVals, Timeout);
      if (EC)
        return EC;

      // No valid wiring exists for the target comp number
      if (!IsSat) {
        if (DebugSynthesis && DebugLevel > 0)
          llvm::outs() << "UNSAT\n";
        break;
      } else {
        if (DebugSynthesis && DebugLevel > 0)
          llvm::outs() << "SAT\n";
      }

      ProgramWiring CandWiring;
      std::map<LocVar, llvm::APInt> ConstValMap;
      Inst *Cand = createInstFromModel(std::make_pair(ModelInsts, ModelVals),
                                       CandWiring, ConstValMap, IC);
      if (!Cand)
        report_fatal_error("synthesis bug: creating inst from a model failed");

      if (DebugSynthesis && DebugLevel > 0) {
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
        if (DebugSynthesis && DebugLevel > 0)
          llvm::outs() << "synthesis succeeded using " << cost(Cand)
                       << " components (LHS cost: " << LHSCost << ")\n";
        RHS = Cand;
        return EC;
      }

      Refinements++;
      if (DebugSynthesis && DebugLevel > 0)
        llvm::outs() << "didn't work for all inputs "
                     << "(#cex: "<< S.size()+1 << ", "
                     << "refinement: " << Refinements << ")\n";
      // Parse input counterexamples from the model
      std::map<Inst *, Inst *> InputMap;
      for (unsigned J = 0; J < ModelInsts.size(); ++J) {
        auto Name = ModelInsts[J]->Name;
        if (Name.find(INPUT_PREFIX) != std::string::npos) {
          auto In = ModelInsts[J];
          auto Val = ModelVals[J];
          InputMap[In] = IC.getConst(Val);
          if (DebugSynthesis && DebugLevel > 1)
            llvm::outs() << "counterexample: " << Name << " = " << Val << "\n";
        }
      }
      // Counterexamples should be unique in each iteration
      bool CexExists = false;
      for (auto const &E : S)
        if (std::equal(E.begin(), E.end(), InputMap.begin())) {
          CexExists = true;
          break;
        }
      // Add counterexamples to S
      if (!CexExists)
        S.push_back(InputMap);

      if (!hasConst(Cand))
        continue;

      // Constants are not constrained by the inputs, thus, we must explicitly
      // constrain the not-working cand wiring incl. the constants and forbid
      // the wiring completely after MaxWiringAttempts is reached
      auto WI = NotWorkingConstWirings.find(CandWiring);
      if (WI == NotWorkingConstWirings.end()) {
        NotWorkingConstWirings[CandWiring] = 0;
        continue;
      }
      WI->second++;
      if (DebugSynthesis && DebugLevel > 1) {
        llvm::outs() << "cand with constants, constraining wiring\n";
        if (WI->second == MaxWiringAttempts)
          llvm::outs() << "cand reached MaxWiringAttempts "
                       << "(" << MaxWiringAttempts << "), forbidding\n";
      }
      Inst *Ante = IC.getConst(APInt(1, true));
      for (auto const &Pair : CandWiring) {
        auto const &L_x = Pair.first;
        auto const &L_y = Pair.second;
        if (DebugSynthesis && DebugLevel > 2)
          llvm::outs() << getLocVarStr(L_x.first) << " == "
                       << getLocVarStr(L_y.first) << "\n";
        // Constrain the wiring
        Inst *Eq = IC.getInst(Inst::Eq, 1, {L_x.second, L_y.second});
        Ante = IC.getInst(Inst::And, 1, {Ante, Eq});
        // If the cand is a constant, forbid the wiring immediately
        if (Cand->K == Inst::Const)
          continue;
        // Otherwise, constrain the wiring with constants as long as
        // MaxWiringAttempts is not reached. Afterwards, the wiring
        // will be banned (without constants)
        if (WI->second < MaxWiringAttempts) {
          auto CI = ConstValMap.find(L_y.first);
          if (CI == ConstValMap.end())
            continue;
          auto const &Cons = CompInstMap[L_y.first];
          if (DebugSynthesis && DebugLevel > 1)
            llvm::outs() << "with constant " << getLocVarStr(L_y.first)
                         << " == " << CI->second << "\n";
          Eq = IC.getInst(Inst::Eq, 1, {Cons, IC.getConst(CI->second)});
          Ante = IC.getInst(Inst::And, 1, {Ante, Eq});
        }
      }
      LoopPCs.emplace_back(Ante, IC.getConst(APInt(1, false)));
    }
  }

  return EC;
}

void InstSynthesis::setCompLibrary() {
  if (!CmdMaxCompNum)
    return;
  if (CmdUserCompKinds.size()) {
    std::vector<Inst::Kind> Kinds;
    // Parse user-provided component kind strings
    for (auto KindStr : splitString(CmdUserCompKinds.c_str())) {
      Inst::Kind K = Inst::getKind(KindStr);
      UserCompKinds.insert(K);
      if (KindStr == Inst::getKindName(Inst::Const)) { // Special case
        ConstComps.push_back(Component{Inst::Const, 0, {}});
      } else if (K == Inst::ZExt || K == Inst::SExt || K == Inst::Trunc)
        continue; // handled in addZSTComps
      else if (K == Inst::Kind(~0))
        report_fatal_error("unknown instruction: " + KindStr);
      else if (UnsupportedCompKinds.count(K))
        report_fatal_error("unsupported instruction: " + KindStr);
      else
        Kinds.push_back(K);
    }
    for (auto const &Comp : CompLibrary)
      for (auto const &Kind : Kinds)
        if (Comp.Kind == Kind)
          Comps.push_back(Comp);
  } else {
    Comps = CompLibrary;
    ConstComps.push_back(Component{Inst::Const, 0, {}});
    llvm::outs() << "WARNING: using all " << Comps.size()
                 << " components, synthesis will probably take long time"
                 << " or run out of memory\n";
  }
}

void InstSynthesis::initInputVars(Inst *LHS, InstContext &IC) {
  std::vector<Inst *> Tmp;
  getInputVars(LHS, Tmp);
  // Remove duplicates
  std::set<Inst *> TmpSet;
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
  }
}

void InstSynthesis::initConstComponents(InstContext &IC) {
  for (unsigned J = 0; J < ConstComps.size(); ++J) {
    auto &Comp = ConstComps[J];
    // Treat constant comps as ordinary inputs
    LocVar In = std::make_pair(0, Inputs.size()+J+1);
    std::string LocVarStr = getLocVarStr(In, LOC_PREFIX);
    Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Add constant component location to I
    I.emplace_back(In, Loc);
    // Update name
    LocVarStr = getLocVarStr(In, CONST_PREFIX);
    LocInstMap[LocVarStr] = std::make_pair(In, Loc);
    // Update CompInstMap map with concrete Inst
    Loc = IC.createVar(DefaultWidth, LocVarStr);
    CompInstMap[In] = Loc;
  }
}

void InstSynthesis::setDefaultWidth(Inst *LHS) {
  // Set the DefaultWidth of component instances to the max width seen in inputs
  for (auto In : Inputs)
    if (In->Width > DefaultWidth)
      DefaultWidth = In->Width;
  // No inputs, use output width
  if (!DefaultWidth)
    DefaultWidth = LHS->Width;
}

void InstSynthesis::addZSTComps(Inst *LHS) {
  bool TestMode = CmdUserCompKinds.size() ? true : false;

  // Extend all inputs to DefaultWidth
  for (auto In : Inputs) {
    if (In->Width < DefaultWidth) {
      if (TestMode) {
        if (UserCompKinds.count(Inst::ZExt))
          Comps.emplace_back(Component{Inst::ZExt, DefaultWidth, {In->Width}});
        if (UserCompKinds.count(Inst::SExt))
          Comps.emplace_back(Component{Inst::SExt, DefaultWidth, {In->Width}});
      } else {
        Comps.emplace_back(Component{Inst::ZExt, DefaultWidth, {In->Width}});
        Comps.emplace_back(Component{Inst::SExt, DefaultWidth, {In->Width}});
      }
    }
  }
  // It's common to extend from i1 (e.g. icmp output) to bigger iN
  if (DefaultWidth > 1) {
    if (TestMode) {
      if (UserCompKinds.count(Inst::ZExt)) {
        Comps.emplace_back(Component{Inst::ZExt, DefaultWidth, {1}});
        if (DefaultWidth != LHS->Width && LHS->Width > 1)
          Comps.emplace_back(Component{Inst::ZExt, LHS->Width, {1}});
      }
      if (UserCompKinds.count(Inst::SExt)) {
        Comps.emplace_back(Component{Inst::SExt, DefaultWidth, {1}});
        if (DefaultWidth != LHS->Width && LHS->Width > 1)
          Comps.emplace_back(Component{Inst::SExt, LHS->Width, {1}});
      }
    } else {
      Comps.emplace_back(Component{Inst::ZExt, DefaultWidth, {1}});
      Comps.emplace_back(Component{Inst::SExt, DefaultWidth, {1}});
      if (DefaultWidth != LHS->Width && LHS->Width > 1) {
        Comps.emplace_back(Component{Inst::ZExt, LHS->Width, {1}});
        Comps.emplace_back(Component{Inst::SExt, LHS->Width, {1}});
      }
    }
  }
  // Sometimes the result is extended to bigger output iN
  if (DefaultWidth < LHS->Width) {
    if (TestMode) {
      if (UserCompKinds.count(Inst::ZExt))
        Comps.emplace_back(Component{Inst::ZExt, LHS->Width, {DefaultWidth}});
      if (UserCompKinds.count(Inst::SExt))
        Comps.emplace_back(Component{Inst::SExt, LHS->Width, {DefaultWidth}});
    } else {
      Comps.emplace_back(Component{Inst::ZExt, LHS->Width, {DefaultWidth}});
      Comps.emplace_back(Component{Inst::SExt, LHS->Width, {DefaultWidth}});
    }
  }
  // Sometimes the result is truncated to smaller output iN
  if (DefaultWidth > LHS->Width) {
    if (TestMode) {
      if (UserCompKinds.count(Inst::Trunc))
        Comps.emplace_back(Component{Inst::Trunc, LHS->Width, {DefaultWidth}});
    } else {
      Comps.emplace_back(Component{Inst::Trunc, LHS->Width, {DefaultWidth}});
    }
  }
}

void InstSynthesis::initComponents(InstContext &IC) {
  for (unsigned J = 0; J < Comps.size(); ++J) {
    auto &Comp = Comps[J];
    std::string LocVarStr;
    // First, init component inputs
    std::vector<Inst *> CompOps;
    for (unsigned K = 0; K < Comp.OpWidths.size(); ++K) {
      LocVar In = std::make_pair(J+1, K+1);
      LocVarStr = getLocVarStr(In, LOC_PREFIX);
      Inst *Loc = IC.createVar(LocInstWidth, LocVarStr);
      LocInstMap[LocVarStr] = std::make_pair(In, Loc);
      // Add component input location to P
      P.emplace_back(In, Loc);
      // Create concrete component input encoded as a fresh variable
      LocVarStr = getLocVarStr(In, COMP_INPUT_PREFIX);
      if (Comp.OpWidths[K] != 0)
        Loc = IC.createVar(Comp.OpWidths[K], LocVarStr);
      else
        Loc = IC.createVar(DefaultWidth, LocVarStr);
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
      Comp.Width = DefaultWidth;
    Loc = IC.getInst(Comp.Kind, Comp.Width, CompOps);
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
  llvm::outs() << "number of inputs: " << Inputs.size() << ", "
               << "constants: " << ConstComps.size() << "\n";
  llvm::outs() << "N: " << N << ", M: " << M << "\n";
  llvm::outs() << "default instruction width: " << DefaultWidth << "\n";
  llvm::outs() << "component library: ";
  for (auto const &Comp : Comps)
    llvm::outs() << Inst::getKindName(Comp.Kind)
                 << " (" << Comp.Width << ", " << Comp.OpWidths.size() << "); ";
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

  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << "consistency constraints:\n";
  // Don't wire the outputs of two components
  for (unsigned J = 0; J < R.size(); ++J) {
    auto const &L_x = R[J];
    for (unsigned K = J+1; K < R.size(); ++K) {
      auto const &L_y = R[K];
      InvalidWirings.insert(std::make_pair(L_x.first, L_y.first));
      Inst *Ne = IC.getInst(Inst::Ne, 1, {L_x.second, L_y.second});
      Ret = IC.getInst(Inst::And, 1, {Ret, Ne});
      if (DebugSynthesis && DebugLevel > 1)
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

  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << "acyclicity constraints:\n";
  // Component inputs
  for (auto const &L_x : P) {
    // Grab a component's output LocInst
    std::string LocVarStr = LOC_PREFIX + std::to_string(L_x.first.first)
                                       + LOC_SEP + "0";
    assert(LocInstMap.count(LocVarStr) && "unknown location variable");
    auto const &L_y = LocInstMap[LocVarStr];
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << getLocVarStr(L_x.first) << " < "
                   << L_x.first.first << LOC_SEP << "0" << "\n";
    Inst *Ult = IC.getInst(Inst::Ult, 1, {L_x.second, L_y.second});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ult});
  }

  return Ret;
}

Inst *InstSynthesis::getLocVarConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << "location variable constraints:\n";
  std::vector<LocInst> Tmp(P.begin(), P.end());
  Tmp.insert(Tmp.end(), I.begin(), I.end());
  // All inputs
  for (auto const &L_x : Tmp) {
    if (DebugSynthesis && DebugLevel > 1)
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

  // All component outputs
  for (auto const &L_x : R) {
    Inst *Ult = 0;
    Ult = IC.getInst(Inst::Ult, 1,
                     {L_x.second, IC.getConst(APInt(L_x.second->Width, N))});
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << N << " <= " << getLocVarStr(L_x.first);
    Inst *Ne = IC.getInst(Inst::Eq, 1, {Ult, IC.getConst(APInt(1, false))});
    Ret = IC.getInst(Inst::And, 1, {Ret, Ne});

    Ult = IC.getInst(Inst::Ult, 1, {L_x.second,
                                    IC.getConst(APInt(L_x.second->Width,
                                                M))});
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << " < " << M << "\n";
    Ret = IC.getInst(Inst::And, 1, {Ret, Ult});
  }

  return Ret;
}

Inst *InstSynthesis::getOutputLocVarConstraint(int Begin, int End,
                                               InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  Inst *Ult = IC.getInst(Inst::Ult, 1,
                         {O.second, IC.getConst(APInt(O.second->Width, Begin))});
  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << Begin << " <= " << getLocVarStr(O.first);

  Inst *Ne = IC.getInst(Inst::Eq, 1, {Ult, IC.getConst(APInt(1, false))});
  Ret = IC.getInst(Inst::And, 1, {Ret, Ne});

  Ult = IC.getInst(Inst::Ult, 1, {O.second,
                                  IC.getConst(APInt(O.second->Width,
                                              End))});
  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << " < " << End << "\n";
  Ret = IC.getInst(Inst::And, 1, {Ret, Ult});

  return Ret;
}

Inst *InstSynthesis::getConnectivityConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, true));

  if (DebugSynthesis && DebugLevel > 2)
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
      if (DebugSynthesis && DebugLevel > 2)
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

  if (DebugSynthesis && DebugLevel > 1)
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
      if (DebugSynthesis && DebugLevel > 1)
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
      if (DebugSynthesis && DebugLevel > 1)
        llvm::outs() << getLocVarStr(L_x.first) << " == "
                     << getLocVarStr(L_y.first) << " || ";
    }
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << "false\n";
    // Add to result
    if (Ante != IC.getConst(APInt(1, false)))
      Ret = IC.getInst(Inst::And, 1, {Ret, Ante});
  }

  return Ret;
}

Inst *InstSynthesis::getOutputDefinednessConstraint(InstContext &IC) {
  Inst *Ret = IC.getConst(APInt(1, false));

  if (DebugSynthesis && DebugLevel > 1)
    llvm::outs() << "output-definedness constraints:\n";
  unsigned Width = CompInstMap[O.first]->Width;
  // Inputs
  for (auto const &In : I) {
    if (isWiringInvalid(In.first, O.first))
      continue;
    Inst *Eq = IC.getInst(Inst::Eq, 1, {O.second, In.second});
    Ret = IC.getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(In.first) << " || ";
  }
  // Component outputs
  for (auto const &L_y : R) {
    if (isWiringInvalid(L_y.first, O.first))
      continue;
    Inst *Eq = IC.getInst(Inst::Eq, 1, {O.second, L_y.second});
    Ret = IC.getInst(Inst::Or, 1, {Ret, Eq});
    if (DebugSynthesis && DebugLevel > 1)
      llvm::outs() << getLocVarStr(O.first) << " == "
                   << getLocVarStr(L_y.first) << " || ";
  }
  if (DebugSynthesis && DebugLevel > 1)
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
                                         ProgramWiring &CandWiring,
                                         std::map<LocVar, llvm::APInt> &ConstValMap,
                                         InstContext &IC) {
  LineLocVarMap LineWiring;
  LocVar OutLoc = parseWiringModel(Solution, LineWiring, ConstValMap);
  if (!CompInstMap.count(OutLoc))
    report_fatal_error("synthesis bug: output location not wired");
  auto Left = getLocVarStr(O.first, LOC_PREFIX);
  auto Right = getLocVarStr(OutLoc, LOC_PREFIX);
  CandWiring.emplace_back(LocInstMap[Left], LocInstMap[Right]);

  if (DebugSynthesis && DebugLevel > 2) {
    llvm::outs() << "found valid wiring, output "
                 << getLocVarStr(OutLoc) << ".\n";
    llvm::outs() << "line\tlocations\n";
    for (auto const &E : LineWiring) {
      llvm::outs() << E.first << "\t";
      for (auto const &Loc : E.second)
        llvm::outs() << getLocVarStr(Loc) << " ";
      llvm::outs() << "\n";
    }
  }

  auto OpLocs = getOpLocs(OutLoc);
  if (DebugSynthesis && DebugLevel > 2) {
    llvm::outs() << "creating program from wiring\n";
    llvm::outs() << "- starting with OutLoc " << getLocVarStr(OutLoc)
                 << ", OpLocs { ";
    for (auto const &OpLoc : OpLocs)
      llvm::outs() << getLocVarStr(OpLoc) << " ";
    llvm::outs() << "}\n";
  }
  Inst *Res = createInstFromWiring(OutLoc, OpLocs, LineWiring,
                                   ConstValMap, CandWiring, IC);
  assert(Res && "creating instruction from wiring failed");

  return Res;
}

Inst *InstSynthesis::createInstFromWiring(
      const LocVar &OutLoc,
      const std::vector<LocVar> &OpLocs,
      const LineLocVarMap &LineWiring,
      const std::map<LocVar, llvm::APInt> &ConstValMap,
      ProgramWiring &CandWiring,
      InstContext &IC) {
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
    if (DebugSynthesis && DebugLevel > 2) {
      llvm::outs() << "- continue with OutLoc " << getLocVarStr(Match)
                   << ", OpLocs {";
      for (auto const &R : Res)
        llvm::outs() << getLocVarStr(R) << " ";
      llvm::outs() << "}\n";
    }
    // Recurse
    Inst *Op = createInstFromWiring(Match, Res, LineWiring,
                                    ConstValMap, CandWiring, IC);
    // Store result
    Ops.push_back(Op);
  }

  // It it a constant?
  if (ConstValMap.count(OutLoc)) {
    if (DebugSynthesis && DebugLevel > 2)
      llvm::outs() << "- creating constant inst " << getLocVarStr(OutLoc)
                   << " with value " << ConstValMap.at(OutLoc) << "\n";
    return IC.getConst(ConstValMap.at(OutLoc));
  }
  // Is it an input?
  if (OutLoc.first == 0) {
    if (DebugSynthesis && DebugLevel > 2)
      llvm::outs() << "- creating input inst " << getLocVarStr(OutLoc) << "\n";
    return CompInstMap[OutLoc];
  }
  // Grab the target component
  Component Comp = Comps[OutLoc.first-1];
  assert(OutLoc.first >= 1 && "invalid component location variable");
  assert((Ops.size() == Comp.OpWidths.size()) && "op num mismatch");
  if (DebugSynthesis && DebugLevel > 2) {
    llvm::outs() << "- creating inst " << Inst::getKindName(Comp.Kind)
                 << ", width " << Comp.Width << "\n";
    llvm::outs() << "before junk removal:\n";
    ReplacementContext Context;
    PrintReplacementRHS(llvm::outs(), IC.getInst(Comp.Kind, Comp.Width, Ops),
                        Context);
  }

  return createJunkFreeInst(Comp.Kind, Comp.Width, Ops, IC);
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

  if (DebugSynthesis && DebugLevel > 2)
    llvm::outs() << "- looking for OpLoc wiring "
                 << getLocVarStr(OpLoc) << "\n";
  for (auto const &E : LineWiring) {
    if (E.second.count(OpLoc)) {
      if (DebugSynthesis && DebugLevel > 2)
        llvm::outs() << "- found wiring input on line " << E.first << ", taking ";
      for (auto const &In : E.second) {
        // Take either input, constant, or component output of matching width
        if ((In.first == 0 || In.second == 0) && !isWiringInvalid(In, OpLoc)) {
          Match = In;
          if (DebugSynthesis && DebugLevel > 2)
            llvm::outs() << getLocVarStr(Match);
          FoundMatch = true;
          break;
        }
      }
      if (DebugSynthesis && DebugLevel > 2)
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
    if (Ops[0] == Ops[1])
      return IC.getConst(APInt(Width, 0));
    else if (Ops[1] == IC.getConst(APInt(Width, 0)))
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
    if (Ops[0]->K == Inst::Const)
      return IC.getConst(APInt(Width, Ops[0]->Val.getZExtValue()));
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

void InstSynthesis::getInputVars(Inst *I, std::vector<Inst *> &InputVars) {
  if (I->K == Inst::Var)
    InputVars.push_back(I);
  for (auto Iz : I->orderedOps())
    getInputVars(Iz, InputVars);
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
    } else if (Loc.first == 0 && Loc.second > Inputs.size()) {
      Str = "const";
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
  for (unsigned J = 0; J < Comp.OpWidths.size(); ++J) {
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

bool InstSynthesis::hasConst(Inst *I) {
  if (I->K == Inst::Const)
    return true;
  bool Res = false;
  for (auto Iz : I->orderedOps())
    Res |= hasConst(Iz);
  return Res;
}

}
