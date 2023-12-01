//===---- X86PreserveNoneFuncList.cpp- Handling PreserveNone calling convention  ----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "X86.h"
#include "X86InstrInfo.h"
#include "X86Subtarget.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include <fcntl.h>
#include <queue>
#include <set>
#include <unistd.h>

using namespace llvm;

namespace llvm {
class MemoryBuffer;
}

#define DEBUG_TYPE "x86-preserve-none"

extern cl::opt<std::string> WritePreserveNoneFilePath;
extern cl::opt<std::string> LoadPreserveNoneFilePath;

static cl::opt<bool> PreserveNoneInfect(
    "x86-preserve-none-infect", cl::init(false),
    cl::desc(
        "Infect preserve-none calling convention into callers if possible."));

STATISTIC(NumPreserveNone, "Number of preserve-none functions");
STATISTIC(NumPreserveNoneInfected,
          "Number of preserve-none functions infected");

namespace {
class X86PreserveNonePass : public MachineFunctionPass {
public:
  static char ID;
  int FD;

  X86PreserveNonePass() : MachineFunctionPass(ID) {}

  StringRef getPassName() const override { return "X86 Preserve-None"; }

  bool runOnMachineFunction(MachineFunction &MF) override;
  bool WritePreserveNoneList(MachineFunction &MF);
  bool LoadPreserveNoneList(MachineFunction &MF);
  ~X86PreserveNonePass() {
    if (this->FD)
      close(this->FD);
  }

private:
  std::set<std::string> FuncNameSet;
  MachineRegisterInfo *MRI = nullptr;
};

class X86PreserveNoneInfectionPass : public ModulePass {
public:
  static char ID;

  X86PreserveNoneInfectionPass() : ModulePass(ID) {}

  StringRef getPassName() const override {
    return "X86 Preserve-None Infection";
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<MachineModuleInfoWrapperPass>();
    AU.addPreserved<MachineModuleInfoWrapperPass>();
    AU.setPreservesAll();
    ModulePass::getAnalysisUsage(AU);
  }
  bool runOnModule(Module &M) override;
  ~X86PreserveNoneInfectionPass() = default;
};
} // end anonymous namespace

char X86PreserveNonePass::ID = 0;
char X86PreserveNoneInfectionPass::ID = 0;

FunctionPass *llvm::createPreserveNonePass() {
  return new X86PreserveNonePass();
}
ModulePass *llvm::createPreserveNoneInfectionPass() {
  return new X86PreserveNoneInfectionPass();
}

INITIALIZE_PASS(X86PreserveNonePass, DEBUG_TYPE, DEBUG_TYPE, false, false)
INITIALIZE_PASS(X86PreserveNoneInfectionPass, "x86-preserve-none-infection",
                "x86-preserve-none-infection", false, false)

// 1. loop through all function
//      -> finding seeds to intialize the worklist
//      -> record a dict mapping from function to its callers
// 2. for func in worklist
//      for caller in caller_map[func]
//        -> if the caller meet the requirement && cc is normal
//          -> add the caller to the worklist
//        -> otherwise, continue
// 3. iterating through the worklist is empty
bool X86PreserveNoneInfectionPass::runOnModule(Module &M) {
  // Make sure this option is on.
  if (!PreserveNoneInfect)
    return false;

  // Check if there's anything in the module. If it's empty, then there's
  // nothing to outline.
  if (M.empty())
    return false;

  auto isInfectableFunc = [](const Function &F) {
    return !F.isWeakForLinker() && F.hasLocalLinkage() && !F.isDeclaration();
  };

  auto hasPreserveNoneAttr = [](const Function &F) {
    return F.hasFnAttribute("no_callee_saved_registers") ||
           F.getCallingConv() == CallingConv::PreserveNone ||
           F.hasFnAttribute("preserve_none");
  };

  std::set<MachineFunction *> VisitedMF;
  std::deque<MachineFunction *> MFWorkList;

  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();
  for (const Function &F : M) {
    MachineFunction *MF = MMI.getMachineFunction(F);
    // We only care about MI counts here. If there's no MachineFunction at this
    // point, then there won't be after the outliner runs, so let's move on.
    if (!MF)
      continue;

    if (hasPreserveNoneAttr(F)) {
      outs() << "Found PreserveNone Func: " << F.getName()
             << ", start infecting ...\n";
      MFWorkList.push_back(MF);
    }
  }

  while (!MFWorkList.empty()) {
    auto *MF = MFWorkList.front();
    auto &F = MF->getFunction();
    MFWorkList.pop_front();
    if (VisitedMF.count(MF))
      continue;

    VisitedMF.insert(MF);

    if (!hasPreserveNoneAttr(F) &&
        (!isInfectableFunc(F) || llvm::any_of(F.users(), [](const User *U) {
          return !isa<CallBase>(U);
        })))
      continue;

    // outs() << "stage2\n";
    for (auto *U : F.users()) {
      auto *CB = cast<CallBase>(U);
      Function *Caller = CB->getCaller();
      auto *CallerMF = MMI.getMachineFunction(*Caller);
      // outs() << "Found caller: " << CallerMF->getName() << "\n";
      if (!VisitedMF.count(CallerMF) && !hasPreserveNoneAttr(*Caller)) {
        // outs() << "add caller: " << CallerMF->getName() << "\n";
        MFWorkList.push_back(CallerMF);
      }
    }

    if (!hasPreserveNoneAttr(F)) {
      NumPreserveNoneInfected++;
      F.addFnAttr("no_callee_saved_registers", "1");
      outs() << "PreserveNone: infect the function " << F.getName()
             << " to preserve-none\n";
    }
  }

  return NumPreserveNoneInfected > 0;
}

bool X86PreserveNonePass::WritePreserveNoneList(MachineFunction &MF) {
  if (MF.getFunction().isDeclaration())
    return false;

  if (FuncNameSet.count(std::string(MF.getName())))
    return false;

  FuncNameSet.insert(std::string(MF.getName()));

  if (!this->FD) {
    if (llvm::sys::fs::exists(WritePreserveNoneFilePath) &&
        !llvm::sys::fs::is_regular_file(WritePreserveNoneFilePath)) {
      outs() << "Failed, Found a non-regular file: "
             << WritePreserveNoneFilePath << "\n";
      return false;
    }
  }
  // Create file lock
  struct flock lock;
  lock.l_type = F_WRLCK; // write lock
  lock.l_whence = SEEK_SET;
  lock.l_start = 0;
  lock.l_len = 0;

  // write data
  std::error_code EC;
  raw_fd_ostream OS(WritePreserveNoneFilePath, EC,
                    llvm::sys::fs::OF_TextWithCRLF | llvm::sys::fs::OF_Append);
  if (EC) {
    outs() << "Could not open " << WritePreserveNoneFilePath;
    return false;
  }

  if (std::error_code EC = llvm::sys::fs::openFileForReadWrite(
          WritePreserveNoneFilePath, this->FD, llvm::sys::fs::CD_CreateNew,
          llvm::sys::fs::OF_Text | llvm::sys::fs::OF_Append)) {
    return false;
  }

  // Lock file
  if (fcntl(this->FD, F_SETLKW, &lock) == -1) {
    outs() << "Unable to lock file\n";
    close(this->FD);
    return false;
  }

  llvm::raw_fd_ostream fds(this->FD, true);
  fds << MF.getName() << "\n";

  // Unlock file
  lock.l_type = F_UNLCK;
  if (fcntl(this->FD, F_SETLKW, &lock) == -1) {
    outs() << "Unable to unlock file\n";
    return false;
  }

  return true;
}

bool X86PreserveNonePass::LoadPreserveNoneList(MachineFunction &MF) {
  bool Changed = false;
  SmallVector<StringRef, 32> lines;
  if (MF.getFunction().isDeclaration())
    return false;

  // load if map is empty
  if (FuncNameSet.empty()) {
    if (!llvm::sys::fs::exists(LoadPreserveNoneFilePath) ||
        !llvm::sys::fs::is_regular_file(LoadPreserveNoneFilePath)) {
      outs() << "Fail to find file: " << LoadPreserveNoneFilePath << "\n";
      return false;
    }
    auto fileBuf = llvm::MemoryBuffer::getFile(LoadPreserveNoneFilePath);

    if (!fileBuf) {
      outs() << "Fail to open file: " << LoadPreserveNoneFilePath << "\n";
      return false;
    }

    fileBuf.get()->getBuffer().split(lines, "\n");
    for (auto line : lines) {
      auto FuncName = line.trim();
      if (!FuncName.empty() && !FuncNameSet.count(std::string(FuncName)))
        FuncNameSet.insert(std::string(FuncName));
    }
  }
  if (FuncNameSet.count(std::string(MF.getName()))) {
    MF.getFunction().addFnAttr("no_callee_saved_registers", "1");
    Changed = true;
  }
  return Changed;
}

bool X86PreserveNonePass::runOnMachineFunction(MachineFunction &MF) {
  // MRI = &MF.getRegInfo();

  // 1. Write PreserveNone function list
  if (WritePreserveNoneFilePath != "-") {
    return WritePreserveNoneList(MF);
    // 2. Load PreserveNone function list
  } else if (LoadPreserveNoneFilePath != "-") {
    return LoadPreserveNoneList(MF);
  }

  return false;
}
