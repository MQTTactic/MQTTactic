#include <set>
#include <vector>
#include <map>
#include <fstream>
#include <math.h>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/GlobalAlias.h"

using namespace llvm;

namespace
{
    std::string getBBLabel(const BasicBlock *Node)
    {
        if (!Node->getName().empty())
            return Node->getName().str();

        std::string Str;
        raw_string_ostream OS(Str);

        Node->printAsOperand(OS, false);
        return OS.str();
    }

    struct Hello : public FunctionPass
    {
        static char ID;
        Hello() : FunctionPass(ID) {}
        bool runOnFunction(Function &F) override
        {
            DebugLoc ACL_dbg_line;

            ACL_dbg_line = F.getEntryBlock().getTerminator()->getDebugLoc();
            // if (ACL_dbg_line.get())
            // {
            //     auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
            //     errs() << F.getName() << "------" << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << "\n";
            // }
            // else
            errs()
                << F.getName() << '\n';
            return false;
        }
    };
}

char Hello::ID = 0;

// Register for opt
static RegisterPass<Hello> X("funcs", "Hello World Pass");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
                                [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM)
                                {
                                    PM.add(new Hello());
                                });