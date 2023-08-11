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
#include "llvm/Demangle/Demangle.h"

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

            /*
            TODO: 梳理CFG的顺序
            */
            // while (true)
            // {
            std::vector<BasicBlock *> bbs;
            BasicBlock *end = nullptr;
            for (BasicBlock &BB : F)
            {
                bbs.push_back(&BB);
                end = &BB;
            }

            for (auto BB : bbs)
            {
                if (succ_empty(BB))
                {
                    BB->moveAfter(end);
                }
            }

            //     if(flag == false)
            // }

            // if (F.getName() == "_ZN5rmqtt6broker7session12SessionState9subscribe28_$u7b$$u7b$closure$u7d$$u7d$17h368dc951787d5034E")
            // {
            //     for (auto &bb : F.getBasicBlockList())
            //     {
            //         errs() << bb << "\n";
            //         for (auto &inst : bb.getInstList())
            //         {
            //             unsigned int opcode = inst.getOpcode();
            //             if (opcode == Instruction::Call)
            //             {
            //                 CallInst *call = static_cast<CallInst *>(&inst);
            //                 errs()
            //                     << "fxxk: " << *call << "\n";
            //                 DebugLoc ACL_dbg_line = call->getDebugLoc();
            //                 if (ACL_dbg_line.get())
            //                 {
            //                     auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
            //                     errs() << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << ": " << ACL_dbg_line->getLine() << ":" << ACL_dbg_line->getColumn() << "\n";
            //                 }
            //             }
            //             else if (opcode == Instruction::Invoke)
            //             {
            //                 InvokeInst *call = static_cast<InvokeInst *>(&inst);
            //                 errs()
            //                     << "fxxk: " << *call << "\n";
            //                 DebugLoc ACL_dbg_line = call->getDebugLoc();
            //                 if (ACL_dbg_line.get())
            //                 {
            //                     auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
            //                     errs() << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << ": " << ACL_dbg_line->getLine() << ":" << ACL_dbg_line->getColumn() << "\n";
            //                 }
            //             }
            //         }
            //     }
            // }

            // DebugLoc ACL_dbg_line;

            // ACL_dbg_line = F.getEntryBlock().getTerminator()->getDebugLoc();
            // if (ACL_dbg_line.get())
            // {
            //     auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
            //     errs() << F.getName() << "------" << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << ": " << ACL_dbg_line->getLine() << "\n";
            // }
            // else
            //     errs()
            //         << F.getName() << '\n';
            errs()
                << F.getName() << '\n';

            errs()
                << llvm::demangle(F.getName().str()) << '\n';

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