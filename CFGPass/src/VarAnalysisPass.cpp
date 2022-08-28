#include "llvm/Pass.h"
#include "../../Include/VarAnalysis.h"

using namespace llvm;

namespace
{
    class VarAnalysisPass : public ModulePass
    {
    public:
        static char ID;
        std::map<std::string, BasicBlock *> ALLBasicBlocks;
        std::set<BasicBlock *> keyBBs;

        int traverseFuncForKBB(Module &M, Function &F);

        VarAnalysisPass() : ModulePass(ID)
        {
        }

        bool runOnModule(Module &M) override
        {
            mqttactic::VarAnalysis *var_analyzer = new mqttactic::VarAnalysis(M);

            for (Module::iterator mi = M.begin(); mi != M.end(); ++mi)
            {
                Function &f = *mi;
                for (auto &bb : f)
                {
                    std::string bb_str = bb.getParent()->getName().str() + ":" + getBBLabel(&bb);
                    ALLBasicBlocks.insert(std::pair<std::string, llvm::BasicBlock *>(bb_str, &bb));
                }
                var_analyzer->SearchKeyVar(M, f);
            }

            int cou = 0;
            for (auto key_var : var_analyzer->key_variables)
            {
                cou += var_analyzer->SemanticKeyBasicBlocks[key_var].size();
            }
            errs() << cou << "\n\n\n\n";

            for (auto key_var : var_analyzer->key_variables)
            {
                errs() << "-----------------KEYVAR-----------------\n"
                       << key_var->name << "\n\n\n\n";
                for (auto sbb : var_analyzer->SemanticKeyBasicBlocks[key_var])
                {
                    errs() << sbb->bb->getParent()->getName() << "\n"
                           << sbb->semantics << "\n";
                    // for (auto var : sbb->values)
                    // {
                    //     errs() << *var << "\n";
                    // }
                    for (auto kbb_c : sbb->contexts)
                    {
                        for (auto bb : kbb_c)
                        {
                            errs() << bb->getParent()->getName() << ":" << var_analyzer->getBBLabel(bb) << " --> ";
                        }
                        errs() << "\n";
                    }
                    errs() << "----------------------------------\n";

                    errs() << *(sbb->bb) << "\n\n";
                }
            }

            return false;
        }
    };

    int VarAnalysisPass::traverseFuncForKBB(Module &M, Function &F)
    {
        std::set<Instruction *> insts;
        std::set<Instruction *>::iterator it;
        int retval = 1;
        for (BasicBlock &BB : F)
        {
            for (auto key_var : var_analyzer->key_variables)
            {
                if (var_analyzer->SemanticKeyBasicBlocks[key_var].find(&BB) != var_analyzer->SemanticKeyBasicBlocks[key_var].end())
                {
                    keyBBs.insert(keyBBs.end(), &BB);
                    retval = 2;
                }
            }
            for (Instruction &I : BB)
            {
                Instruction *inst = &I;
                unsigned int opcode = inst->getOpcode();
                switch (opcode)
                {
                case Instruction::Call:
                {
                    CallInst *call = static_cast<CallInst *>(inst);
                    std::string calledFuncName = "";
                    if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                    {
                        Function *ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()
                                                                         ->stripPointerCastsAndAliases());
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (ptrFunc)
                        {
                            calledFuncName = ptrFunc->getName().str();
                        }
                        else if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    bool isKeyFunc = false;
                    std::map<std::string, short>::iterator Fit = ALLFunctions.find(calledFuncName);

                    // (broker)
                    if (Fit != ALLFunctions.end())
                    {
                        if (Fit->second == 1)
                            goto FINDKEYFUNCS_3;
                        else if (Fit->second == 2)
                        {
                            isKeyFunc = true;
                            goto FINDKEYFUNCS_3;
                        }
                        else
                        {
                            // errs() << "Call function: " << calledFuncName << "\n";
                            Function &calledFunc = *M.getFunction(calledFuncName);
                            Fit->second = 1;
                            int rt = traverseFuncForKBB(M, calledFunc, var_analyzer);
                            if (rt == 2)
                            {
                                isKeyFunc = true;
                                Fit->second = 2;
                            }
                        }

                    FINDKEYFUNCS_3:
                        if (isKeyFunc)
                        {
                            if (keyBBs.find(call->getParent()) == keyBBs.end())
                            {
                                keyBBs.insert(keyBBs.end(), call->getParent());
                            }
                            keyFuncs.insert(calledFuncName);
                            retval = 2;
                        }
                    }
                    break;
                }
                case Instruction::Invoke:
                {
                    InvokeInst *call = static_cast<InvokeInst *>(inst);
                    std::string calledFuncName = "";
                    if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                    {
                        Function *ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()
                                                                         ->stripPointerCastsAndAliases());
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (ptrFunc)
                            calledFuncName = ptrFunc->getName().str();
                        else if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    bool isKeyFunc = false;
                    std::map<std::string, short>::iterator Fit = ALLFunctions.find(calledFuncName);

                    // (broker)
                    if (Fit != ALLFunctions.end())
                    {
                        if (Fit->second == 1)
                            goto FINDKEYFUNCS_4;
                        else if (Fit->second == 2)
                        {
                            isKeyFunc = true;
                            goto FINDKEYFUNCS_4;
                        }
                        else
                        {

                            // errs() << "Call function: " << calledFuncName << "\n";
                            Function &calledFunc = *M.getFunction(calledFuncName);
                            Fit->second = 1;
                            int rt = traverseFuncForKBB(M, calledFunc, var_analyzer);
                            if (rt == 2)
                            {
                                isKeyFunc = true;
                                Fit->second = 2;
                            }
                        }

                    FINDKEYFUNCS_4:
                        if (isKeyFunc)
                        {
                            if (keyBBs.find(call->getParent()) == keyBBs.end())
                            {
                                keyBBs.insert(keyBBs.end(), call->getParent());
                            }
                            keyFuncs.insert(calledFuncName);
                            retval = 2;
                        }
                    }
                    break;
                }

                default:
                    break;
                }
            }
        }
        return retval;
    }
}

char VarAnalysisPass::ID = 0;

// Register for opt
static RegisterPass<VarAnalysisPass> X("VarAnalysisPass", "Var analysis pass");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
                                [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM)
                                {
                                    PM.add(new VarAnalysisPass());
                                });