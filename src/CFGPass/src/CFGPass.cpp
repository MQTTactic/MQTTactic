/*
clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o CFGPass.so
opt -load ./CFGPass.so -CFG ./mosquitto.bc -o /dev/null 2>
handle__publish.output

需要提前获取：
1. 所有自定义函数名 "./ALLFunctions"
*/

#include "VarAnalysis.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

// Here we register the pass arguments
cl::opt<string> Handler("Handler", cl::desc("Specify handler"), cl::Required);


class CFGPass : public ModulePass
{
public:
    typedef std::vector<BasicBlock*> PathType;
    // 用于寻找从handler到endBB"可能"经过的keyBB路径(一般是函数调用所处的BB)
    struct keyBBPath
    {
        BasicBlock* bb;
        std::string func;
        // 表示这条路径上这个BB是必须经过的
        bool mustBePassed;
    };
    // 用于分析单个函数，从首个BB到return的所有可能经过的keyBB路径，不会进入Call
    struct keyBBPathWithoutCall
    {
        BasicBlock* bb;
        // 这个BB调用的函数
        std::set<std::string> calledFuncs;
    };

    struct SemanticABB
    {
        BasicBlock*     bb;
        bool            isVirtualHead = false;
        bool            isVirtualTail = false;
        llvm::Function* callSite = nullptr;
        // 这个BB调用的函数
        std::map<llvm::Instruction*, llvm::Function*> calledFuncs;
        // {Inst: "semantic"}, e.g., {I: "func===LIST:sub_read"}, {I: "func===CALLSITE"}
        std::map<llvm::Instruction*, std::string> semanticInsts;
    };

    struct FuncSliceGraphHeadTail
    {
        SemanticABB* head;
        SemanticABB* tail;
    };

    struct SemanticPathType
    {
        std::string              ptSemantic = "";
        std::vector<std::string> ptSemanticVec;
        std::vector<std::string> ptFunc;
        PathType                 pt;
    };

    static char ID;
    // variable analyzer
    mqttactic::VarAnalysis* var_analyzer;
    // first: 函数名; second: 0表示还未遍历到/1表示遍历过但是不存在关键操作/2表示遍历过并找到了关键操作(但是可能需要几层函数调用)/3表示函数是ACL_CHECK
    std::map<std::string, short> ALLFunctions;

    std::set<const llvm::BasicBlock*> KeyBasicBlocks;
    // AnchorBB: 1. KBB or callsites that will flow to KBB; 2. ACL_CHECK
    std::set<BasicBlock*>               AnchorBBs;
    std::map<BasicBlock*, SemanticABB*> SemanticAnchorBBs;

    // 包含send__**ack的BB
    std::set<BasicBlock*> endBBs;
    // 包含关键操作的函数
    std::set<std::string> keyFuncs;
    // Anchor Basic Block CFG Graphs for each keyFuncs,
    std::map<llvm::Function*, std::map<SemanticABB*, std::map<SemanticABB*, bool>>> FuncSliceGraph;
    // Virtual Head and Tail node in FuncSliceGraph for each keyFuncs
    std::map<llvm::Function*, FuncSliceGraphHeadTail*> FuncSliceGraphHT;
    std::map<SemanticABB*, std::vector<SemanticABB*>>  VirtualCallStack;
    // when traverse CFG，we store {BB, (to ret)real paths count}
    std::map<BasicBlock*, long> completeBBs;
    // when traverse CFG, we store {BB, (to ret)KBB paths}
    std::map<BasicBlock*, std::map<std::string, PathType>> completeBBs_kpath;
    // Function related to handler
    std::set<Function*> HFuncs;

    std::map<Function*, std::map<std::string, SemanticPathType*>> completeFunc_kpath;
    // 已完成遍历的BB之间的边
    std::map<BasicBlock*, std::set<BasicBlock*>> completeEdges;
    // 0: 代表标准的handler函数的end, 1:return为终点 2: keyFuncs的调用为终点
    int switchEnd = 0;

    std::string handlerName;

    std::string outputDir = "../OUTPUT";

    int count = 0;

    /********************************
                Functions
    ********************************/

    void identifyKeyBasicBlock(Module& M, Function& F);
    // 递归遍历函数的所有指令，定位KBB以及调用链
    int traverseCallGraph(Module& M, Function& F);
    // Traverse the handler function
    int traverseCFG(Module& M, Function& F, BasicBlock* origin, std::vector<BasicBlock*> paths);
    // Transform the FuncPathTypes list to a graph
    void constructPathGraph(std::map<llvm::Function*, std::vector<PathType>>& FuncPathTypes);
    void printFuncSliceGraph(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticABB*> path);
    /* Use PathGraph to combine all possible Handler PATHTYPES combinations
     */
    void combinePathTypes(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticPathType> path, std::map<Function*, int> loopStatus, std::vector<BasicBlock*> contextPath, std::vector<Function*> callContext);
    // use the context of KBB to filter the Anchor BBs
    bool isFakeAnchorBB(BasicBlock* bb, std::vector<BasicBlock*> contextPath);
    // 清空所有ALLFunctions中的second
    bool clearALLFunctions();

    void getAllRelatedFuncs(Module& M, Function& F);

    // 获取BB的label
    std::string getBBLabel(const BasicBlock* Node);
    int         getBBLabelIdx(const Function* func, const BasicBlock* Node);


    // 递归遍历函数所有指令，直到找到endBB，返回可能经过的所有keyBBs
    bool traverseFuncToEnd(Module& M, Function& F, BasicBlock* end, bool foundEnd, std::vector<keyBBPath> path, std::vector<std::vector<keyBBPath>>& endPath, std::vector<std::vector<keyBBPath>>& results);
    // 递归遍历一个函数，从头到return
    void traverseFuncToReturn(Module& M, Function& F, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS);
    void traverseFuncToReturnWithoutCall(Module& M, Function& F, std::vector<keyBBPathWithoutCall>& result);

    // 从origin到dest的所有路径，用于计算路径总数
    long traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths);
    // 用于实际地提取出路径
    long traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths, std::vector<std::vector<BasicBlock*>>& results);

    bool isRetBBs(BasicBlock* bb);
    int  endOfHandler(CallBase* call);
    // (UNUSE)
    bool        isKeyBBs(std::string str);
    std::string replaceKeyBBsOrEndName(std::string str);

    CFGPass() : ModulePass(ID)
    {
        // 获取所有函数
        std::string   fname;
        std::ifstream infile("../ALLFunctions");
        if (infile.is_open())
        {
            while (!infile.eof())
            {
                std::getline(infile, fname);
                ALLFunctions.insert(std::map<std::string, short>::value_type(fname, 0));
            }
        }
        handlerName = Handler.c_str();
    }
    void getAnalysisUsage(AnalysisUsage& AU) const override
    {
        AU.setPreservesCFG();
        AU.addRequired<LoopInfoWrapperPass>();
    }
    bool runOnModule(Module& M) override
    {
        Function&                F = *M.getFunction(handlerName);
        std::vector<BasicBlock*> paths;
        // 按函数存放函数内的关键BB们
        std::map<std::string, std::vector<BasicBlock*>> keyVecs;
        // 邻接矩阵，Nodes: entryBlock、return(nullptr)、path_Count
        std::map<BasicBlock*, std::map<BasicBlock*, long>> pathMap;


        keyFuncs.insert(F.getName().str());
        errs() << "[INFO]: Analyzing Function: " << F.getName().str() << "\n";

        identifyKeyBasicBlock(M, F);


        int cou = 0;
        for (auto key_var : var_analyzer->key_variables)
        {
            cou += var_analyzer->SemanticKeyBasicBlocks[key_var].size();
        }
        errs() << "[INFO]: Pointer Analysis found " << cou << " Semantic Key Basic Blocks in the entire source code\n";

        traverseCallGraph(M, F);

        errs() << "[INFO]: Anchor Basic Blocks in " << F.getName().str() << ": " << AnchorBBs.size() << "\n\n\n\n";


        // dbgs() << "\n\n/**********************/\n[DBG]: Semantic AnchorBB: \n/**********************/\n";
        // for (auto sabbit = SemanticAnchorBBs.begin(); sabbit != SemanticAnchorBBs.end(); sabbit++)
        // {
        //     dbgs() << "=====================================================\n";
        //     dbgs() << *(sabbit->first) << "\n\n";
        //     for (auto siit = sabbit->second->semanticInsts.begin(); siit != sabbit->second->semanticInsts.end(); siit++)
        //         dbgs() << *(siit->first) << ":" << siit->second << "\n";
        // }

        // Path Types for each keyFuncs
        std::map<llvm::Function*, std::vector<PathType>> FuncPathTypes;
        // Explore all KBB PathTypes for each keyFuncs
        for (auto fnit = keyFuncs.begin(); fnit != keyFuncs.end(); fnit++)
        {
            Function&                fn = *M.getFunction(*fnit);
            std::vector<BasicBlock*> _paths;
            // KBB PathTypes
            std::vector<PathType> path_types;

            completeBBs.clear();
            completeEdges.clear();
            completeBBs_kpath.clear();
            traverseCFG(M, fn, &(fn.getEntryBlock()), _paths);

            for (auto ptit = completeBBs_kpath[&(fn.getEntryBlock())].begin(); ptit != completeBBs_kpath[&(fn.getEntryBlock())].end(); ptit++)
            {
                path_types.push_back(ptit->second);
            }
            FuncPathTypes.insert(std::map<llvm::Function*, std::vector<PathType>>::value_type(&fn, path_types));
        }

        // Use FuncPathtypes to combine all possible Handler PATHTYPES combinations
        constructPathGraph(FuncPathTypes);

        dbgs() << "\n\n/**********************/\n[DBG]: FuncPathGraph: \n/**********************/\n";
        std::vector<CFGPass::SemanticABB*> pathtest;
        for (auto fptit = FuncPathTypes.begin(); fptit != FuncPathTypes.end(); fptit++)
        {
            dbgs() << fptit->first->getName().str() << ":\n";
            printFuncSliceGraph(M, *(fptit->first), FuncSliceGraphHT[fptit->first]->head, pathtest);
            dbgs() << "\n";
        }


        std::vector<SemanticPathType>  spts;
        SemanticPathType               empty_spt;
        std::map<llvm::Function*, int> loopStatus;
        std::vector<BasicBlock*>       contextPath;
        std::vector<Function*>         callContext;
        spts.push_back(empty_spt);
        combinePathTypes(M, F, FuncSliceGraphHT[&F]->head, spts, loopStatus, contextPath, callContext);


        dbgs() << "\n\n/**********************/\n[DBG]: PATHTYPES (" << completeFunc_kpath[&F].size() << "): \n/**********************/\n";
        for (auto spt : completeFunc_kpath[&F])
        {
            dbgs() << spt.first << "\n";
            // for (auto _f : spt.second->ptFunc)
            //     dbgs() << "->" << _f;
            // dbgs() << "\n";
        }

        return false;
    }
};

void CFGPass::identifyKeyBasicBlock(Module& M, Function& F)
{

    var_analyzer = new mqttactic::VarAnalysis(M);
    int stat = 0;

    // [TODO-x]: msg
    for (auto key_var : var_analyzer->key_variables)
    {

        if (key_var->varType == "Msg")
        {
            for (Module::iterator mi = M.begin(); mi != M.end(); ++mi)
            {
                Function& f = *mi;
                traverseFuncToReturn(M, f, var_analyzer->SemanticKeyBasicBlocks[key_var]);
            }
        }
    }
    // getAllRelatedFuncs(M, F);
    // for (auto f : HFuncs)
    // {
    //     var_analyzer->SearchKeyVar(M, *f);
    // }
    for (Module::iterator mi = M.begin(); mi != M.end(); ++mi)
    {
        Function& f = *mi;
        var_analyzer->SearchKeyVar(M, f);
        // dbgs() << stat << "/" << M.getFunctionList().size() << "\n";
        stat++;
    }


    var_analyzer->all_sess.clear();
    for (auto sess_node : var_analyzer->sess_graph)
    {
        if (var_analyzer->all_sess.find(sess_node.first) == var_analyzer->all_sess.end())
        {
            std::set<llvm::Value*> result;
            var_analyzer->DFS(sess_node.first, result);
            var_analyzer->all_sess.insert(result.begin(), result.end());
            var_analyzer->SESSIONS.push_back(result);
            for (auto _v : result)
            {
                var_analyzer->SESSIONS_idx[_v] = var_analyzer->SESSIONS.size() - 1;
            }
        }
    }

    // dbgs() << "[DBG]: " << var_analyzer->SESSIONS.size() << "\n";
    // for (auto sess : var_analyzer->SESSIONS)
    // {
    //     dbgs() << sess.size() << "\n";
    // }

    std::map<int, int> sess_set_freq;
    for (BasicBlock& BB : F)
    {
        for (Instruction& I : BB)
        {
            Use* operand_list = I.getOperandList();
            for (int i = 0; i < I.getNumOperands(); i++)
            {
                if (var_analyzer->SESSIONS_idx.find(operand_list[i]) != var_analyzer->SESSIONS_idx.end())
                {
                    if (sess_set_freq.find(var_analyzer->SESSIONS_idx[operand_list[i]]) == sess_set_freq.end())
                        sess_set_freq[var_analyzer->SESSIONS_idx[operand_list[i]]] = 1;
                    else
                        sess_set_freq[var_analyzer->SESSIONS_idx[operand_list[i]]] += 1;
                }
            }
        }
    }

    int _max = 0;
    for (auto sess : sess_set_freq)
    {
        if (sess.second >= _max)
        {
            _max = sess.second;
            var_analyzer->Handler_session = sess.first;
        }
    }


    // errs() << "[INFO]: Identifing the session in operations\n";
    // // Try to get the context of `DELIVER` operation backwardly, consist of the `Session` variables
    // std::map<llvm::Value*, std::vector<Function*>> sess_contexts;
    // for (auto key_var : var_analyzer->key_variables)
    // {
    //     if (key_var->varType == "Msg" && var_analyzer->SemanticKeyBasicBlocks[key_var].size() > 0)
    //     {
    //         for (auto sbb : var_analyzer->SemanticKeyBasicBlocks[key_var])
    //         {
    //             sess_contexts.clear();
    //             sbb.second->contexts.clear();
    //             for (auto inst : sbb.second->semantic_inst)
    //             {
    //                 Use* operand_list = inst.first->getOperandList();
    //                 for (int i = 0; i < inst.first->getNumOperands(); i++)
    //                 {
    //                     if (var_analyzer->all_sess.find(operand_list[i]) != var_analyzer->all_sess.end())
    //                     {
    //                         dbgs() << *(inst.first) << "\n";
    //                         var_analyzer->PointerAnalyzer->FindSessionContext(operand_list[i], var_analyzer->sess_type, sess_contexts);
    //                         // [TODO]: 可以只分析deliver第一个参数吗, 一般第一个destination (socket)
    //                         break;
    //                     }
    //                 }
    //             }
    //             for (auto ctx : sess_contexts)
    //             {
    //                 if (var_analyzer->SESSIONS[var_analyzer->Handler_session].find(ctx.first) != var_analyzer->SESSIONS[var_analyzer->Handler_session].end())
    //                 {
    //                     std::string str;
    //                     for (auto t : ctx.second)
    //                     {
    //                         str += "->" + t->getName().str();
    //                     }
    //                     if (sbb.second->call_contexts.find(str) == sbb.second->call_contexts.end())
    //                     {
    //                         sbb.second->call_contexts.insert(std::map<std::string, std::vector<llvm::Function*>>::value_type(str, ctx.second));
    //                         // dbgs() << str << "\n";
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }


    dbgs() << "{\n";
    for (auto key_var : var_analyzer->key_variables)
    {
        if (key_var->varType != "Msg")
            continue;
        dbgs() << "-----------------KEYVAR-----------------\n" << key_var->name << "\n\n\n\n";
        for (auto sbb : var_analyzer->SemanticKeyBasicBlocks[key_var])
        {
            DebugLoc dbl = sbb.first->back().getDebugLoc();
            if (dbl.get())
            {
                auto* Scope = cast<DIScope>(dbl.getScope());
                dbgs() << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << ": " << dbl->getLine() << ":" << dbl->getColumn() << "\n";
            }
            else
            {
                dbgs() << "No debug info\n";
            }

            dbgs() << "[SEMANTIC]: " << sbb.second->semantics << "\n";
            dbgs() << "[Instructions]: \n";
            for (auto var : sbb.second->semantic_inst)
            {
                dbgs() << *(var.first) << "\n";
            }

            dbgs() << "[CONTEXTS]: \n";
            for (auto kbb_c : sbb.second->contexts)
            {
                for (auto bb : kbb_c)
                {
                    // errs() << bb->getParent()->getName() << ":" <<
                    //     getBBLabel(bb) << " --> ";
                    dbl = bb->back().getDebugLoc();
                    if (dbl.get())
                    {
                        auto* Scope = cast<DIScope>(dbl.getScope());
                        dbgs() << Scope->getFilename().str() << ": " << dbl->getLine() << ":" << dbl->getColumn() << " --> ";
                    }
                }
                dbgs() << "\n";
            }

            dbgs() << "[Basic Block]: \n" << *(sbb.first) << "\n\n";
            dbgs() << "----------------------------------\n";
        }
    }
    dbgs() << "}\n";

    for (auto key_var : var_analyzer->key_variables)
    {
        for (auto sbb : var_analyzer->SemanticKeyBasicBlocks[key_var])
        {
            KeyBasicBlocks.insert(sbb.first);
        }
    }
}

int CFGPass::traverseCallGraph(Module& M, Function& F)
{
    std::set<Instruction*>           insts;
    std::set<Instruction*>::iterator it;
    int                              retval = 1;
    for (BasicBlock& BB : F)
    {
        for (Instruction& I : BB)
        {
            insts.insert(&I);
        }
    }
    for (it = insts.begin(); it != insts.end(); it++)
    {
        llvm::Instruction* inst = *it;
        unsigned int       opcode = inst->getOpcode();

        switch (opcode)
        {
        case Instruction::Call: {
            CallInst*                              call = static_cast<CallInst*>(inst);
            std::string                            calledFuncName = "";
            int                                    rt;
            bool                                   isKeyFunc = false;
            std::map<std::string, short>::iterator Fit;

            if (call->isIndirectCall() || call->getCalledFunction() == NULL)
            {
                Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
            Fit = ALLFunctions.find(calledFuncName);
            Function& calledFunc = *M.getFunction(calledFuncName);

            // 禁止进入系统函数(只关注broker中声明的函数)
            if (Fit != ALLFunctions.end() && calledFuncName != "log__printf")
            {
                if (Fit->second == 1)
                    goto FINDKEYFUNCS;
                else if (Fit->second == 2)
                {
                    isKeyFunc = true;
                    goto FINDKEYFUNCS;
                }
                else if (mqttactic::permission_check == calledFuncName)
                {
                    isKeyFunc = true;
                    Fit->second = 3;
                    goto FINDKEYFUNCS;
                }
                Fit->second = 1;
                rt = traverseCallGraph(M, calledFunc);
                if (rt == 2)
                {
                    isKeyFunc = true;
                    Fit->second = 2;
                }

            FINDKEYFUNCS:
                if (isKeyFunc)
                {
                    BasicBlock* inst_bb = inst->getParent();
                    if (SemanticAnchorBBs.find(inst_bb) == SemanticAnchorBBs.end())
                    {
                        struct SemanticABB* sabb = new SemanticABB();
                        sabb->bb = inst_bb;
                        SemanticAnchorBBs.insert(std::map<llvm::BasicBlock*, SemanticABB*>::value_type(inst_bb, sabb));
                    }
                    AnchorBBs.insert(inst_bb);
                    if (Fit->second != 3)
                    {
                        SemanticAnchorBBs[inst_bb]->semanticInsts.insert(std::map<llvm::Instruction*, std::string>::value_type(inst, F.getName().str() + "===" + "CALLSITE"));
                        SemanticAnchorBBs[inst_bb]->calledFuncs.insert(std::map<llvm::Instruction*, llvm::Function*>::value_type(inst, &calledFunc));
                        keyFuncs.insert(calledFuncName);
                    }
                    // if calledFuncName is `permission_check`
                    else
                    {
                        SemanticAnchorBBs[inst_bb]->semanticInsts.insert(std::map<llvm::Instruction*, std::string>::value_type(inst, F.getName().str() + "===" + "ACLCHECK"));
                    }
                    if (retval < 2)
                        retval = 2;
                }
            }

            break;
        }
        case Instruction::Invoke: {
            InvokeInst*                            call = static_cast<InvokeInst*>(inst);
            std::string                            calledFuncName = "";
            int                                    rt;
            bool                                   isKeyFunc = false;
            std::map<std::string, short>::iterator Fit;
            if (call->isIndirectCall() || call->getCalledFunction() == NULL)
            {
                Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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

            Fit = ALLFunctions.find(calledFuncName);
            Function& calledFunc = *M.getFunction(calledFuncName);
            // 禁止进入系统函数(只关注broker中声明的函数)
            if (Fit != ALLFunctions.end() && calledFuncName != "log__printf")
            {
                // errs() << "Call function: " << calledFuncName <<
                // "\n";

                if (Fit->second == 1)
                    goto FINDKEYFUNCS_2;
                else if (Fit->second == 2)
                {
                    isKeyFunc = true;
                    goto FINDKEYFUNCS_2;
                }
                else if (mqttactic::permission_check == calledFuncName)
                {
                    isKeyFunc = true;
                    Fit->second = 3;
                    goto FINDKEYFUNCS_2;
                }
                Fit->second = 1;
                rt = traverseCallGraph(M, calledFunc);
                if (rt == 2)
                {
                    isKeyFunc = true;
                    Fit->second = 2;
                }
            FINDKEYFUNCS_2:
                if (isKeyFunc)
                {
                    BasicBlock* inst_bb = inst->getParent();
                    if (SemanticAnchorBBs.find(inst_bb) == SemanticAnchorBBs.end())
                    {
                        struct SemanticABB* sabb = new SemanticABB();
                        sabb->bb = inst_bb;
                        SemanticAnchorBBs.insert(std::map<llvm::BasicBlock*, SemanticABB*>::value_type(inst_bb, sabb));
                    }
                    AnchorBBs.insert(inst_bb);
                    if (Fit->second != 3)
                    {
                        SemanticAnchorBBs[inst_bb]->semanticInsts.insert(std::map<llvm::Instruction*, std::string>::value_type(inst, F.getName().str() + "===" + "CALLSITE"));
                        SemanticAnchorBBs[inst_bb]->calledFuncs.insert(std::map<llvm::Instruction*, llvm::Function*>::value_type(inst, &calledFunc));
                        keyFuncs.insert(calledFuncName);
                    }
                    // if calledFuncName is `permission_check`
                    else
                    {
                        SemanticAnchorBBs[inst_bb]->semanticInsts.insert(std::map<llvm::Instruction*, std::string>::value_type(inst, F.getName().str() + "===" + "ACLCHECK"));
                    }
                    if (retval < 2)
                        retval = 2;
                }
            }

            break;
        }

        default:
            break;
        }
    }

    for (BasicBlock& BB : F)
    {
        const BasicBlock* bbp = &BB;
        for (auto key_var : var_analyzer->key_variables)
        {
            if (var_analyzer->SemanticKeyBasicBlocks[key_var].find(&BB) != var_analyzer->SemanticKeyBasicBlocks[key_var].end())
            {
                mqttactic::SemanticKBB* skbb = var_analyzer->SemanticKeyBasicBlocks[key_var][&BB];
                AnchorBBs.insert(&BB);
                if (SemanticAnchorBBs.find(&BB) == SemanticAnchorBBs.end())
                {
                    struct SemanticABB* sabb = new SemanticABB();
                    sabb->bb = &BB;
                    SemanticAnchorBBs.insert(std::map<llvm::BasicBlock*, SemanticABB*>::value_type(&BB, sabb));
                }
                for (auto siit = skbb->semantic_inst.begin(); siit != skbb->semantic_inst.end(); siit++)
                {
                    std::string semantic = BB.getParent()->getName().str() + "===";
                    switch (siit->second)
                    {
                    case mqttactic::READ: {
                        semantic += key_var->varType + "_read";
                        break;
                    }
                    case mqttactic::WRITE: {
                        semantic += key_var->varType + "_write";
                        break;
                    }
                    case mqttactic::WRITE0: {
                        semantic += key_var->varType + "_remove";
                        break;
                    }
                    case mqttactic::WRITE1: {
                        semantic += key_var->varType + "_add";
                        break;
                    }
                    case mqttactic::DELIVER: {
                        semantic += "DELIVER";
                        break;
                    }
                    default: {
                        errs() << "[ERROR]: Cannot parse semantic of: " << *(siit->first) << "\n";
                        break;
                    }
                    }

                    SemanticAnchorBBs[&BB]->semanticInsts.insert(std::map<llvm::Instruction*, std::string>::value_type(siit->first, semantic));
                }
                retval = 2;
                return retval;
            }
        }
    }
    return retval;
}

int CFGPass::traverseCFG(Module& M, Function& F, BasicBlock* origin, std::vector<BasicBlock*> paths)
{
    long                            PathCount = 0;
    LoopInfo&                       LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    std::set<BasicBlock*>           NextBBs;
    int                             succCount = 0;
    std::map<std::string, PathType> pt_set;

    paths.push_back(origin);
    completeBBs_kpath.insert(std::map<BasicBlock*, std::map<std::string, PathType>>::value_type(origin, pt_set));
    std::map<BasicBlock*, long>::iterator Bit = completeBBs.find(origin);
    if (Bit != completeBBs.end())
        return Bit->second;

    // errs() << getBBLabel(origin) << "\n";
    Loop* L = LI.getLoopFor(origin);
    for (BasicBlock* Succ : successors(origin))
    {
        succCount++;
        // 发现循环
        if (L != NULL && L->getHeader() == Succ)
        {
            SmallVector<BasicBlock*, 8>                         ExitBlocks;
            SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
            L->getExitBlocks(ExitBlocks);
            L->getExitEdges(ExitEdges);
            // 保存循环边 e.g., %100->%30
            std::map<BasicBlock*, std::set<BasicBlock*>>::iterator eit = completeEdges.find(origin);
            if (eit == completeEdges.end())
            {
                std::set<BasicBlock*> v;
                v.insert(Succ);
                completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(origin, v));
            }
            else
            {
                eit->second.insert(Succ);
            }
            for (std::pair<BasicBlock*, BasicBlock*> ExitEdge : ExitEdges)
            {
                eit = completeEdges.find(ExitEdge.first);
                if (eit == completeEdges.end())
                {
                    std::set<BasicBlock*> v;
                    v.insert(ExitEdge.second);
                    completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(ExitEdge.first, v));
                }
                else
                {
                    eit->second.insert(ExitEdge.second);
                }
            }
            for (llvm::BasicBlock* ExitBlock : ExitBlocks)
            {
                NextBBs.insert(ExitBlock);
            }
        }
        else
        {
            int count = std::count(paths.begin(), paths.end(), Succ);
            if (count > 2)
            {
                continue;
            }
            NextBBs.insert(Succ);
        }
    }
    for (BasicBlock* Nextbb : NextBBs)
    {
        int c = traverseCFG(M, F, Nextbb, paths);
        for (auto ptit = completeBBs_kpath[Nextbb].begin(); ptit != completeBBs_kpath[Nextbb].end(); ptit++)
        {
            std::string pt_str = ptit->first;
            PathType    pt;
            for (auto kbbit = ptit->second.begin(); kbbit != ptit->second.end(); kbbit++)
            {
                pt.push_back(*kbbit);
            }
            // If origin is keyBB, we store the origin in "completeBBs_kpath"
            if (AnchorBBs.find(origin) != AnchorBBs.end())
            {
                pt_str = getBBLabel(origin) + pt_str;
                pt.insert(pt.begin(), origin);
            }

            if (completeBBs_kpath[origin].find(pt_str) == completeBBs_kpath[origin].end())
            {
                completeBBs_kpath[origin].insert(std::map<std::string, PathType>::value_type(pt_str, pt));
            }
        }

        PathCount += c;
        if (c > 0)
        {
            // 保存origin到dest所有边
            std::map<BasicBlock*, std::set<BasicBlock*>>::iterator eit = completeEdges.find(origin);
            if (eit == completeEdges.end())
            {
                std::set<BasicBlock*> v;
                v.insert(Nextbb);
                completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(origin, v));
            }
            else
            {
                eit->second.insert(Nextbb);
            }
        }
    }
    if (succCount == 0 && isRetBBs(origin))
    {
        std::string pt_str = "";
        PathType    pt;
        // If origin is keyBB
        if (AnchorBBs.find(origin) != AnchorBBs.end())
        {
            pt_str = getBBLabel(origin) + pt_str;
            pt.insert(pt.begin(), origin);
        }
        // If origin is not keyBB, pt is empty, which is also one type of PathType
        completeBBs_kpath[origin].insert(std::map<std::string, PathType>::value_type(pt_str, pt));

        completeBBs.insert(std::map<BasicBlock*, long>::value_type(origin, 1));
        return 1;
    }

    completeBBs.insert(std::map<BasicBlock*, long>::value_type(origin, PathCount));

    return PathCount;
}

void CFGPass::constructPathGraph(std::map<llvm::Function*, std::vector<PathType>>& FuncPathTypes)
{
    // Create both head and tail for each function
    for (auto func : FuncPathTypes)
    {
        FuncSliceGraphHT[func.first] = new FuncSliceGraphHeadTail();
        FuncSliceGraphHT[func.first]->head = new SemanticABB();
        FuncSliceGraphHT[func.first]->tail = new SemanticABB();
        FuncSliceGraphHT[func.first]->head->bb = &(func.first->getEntryBlock());
        FuncSliceGraphHT[func.first]->head->isVirtualHead = true;
        FuncSliceGraphHT[func.first]->tail->bb = FuncSliceGraphHT[func.first]->head->bb;
        FuncSliceGraphHT[func.first]->tail->isVirtualTail = true;
    }


    for (auto fptit = FuncPathTypes.begin(); fptit != FuncPathTypes.end(); fptit++)
    {
        // for each path type of this function
        for (auto ptit = fptit->second.begin(); ptit != fptit->second.end(); ptit++)
        {
            SemanticABB* origin = FuncSliceGraphHT[fptit->first]->head;
            // for each anchor BB for this path type
            for (auto bit = (*ptit).begin(); bit != (*ptit).end(); bit++)
            {
                BasicBlock*  bb = *bit;
                SemanticABB* dest = new SemanticABB();
                dest->bb = bb;


                // if there are CALLSITE in this BB, then slice Graph can be: ABB_1 -> "ABB_2"[inst1-inst3] -> Func_1_head -> Func_2_head -> "ABB_2"[inst6-inst8]
                for (Instruction& I : *bb)
                {
                    if (SemanticAnchorBBs[bb]->semanticInsts.find(&I) != SemanticAnchorBBs[bb]->semanticInsts.end())
                    {
                        if (SemanticAnchorBBs[bb]->semanticInsts[&I].find("CALLSITE") != std::string::npos)
                        {
                            if (FuncSliceGraph[fptit->first].find(origin) == FuncSliceGraph[fptit->first].end())
                            {
                                std::map<SemanticABB*, bool> succs;
                                FuncSliceGraph[fptit->first].insert(std::map<SemanticABB*, std::map<SemanticABB*, bool>>::value_type(origin, succs));
                            }
                            FuncSliceGraph[fptit->first][origin][dest] = true;


                            origin = dest;
                            dest = new SemanticABB();
                            dest->bb = bb;
                            dest->callSite = SemanticAnchorBBs[bb]->calledFuncs[&I];
                            if (FuncSliceGraph[fptit->first].find(origin) == FuncSliceGraph[fptit->first].end())
                            {
                                std::map<SemanticABB*, bool> succs;
                                FuncSliceGraph[fptit->first].insert(std::map<SemanticABB*, std::map<SemanticABB*, bool>>::value_type(origin, succs));
                            }
                            FuncSliceGraph[fptit->first][origin][dest] = true;
                            origin = dest;
                            dest = new SemanticABB();
                            dest->bb = bb;
                        }
                        else
                        {
                            dest->semanticInsts.insert(std::map<Instruction*, std::string>::value_type(&I, SemanticAnchorBBs[bb]->semanticInsts[&I]));
                        }
                    }
                }

                if (FuncSliceGraph[fptit->first].find(origin) == FuncSliceGraph[fptit->first].end())
                {
                    std::map<SemanticABB*, bool> succs;
                    FuncSliceGraph[fptit->first].insert(std::map<SemanticABB*, std::map<SemanticABB*, bool>>::value_type(origin, succs));
                }
                FuncSliceGraph[fptit->first][origin][dest] = true;
                origin = dest;
            }
            if (FuncSliceGraph[fptit->first].find(origin) == FuncSliceGraph[fptit->first].end())
            {
                std::map<SemanticABB*, bool> succs;
                FuncSliceGraph[fptit->first].insert(std::map<SemanticABB*, std::map<SemanticABB*, bool>>::value_type(origin, succs));
            }
            FuncSliceGraph[fptit->first][origin][FuncSliceGraphHT[fptit->first]->tail] = true;
        }
    }
}

void CFGPass::combinePathTypes(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticPathType> paths, std::map<Function*, int> loopStatus, std::vector<BasicBlock*> contextPath, std::vector<Function*> callContext)
{
    std::string func = origin->bb->getParent()->getName().str();
    for (auto& p : paths)
    {
        if (p.ptFunc.size() == 0 || (p.ptFunc.size() > 0 && func != p.ptFunc.back()))
        {
            p.ptFunc.push_back(func);
        }
    }
    if (origin->isVirtualHead)
    {
        callContext.push_back(origin->bb->getParent());
    }

    if (origin->callSite == nullptr && origin->isVirtualHead == false && origin->isVirtualTail == false)
    {
        if (KeyBasicBlocks.find(origin->bb) != KeyBasicBlocks.end() && !isFakeAnchorBB(origin->bb, contextPath))
        {
            for (auto& p : paths)
            {
                // store the abb in path
                p.pt.push_back(origin->bb);
                for (auto s : origin->semanticInsts)
                {
                    std::string raw_s = s.second.substr(s.second.find_last_of("===") + 1);

                    if (p.ptSemanticVec.empty() || (p.ptSemanticVec.size() > 0 && p.ptSemanticVec.back() != raw_s))
                    {
                        p.ptSemanticVec.push_back(raw_s);
                        p.ptSemantic += "->" + raw_s;
                    }
                }
            }
            contextPath.push_back(origin->bb);
        }
    }

    // step into another function
    if (origin->callSite)
    {
        Function* calledFunc = origin->callSite;

        if (loopStatus.find(calledFunc) == loopStatus.end())
            loopStatus.insert(std::map<Function*, int>::value_type(calledFunc, 0));
        loopStatus[calledFunc] += 1;
        if (loopStatus[calledFunc] == 1)
        {
            if (completeFunc_kpath.find(calledFunc) == completeFunc_kpath.end())
            {
                std::vector<SemanticPathType> calledFuncPaths;
                SemanticPathType              empty_spt;
                calledFuncPaths.push_back(empty_spt);
                combinePathTypes(M, *calledFunc, FuncSliceGraphHT[calledFunc]->head, calledFuncPaths, loopStatus, contextPath, callContext);
            }
            std::vector<SemanticPathType> paths_tmp(paths);
            paths.clear();
            for (auto spt : completeFunc_kpath[calledFunc])
            {
                if (spt.second->ptSemanticVec.size() == 0)
                {
                    paths.insert(paths.end(), paths_tmp.begin(), paths_tmp.end());
                    continue;
                }
                for (auto current_path : paths_tmp)
                {
                    SemanticPathType p(current_path);
                    p.pt.insert(p.pt.end(), spt.second->pt.begin(), spt.second->pt.end());
                    p.ptFunc.insert(p.ptFunc.end(), spt.second->ptFunc.begin(), spt.second->ptFunc.end());
                    if (p.ptSemanticVec.empty() || (p.ptSemanticVec.size() > 0 && p.ptSemanticVec.back() != spt.second->ptSemanticVec.front()))
                    {
                        p.ptSemanticVec.insert(p.ptSemanticVec.end(), spt.second->ptSemanticVec.begin(), spt.second->ptSemanticVec.end());
                        p.ptSemantic += spt.second->ptSemantic;
                    }
                    else
                    {
                        if (spt.second->ptSemanticVec.size() != 1)
                        {
                            p.ptSemanticVec.insert(p.ptSemanticVec.end(), spt.second->ptSemanticVec.begin() + 1, spt.second->ptSemanticVec.end());
                            for (auto psit = spt.second->ptSemanticVec.begin() + 1; psit != spt.second->ptSemanticVec.end(); psit++)
                                p.ptSemantic += "->" + *psit;
                        }
                    }
                    paths.push_back(p);
                }
            }

            loopStatus[calledFunc] -= 1;
        }
        else
        {
            errs() << "[ERROR]: Loop in the path, loopStatus = " << loopStatus[calledFunc] << "\n";
            loopStatus[calledFunc] -= 1;
        }
    }

    // When encounter the virtual tail Node of a function, it means we need to return to the last CALLSITE
    else if (origin->isVirtualTail)
    {
        if (completeFunc_kpath.find(&F) == completeFunc_kpath.end())
            completeFunc_kpath.insert(std::map<Function*, std::map<std::string, CFGPass::SemanticPathType*>>::value_type(&F, std::map<std::string, CFGPass::SemanticPathType*>()));

        for (auto p : paths)
        {
            if (completeFunc_kpath[&F].find(p.ptSemantic) == completeFunc_kpath[&F].end())
            {
                completeFunc_kpath[&F].insert(std::map<std::string, CFGPass::SemanticPathType*>::value_type(p.ptSemantic, new SemanticPathType(p)));
            }
        }
        callContext.pop_back();
    }


    for (auto succ : FuncSliceGraph[&F][origin])
    {
        if (succ.second != true)
            continue;

        combinePathTypes(M, F, succ.first, paths, loopStatus, contextPath, callContext);
    }
}


void CFGPass::printFuncSliceGraph(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticABB*> path)
{
    path.push_back(origin);
    if (origin->isVirtualTail)
    {
        for (auto s : path)
        {
            if (s->isVirtualHead)
                errs() << " -> "
                       << "HEAD";
            else if (s->isVirtualTail)
                errs() << " -> "
                       << "TAIL";
            else if (s->callSite)
            {

                errs() << " -> "
                       << "CALLSITE (" << s->callSite->getName().str() << ")";
            }
            else
            {
                for (auto SI : s->semanticInsts)
                {
                    errs() << " -> " << SI.second;
                }
            }
        }
        errs() << "\n";
        return;
    }
    for (auto succ : FuncSliceGraph[&F][origin])
    {
        if (succ.second)
            printFuncSliceGraph(M, F, succ.first, path);
    }
}


bool CFGPass::isFakeAnchorBB(BasicBlock* bb, std::vector<BasicBlock*> contextPath)
{
    // use the context of KBB to filter the Anchor BBs
    bool                               fakeAnchorBB = true;
    std::vector<mqttactic::KBBContext> contexts;
    for (auto key_var : var_analyzer->key_variables)
    {
        if (var_analyzer->SemanticKeyBasicBlocks[key_var].find(bb) != var_analyzer->SemanticKeyBasicBlocks[key_var].end())
        {
            // // [TODO-x]: 更新Msg的context过滤
            // if (key_var->varType == "Msg")
            // {
            //     return false;
            // }
            if (key_var->varType == "Msg")
            {
                return false;
                // bool flag = true;
                // dbgs() << "callcontext :";
                // for (auto f : callContext)
                // {
                //     dbgs() << f->getName().str() << "->";
                // }
                // dbgs() << "\n";
                // for (auto ctxs : var_analyzer->SemanticKeyBasicBlocks[key_var][bb]->contexts)
                // {

                //     std::set<const llvm::Function*> funcs;
                //     for (auto bb : ctxs)
                //     {
                //         funcs.insert(bb->getParent());
                //     }
                //     for (auto f : callContext)
                //     {
                //         if (funcs.find(f) == funcs.end())
                //             continue;
                //     }
                //     flag = false;
                //     break;
                // }
                // return flag;
            }
            contexts.insert(contexts.end(), var_analyzer->SemanticKeyBasicBlocks[key_var][bb]->contexts.begin(), var_analyzer->SemanticKeyBasicBlocks[key_var][bb]->contexts.end());
        }
    }

    // 如果当前的真实contextPath不包含ctx[0](每一个KBB保存多个context, 只有满足这些context, 才是KBB), 认为是fake的
    for (auto ctx : contexts)
    {
        if (ctx.size() == 0)
        {
            fakeAnchorBB = false;
            break;
        }
        else
        {

            BasicBlock* first_bb = const_cast<BasicBlock*>(ctx[0]);
            if (std::find(contextPath.begin(), contextPath.end(), first_bb) != contextPath.end())
            {
                fakeAnchorBB = false;
                break;
            }
        }
    }
    if (contexts.empty())
        fakeAnchorBB = false;
    return fakeAnchorBB;
}

bool CFGPass::clearALLFunctions()
{
    for (std::map<std::string, short>::iterator it = CFGPass::ALLFunctions.begin(); it != CFGPass::ALLFunctions.end(); it++)
    {
        it->second = 0;
    }
    return true;
}


void CFGPass::getAllRelatedFuncs(Module& M, Function& F)
{
    std::set<Instruction*>           insts;
    std::set<Instruction*>::iterator it;
    int                              retval = 1;

    HFuncs.insert(&F);
    for (BasicBlock& BB : F)
    {
        for (Instruction& I : BB)
        {
            insts.insert(&I);
        }
    }
    for (it = insts.begin(); it != insts.end(); it++)
    {
        llvm::Instruction* inst = *it;
        unsigned int       opcode = inst->getOpcode();

        switch (opcode)
        {
        case Instruction::Call: {
            CallInst*                              call = static_cast<CallInst*>(inst);
            std::string                            calledFuncName = "";
            int                                    rt;
            bool                                   isKeyFunc = false;
            std::map<std::string, short>::iterator Fit;

            if (call->isIndirectCall() || call->getCalledFunction() == NULL)
            {
                Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
            Fit = ALLFunctions.find(calledFuncName);
            Function& calledFunc = *M.getFunction(calledFuncName);

            // 禁止进入系统函数(只关注broker中声明的函数)
            if (Fit != ALLFunctions.end() && calledFuncName != "log__printf" && HFuncs.find(&calledFunc) == HFuncs.end())
            {
                getAllRelatedFuncs(M, calledFunc);
            }

            break;
        }
        case Instruction::Invoke: {
            InvokeInst*                            call = static_cast<InvokeInst*>(inst);
            std::string                            calledFuncName = "";
            int                                    rt;
            bool                                   isKeyFunc = false;
            std::map<std::string, short>::iterator Fit;
            if (call->isIndirectCall() || call->getCalledFunction() == NULL)
            {
                Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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

            Fit = ALLFunctions.find(calledFuncName);
            Function& calledFunc = *M.getFunction(calledFuncName);
            // 禁止进入系统函数(只关注broker中声明的函数)
            if (Fit != ALLFunctions.end() && calledFuncName != "log__printf" && HFuncs.find(&calledFunc) == HFuncs.end())
            {
                getAllRelatedFuncs(M, calledFunc);
            }

            break;
        }

        default:
            break;
        }
    }
}


std::string CFGPass::getBBLabel(const BasicBlock* Node)
{
    if (!Node->getName().empty())
        return "%" + Node->getName().str();

    std::string        Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
};

int CFGPass::getBBLabelIdx(const Function* func, const BasicBlock* Node)
{
    int idx = 0;
    for (auto& iter : func->getBasicBlockList())
    {
        if (Node == &iter)
        {
            break;
        }
        idx++;
    }
    return idx;
}

bool CFGPass::traverseFuncToEnd(Module& M, Function& F, BasicBlock* end, bool foundEnd, std::vector<keyBBPath> path, std::vector<std::vector<keyBBPath>>& endPath, std::vector<std::vector<keyBBPath>>& results)
{
    bool found_end = foundEnd;
    for (BasicBlock& BB : F)
    {
        int Bindex;
        if (AnchorBBs.find(&BB) != AnchorBBs.end())
        {
            struct keyBBPath k;
            k.bb = &BB;
            k.mustBePassed = false;
            k.func = F.getName().str();
            path.push_back(k);
            Bindex = path.size() - 1;
        }
        if (&BB == end)
        {
            bool repeat = false;
            for (std::vector<std::vector<keyBBPath>>::iterator it = endPath.begin(); it != endPath.end(); it++)
            {
                bool flag = false;
                if (path.size() != (*it).size())
                    continue;
                for (int i = 0; i < path.size(); i++)
                {
                    if (path[i].bb == (*it)[i].bb)
                        continue;
                    else
                    {
                        flag = true;
                        break;
                    }
                }
                if (flag)
                {
                    continue;
                }
                else
                {
                    repeat = true;
                    break;
                }
            }
            if (!repeat)
            {
                endPath.push_back(path);
                found_end = true;
            }
            // for (std::vector<keyBBPath>::iterator it = path.begin(); it
            // != path.end(); it++)
            // {
            //     errs() << (*it).bb->getParent()->getName().str() << ":"
            //     << getBBLabel((*it).bb) << "\n";
            // }
            // errs() << '\n';
        }
        for (Instruction& I : BB)
        {
            llvm::Instruction* inst = &I;
            unsigned int       opcode = inst->getOpcode();
            switch (opcode)
            {
            case Instruction::Call: {
                CallInst*   call = static_cast<CallInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (!found_end && keyFuncs.find(calledFuncName) != keyFuncs.end() && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    found_end = traverseFuncToEnd(M, *(call->getCalledFunction()), end, found_end, path, endPath, results);
                    if (found_end)
                    {
                        path.clear();
                        for (std::vector<keyBBPath>::iterator it = results[results.end() - results.begin() - 1].begin(); it != results[results.end() - results.begin() - 1].end(); it++)
                        {
                            path.push_back((*it));
                        }
                        results.pop_back();
                    }
                }
                break;
            }
            case Instruction::Invoke: {
                InvokeInst* call = static_cast<InvokeInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (!found_end && keyFuncs.find(calledFuncName) != keyFuncs.end() && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    found_end = traverseFuncToEnd(M, *(call->getCalledFunction()), end, found_end, path, endPath, results);
                    if (found_end)
                    {
                        path.clear();
                        for (std::vector<keyBBPath>::iterator it = results[results.end() - results.begin() - 1].begin(); it != results[results.end() - results.begin() - 1].end(); it++)
                        {
                            path.push_back((*it));
                        }
                        results.pop_back();
                    }
                }
                break;
            }
            case Instruction::Ret: {
                if (path[path.end() - path.begin() - 1].bb != &BB)
                {
                    struct keyBBPath k;
                    k.bb = nullptr;
                    k.mustBePassed = false;
                    k.func = F.getName().str();
                    path.push_back(k);
                }
                else
                {
                    path[path.end() - path.begin() - 1].bb = nullptr;
                    path[path.end() - path.begin() - 1].mustBePassed = true;
                }
                if (F.getName().str() == handlerName && found_end)
                {
                    bool exist = false;
                    for (std::vector<std::vector<keyBBPath>>::iterator rit = results.begin(); rit != results.end(); rit++)
                    {
                        if ((*rit).size() == path.size())
                        {
                            bool sameflag = true;
                            for (int i = 0; i < path.size(); i++)
                            {
                                if ((*rit)[i].bb == path[i].bb)
                                    continue;
                                else
                                {
                                    sameflag = false;
                                    break;
                                }
                            }
                            if (sameflag)
                            {
                                exist = true;
                                break;
                            }
                        }
                    }
                    if (!exist)
                        results.push_back(path);
                }
                else if (found_end)
                {
                    results.push_back(path);
                }
                return found_end;
            }
            default:
                break;
            }
        }
    }
    return found_end;
}

void CFGPass::traverseFuncToReturn(Module& M, Function& F, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS)
{
    for (BasicBlock& BB : F)
    {
        if (AnchorBBs.find(&BB) != AnchorBBs.end())
        {
            continue;
        }
        for (Instruction& I : BB)
        {
            llvm::Instruction* inst = &I;
            unsigned int       opcode = inst->getOpcode();
            switch (opcode)
            {
            case Instruction::Call: {
                CallInst*   call = static_cast<CallInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (calledFuncName.find("send__real_publish") != std::string::npos && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    AnchorBBs.insert(&BB);
                    if (SKBBS.find(&BB) == SKBBS.end())
                    {
                        mqttactic::SemanticKBB* sbb = new mqttactic::SemanticKBB();
                        sbb->bb = &BB;
                        sbb->values.push_back(inst);
                        sbb->semantics = mqttactic::DELIVER;
                        sbb->semantic_inst.insert(std::map<llvm::Instruction*, int>::value_type(const_cast<llvm::Instruction*>(inst), mqttactic::DELIVER));

                        SKBBS.insert(std::pair<const llvm::BasicBlock*, mqttactic::SemanticKBB*>(&BB, sbb));
                    }
                }
                break;
            }
            case Instruction::Invoke: {
                InvokeInst* call = static_cast<InvokeInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (calledFuncName.find("send__real_publish") != std::string::npos && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    AnchorBBs.insert(&BB);
                    if (SKBBS.find(&BB) == SKBBS.end())
                    {
                        mqttactic::SemanticKBB* sbb = new mqttactic::SemanticKBB();
                        sbb->bb = &BB;
                        sbb->values.push_back(inst);
                        sbb->semantics = mqttactic::DELIVER;
                        sbb->semantic_inst.insert(std::map<llvm::Instruction*, int>::value_type(const_cast<llvm::Instruction*>(inst), mqttactic::DELIVER));

                        SKBBS.insert(std::pair<const llvm::BasicBlock*, mqttactic::SemanticKBB*>(&BB, sbb));
                    }
                }
                break;
            }
            default:
                break;
            }
        }
    }
}

void CFGPass::traverseFuncToReturnWithoutCall(Module& M, Function& F, std::vector<keyBBPathWithoutCall>& result)
{
    for (BasicBlock& BB : F)
    {
        if (AnchorBBs.find(&BB) != AnchorBBs.end())
        {
            struct keyBBPathWithoutCall k;
            std::set<std::string>       F;
            k.bb = &BB;
            k.calledFuncs = F;
            result.push_back(k);
        }
        for (Instruction& I : BB)
        {
            llvm::Instruction* inst = &I;
            unsigned int       opcode = inst->getOpcode();
            switch (opcode)
            {
            case Instruction::Call: {
                CallInst*   call = static_cast<CallInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (keyFuncs.find(calledFuncName) != keyFuncs.end() && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    result[result.end() - result.begin() - 1].calledFuncs.insert(calledFuncName);
                }
                break;
            }
            case Instruction::Invoke: {
                InvokeInst* call = static_cast<InvokeInst*>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || call->getCalledFunction() == NULL)
                {
                    Function*          ptrFunc = dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCastsAndAliases());
                    const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
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
                if (keyFuncs.find(calledFuncName) != keyFuncs.end() && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    result[result.end() - result.begin() - 1].calledFuncs.insert(calledFuncName);
                }
                break;
            }
            case Instruction::Ret: {
                // 遇到返回，则插入一个null basicblock，代表返回
                struct keyBBPathWithoutCall k;
                std::set<std::string>       F;
                k.bb = nullptr;
                k.calledFuncs = F;
                result.push_back(k);
                // if (result.empty() || result[result.end() -
                // result.begin() - 1].bb
                // != &BB)
                // {
                //     struct keyBBPathWithoutCall k;
                //     std::set<std::string> F;
                //     k.bb = nullptr;
                //     k.calledFuncs = F;
                //     result.push_back(k);
                // }
                // else
                // {
                //     result[result.end() - result.begin() - 1].bb =
                //     nullptr;
                // }
                return;
            }
            default:
                break;
            }
        }
    }
}

long CFGPass::traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths)
{
    paths.push_back(origin);
    std::map<BasicBlock*, long>::iterator Bit = completeBBs.find(origin);
    if (Bit != completeBBs.end())
        return Bit->second;
    if (origin == dest)
    {
        if (Bit == completeBBs.end())
            completeBBs.insert(std::map<BasicBlock*, long>::value_type(origin, 1));
        return 1;
    }
    // 在途中发现其他变量
    else if (paths.size() > 1 && AnchorBBs.find(origin) != AnchorBBs.end())
        return 0;

    long                  PathCount = 0;
    LoopInfo&             LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    std::set<BasicBlock*> NextBBs;
    int                   succCount = 0;
    // errs() << getBBLabel(origin) << "\n";
    Loop* L = LI.getLoopFor(origin);
    for (BasicBlock* Succ : successors(origin))
    {
        succCount++;
        // 发现循环
        if (L != NULL && L->getHeader() == Succ)
        {
            SmallVector<BasicBlock*, 8>                         ExitBlocks;
            SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
            L->getExitBlocks(ExitBlocks);
            L->getExitEdges(ExitEdges);
            // 保存循环边 e.g. %100->%30
            std::map<BasicBlock*, std::set<BasicBlock*>>::iterator eit = completeEdges.find(origin);
            if (eit == completeEdges.end())
            {
                std::set<BasicBlock*> v;
                v.insert(Succ);
                completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(origin, v));
            }
            else
            {
                eit->second.insert(Succ);
            }
            for (std::pair<BasicBlock*, BasicBlock*> ExitEdge : ExitEdges)
            {
                eit = completeEdges.find(ExitEdge.first);
                if (eit == completeEdges.end())
                {
                    std::set<BasicBlock*> v;
                    v.insert(ExitEdge.second);
                    completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(ExitEdge.first, v));
                }
                else
                {
                    eit->second.insert(ExitEdge.second);
                }
            }
            for (llvm::BasicBlock* ExitBlock : ExitBlocks)
            {
                NextBBs.insert(ExitBlock);
            }
        }
        else
        {
            int count = std::count(paths.begin(), paths.end(),
                                   Succ);  // 查找对象类型时，需要该类提供重载==函数
            if (count > 2)
            {
                continue;
            }
            NextBBs.insert(Succ);
        }
    }
    for (BasicBlock* Nextbb : NextBBs)
    {
        int c = traversePath(M, F, Nextbb, dest, paths);
        PathCount += c;
        if (c > 0)
        {
            // 保存origin到dest所有边
            std::map<BasicBlock*, std::set<BasicBlock*>>::iterator eit = completeEdges.find(origin);
            if (eit == completeEdges.end())
            {
                std::set<BasicBlock*> v;
                v.insert(Nextbb);
                completeEdges.insert(std::map<BasicBlock*, std::set<BasicBlock*>>::value_type(origin, v));
            }
            else
            {
                eit->second.insert(Nextbb);
            }
        }
    }
    if (dest == nullptr && succCount == 0 && isRetBBs(origin))
    {
        completeBBs.insert(std::map<BasicBlock*, long>::value_type(origin, 1));
        return 1;
    }

    completeBBs.insert(std::map<BasicBlock*, long>::value_type(origin, PathCount));
    return PathCount;
}

long CFGPass::traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths, std::vector<std::vector<BasicBlock*>>& results)
{
    if (results.size() >= 10)
    {
        return 0;
    }
    paths.push_back(origin);
    if (origin == dest)
    {
        results.push_back(paths);
        return 1;
    }
    // 在途中发现其他变量
    else if (paths.size() > 1 && AnchorBBs.find(origin) != AnchorBBs.end())
        return 0;

    long                  PathCount = 0;
    LoopInfo&             LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    std::set<BasicBlock*> NextBBs;
    int                   succCount = 0;
    Loop*                 L = LI.getLoopFor(origin);
    for (BasicBlock* Succ : successors(origin))
    {
        succCount++;
        // 发现循环
        if (L != NULL && L->getHeader() == Succ)
        {
            SmallVector<BasicBlock*, 8> ExitBlocks;
            L->getExitBlocks(ExitBlocks);
            for (llvm::BasicBlock* ExitBlock : ExitBlocks)
            {
                NextBBs.insert(ExitBlock);
            }
        }
        else
            NextBBs.insert(Succ);
    }
    for (BasicBlock* Nextbb : NextBBs)
    {
        PathCount += traversePath(M, F, Nextbb, dest, paths, results);
    }
    if (dest == nullptr && succCount == 0 && isRetBBs(origin))
    {
        results.push_back(paths);
        return 1;
    }

    return PathCount;
}

bool CFGPass::isRetBBs(BasicBlock* bb)
{
    BasicBlock& BB = *bb;
    bool        ret = false;
    for (Instruction& I : BB)
    {
        unsigned int opcode = I.getOpcode();

        switch (opcode)
        {
        case Instruction::Ret: {
            ret = true;
            break;
        }
        }
    }
    return ret;
}

bool CFGPass::isKeyBBs(std::string str)
{
    std::vector<std::string> key_var_op = {"subs_read", "subs_write", "RetainedMsg_read", "RetainedMsg_write", "WillMsg_read", "WillMsg_write", "msg_read", "msg_write"};

    for (std::string op : key_var_op)
    {
        if (op.find(str) != std::string::npos)
        {
            return true;
        }
    }

    return false;
}

std::string CFGPass::replaceKeyBBsOrEndName(std::string str)
{
    std::vector<std::string> key_var_op = {"subs_read", "subs_write", "RetainedMsg_read", "RetainedMsg_write", "WillMsg_read", "WillMsg_write", "msg_read", "msg_write"};

    for (std::string op : key_var_op)
    {
        if (op.find(str) != std::string::npos)
        {
            return op;
        }
    }
    return "ERROR";
    // if (send__pubcomp.find(str) != std::string::npos)
    //     return "send__pubcomp";
    // else if (send__puback.find(str) != std::string::npos)
    //     return "send__puback";
    // else if (send__pubrec.find(str) != std::string::npos)
    //     return "send__pubrec";
    // else if (send__connack.find(str) != std::string::npos)
    //     return "send__connack";
    // else if (send__suback.find(str) != std::string::npos)
    //     return "send__suback";
    // else if (send__unsuback.find(str) != std::string::npos)
    //     return "send__unsuback";
    // else if (acl_revoke.find(str) != std::string::npos)
    //     return "acl_revoke";
    // else if (acl_check.find(str) != std::string::npos)
    //     return "acl_check";
    // else if (deliver_to_subscribers.find(str) != std::string::npos)
    //     return "deliver_to_subscribers";
    // else if (deliver.find(str) != std::string::npos)
    //     return "deliver";
    // else if (sub_remove.find(str) != std::string::npos)
    //     return "sub_remove";
    // else if (sub_add.find(str) != std::string::npos)
    //     return "sub_add";
    // else
    //     return "ERROR";
}

int CFGPass::endOfHandler(CallBase* call)
{
    return 0;
}


char CFGPass::ID = 0;

// Register for opt
static RegisterPass<CFGPass> X("CFG", "CFGPass");

// Register for clang
static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible, [](const PassManagerBuilder& Builder, legacy::PassManagerBase& PM) { PM.add(new CFGPass()); });
