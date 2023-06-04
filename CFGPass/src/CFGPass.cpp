/*
clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o CFGPass.so
opt -load ./CFGPass.so -CFG ./mosquitto.bc -o /dev/null 2>
handle__publish.output

：
1.  "./ALLFunctions"
*/

#include "../../Include/VarAnalysis.h"
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


class CFGPass : public ModulePass
{
public:
    typedef std::vector<BasicBlock*> PathType;
    // handlerendBB""keyBB(BB)
    struct keyBBPath
    {
        BasicBlock* bb;
        std::string func;
        // BB
        bool mustBePassed;
    };
    // ，BBreturnkeyBB，Call
    struct keyBBPathWithoutCall
    {
        BasicBlock* bb;
        // BB
        std::set<std::string> calledFuncs;
    };

    struct SemanticABB
    {
        BasicBlock*     bb;
        bool            isVirtualHead = false;
        bool            isVirtualTail = false;
        llvm::Function* callSite = nullptr;
        // BB
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
        PathType                 pt;
    };

    static char ID;
    // variable analyzer
    mqttactic::VarAnalysis* var_analyzer;
    // first: ; second: 0/1/2()/3ACL_CHECK
    std::map<std::string, short>       ALLFunctions;
    std::map<std::string, BasicBlock*> ALLBasicBlocks;

    std::set<const llvm::BasicBlock*> KeyBasicBlocks;
    // AnchorBB: 1. KBB or callsites that will flow to KBB; 2. ACL_CHECK
    std::set<BasicBlock*>               AnchorBBs;
    std::map<BasicBlock*, SemanticABB*> SemanticAnchorBBs;

    // send__**ackBB
    std::set<BasicBlock*> endBBs;
    // 
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

    std::map<Function*, std::map<std::string, SemanticPathType*>> completeFunc_kpath;
    // BB
    std::map<BasicBlock*, std::set<BasicBlock*>> completeEdges;
    // 0: handlerend, 1:return 2: keyFuncs
    int switchEnd = 0;

    std::string handlerName = mqttactic::handle__pubrel;

    std::string outputDir = "../OUTPUT";

    int count = 0;

    /********************************
                Functions
    ********************************/

    void identifyKeyBasicBlock(Module& M, Function& F);
    // ，KBB
    int traverseCallGraph(Module& M, Function& F);
    // Traverse the handler function
    int traverseCFG(Module& M, Function& F, BasicBlock* origin, std::vector<BasicBlock*> paths);
    // Transform the FuncPathTypes list to a graph
    void constructPathGraph(std::map<llvm::Function*, std::vector<PathType>>& FuncPathTypes);
    void printFuncSliceGraph(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticABB*> path);
    /* Use PathGraph to combine all possible Handler PATHTYPES combinations
     */
    void combinePathTypes(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticPathType> path, std::map<Function*, int> loopStatus, std::vector<BasicBlock*> contextPath);

    // use the context of KBB to filter the Anchor BBs
    bool isFakeAnchorBB(BasicBlock* bb, std::vector<BasicBlock*> contextPath);
    // ALLFunctionssecond
    bool clearALLFunctions();

    // BBlabel
    std::string getBBLabel(const BasicBlock* Node);
    int         getBBLabelIdx(const Function* func, const BasicBlock* Node);
    // KBB
    void readKBBFile(std::string file);

    // ，endBB，keyBBs
    bool traverseFuncToEnd(Module& M, Function& F, BasicBlock* end, bool foundEnd, std::vector<keyBBPath> path, std::vector<std::vector<keyBBPath>>& endPath, std::vector<std::vector<keyBBPath>>& results);
    // ，return，keyBBs()
    void traverseFuncToReturn(Module& M, Function& F, std::vector<keyBBPath> path, std::vector<keyBBPath>& result);
    void traverseFuncToReturnWithoutCall(Module& M, Function& F, std::vector<keyBBPathWithoutCall>& result);

    // origindest，
    long traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths);
    // 
    long traversePath(Module& M, Function& F, BasicBlock* origin, BasicBlock* dest, std::vector<BasicBlock*> paths, std::vector<std::vector<BasicBlock*>>& results);

    bool isRetBBs(BasicBlock* bb);
    int  endOfHandler(CallBase* call);
    // (UNUSE)
    bool        isKeyBBs(std::string str);
    std::string replaceKeyBBsOrEndName(std::string str);

    CFGPass() : ModulePass(ID)
    {
        // 
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
        // BB
        std::map<std::string, std::vector<BasicBlock*>> keyVecs;
        // ，Nodes: entryBlock、return(nullptr)、path_Count
        std::map<BasicBlock*, std::map<BasicBlock*, long>> pathMap;

        for (Module::iterator mi = M.begin(); mi != M.end(); ++mi)
        {
            Function& f = *mi;
            for (auto& bb : f)
            {
                std::string bb_str = bb.getParent()->getName().str() + ":" + getBBLabel(&bb);
                ALLBasicBlocks.insert(std::pair<std::string, llvm::BasicBlock*>(bb_str, &bb));
            }
        }

        keyFuncs.insert(F.getName().str());
        errs() << "[INFO]: Analyzing Function: " << F.getName().str() << "\n";

        identifyKeyBasicBlock(M, F);
        int cou = 0;
        for (auto key_var : var_analyzer->key_variables)
        {
            cou += var_analyzer->SemanticKeyBasicBlocks[key_var].size();
        }
        errs() << "[INFO]: Pointer Analysis found " << cou << " Semantic Key Basic Blocks\n";

        traverseCallGraph(M, F);


        errs() << "[INFO]: Anchor Basic Blocks: " << AnchorBBs.size() << "\n\n\n\n";

        dbgs() << "\n\n/**********************/\n[DBG]: Semantic AnchorBB: \n/**********************/\n";
        for (auto sabbit = SemanticAnchorBBs.begin(); sabbit != SemanticAnchorBBs.end(); sabbit++)
        {
            dbgs() << "=====================================================\n";
            dbgs() << *(sabbit->first) << "\n\n";
            for (auto siit = sabbit->second->semanticInsts.begin(); siit != sabbit->second->semanticInsts.end(); siit++)
                dbgs() << *(siit->first) << ":" << siit->second << "\n";
        }

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


        // for (auto fptit = FuncPathTypes.begin(); fptit != FuncPathTypes.end(); fptit++)
        // {
        //     dbgs() << fptit->first->getName().str() << ": \n";
        //     for (auto ptit = fptit->second.begin(); ptit != fptit->second.end(); ptit++)
        //     {
        //         dbgs() << "PT: ";
        //         for (auto bit = (*ptit).begin(); bit != (*ptit).end(); bit++)
        //         {
        //             dbgs() << getBBLabel(*bit) << " -> ";
        //         }
        //         dbgs() << "\n";
        //     }
        // }

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
        spts.push_back(empty_spt);
        combinePathTypes(M, F, FuncSliceGraphHT[&F]->head, spts, loopStatus, contextPath);

        dbgs() << "\n\n/**********************/\n[DBG]: PATHTYPES (" << completeFunc_kpath[&F].size() << "): \n/**********************/\n";
        for (auto spt : completeFunc_kpath[&F])
        {
            dbgs() << spt.first << "\n";
        }

        assert(1 == 2);

        {
            // keyBBs
            for (std::set<BasicBlock*>::iterator it = AnchorBBs.begin(); it != AnchorBBs.end(); it++)
            {
                std::string                                               funcName = (*it)->getParent()->getName().str();
                int                                                       label = getBBLabelIdx((*it)->getParent(), *it);
                std::map<std::string, std::vector<BasicBlock*>>::iterator keyVecit = keyVecs.find(funcName);

                if (keyVecit == keyVecs.end())
                {
                    std::vector<BasicBlock*> v;
                    v.push_back(*it);
                    keyVecs.insert(std::map<std::string, std::vector<BasicBlock*>>::value_type(funcName, v));
                }
                else
                {
                    for (int i = 0; i < keyVecit->second.size(); i++)
                    {
                        int l = getBBLabelIdx((*it)->getParent(), keyVecit->second[i]);
                        if (label < l)
                        {
                            keyVecit->second.insert(keyVecit->second.begin() + i, *it);
                            break;
                        }
                        else if (i == keyVecit->second.size() - 1)
                        {
                            keyVecit->second.push_back(*it);
                            break;
                        }
                    }
                }
            }

            if (keyVecs.empty())
            {
                std::vector<BasicBlock*> v;
                keyVecs.insert(std::map<std::string, std::vector<BasicBlock*>>::value_type(F.getName().str(), v));
            }
            // 
            for (std::map<std::string, std::vector<BasicBlock*>>::iterator it = keyVecs.begin(); it != keyVecs.end(); it++)
            {
                long p = 0;
                errs() << "\n" << it->first << ":\n";
                //  entryBlockkeyBB
                for (int i = 0; i < it->second.size(); i++)
                {
                    p = traversePath(M, *M.getFunction(it->first), &(M.getFunction(it->first)->getEntryBlock()), (it->second)[i], paths);
                    if (pathMap.find(&(M.getFunction(it->first)->getEntryBlock())) == pathMap.end())
                    {
                        std::map<BasicBlock*, long> dest;
                        dest.insert(std::map<BasicBlock*, long>::value_type((it->second)[i], p));
                        pathMap.insert(std::map<BasicBlock*, std::map<BasicBlock*, long>>::value_type(&(M.getFunction(it->first)->getEntryBlock()), dest));
                    }
                    else
                    {
                        pathMap[&(M.getFunction(it->first)->getEntryBlock())].insert(std::map<BasicBlock*, long>::value_type((it->second)[i], p));
                    }
                    errs() << it->first << " ---> " << getBBLabel((it->second)[i]) << ":";
                    errs() << p << "\n";
                    // ，origin->destBBs
                    if (p != 0)
                    {
                        std::error_code err;
                        std::string     fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel(&(M.getFunction(it->first)->getEntryBlock())) + "-" + getBBLabel((it->second)[i]);
                        raw_fd_ostream  fd(fileName, err);
                        for (std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                        {
                            for (std::set<llvm::BasicBlock*>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                                fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                        }
                    }
                    completeBBs.clear();
                    completeEdges.clear();
                }
                //  entryBlockreturn
                p = traversePath(M, *M.getFunction(it->first), &(M.getFunction(it->first)->getEntryBlock()), nullptr, paths);
                if (pathMap.find(&(M.getFunction(it->first)->getEntryBlock())) == pathMap.end())
                {
                    std::map<BasicBlock*, long> dest;
                    dest.insert(std::map<BasicBlock*, long>::value_type(nullptr, p));
                    pathMap.insert(std::map<BasicBlock*, std::map<BasicBlock*, long>>::value_type(&(M.getFunction(it->first)->getEntryBlock()), dest));
                }
                else
                {
                    pathMap[&(M.getFunction(it->first)->getEntryBlock())].insert(std::map<BasicBlock*, long>::value_type(nullptr, p));
                }
                errs() << it->first << " ---> "
                       << "RETURN"
                       << ":";
                errs() << p << "\n";
                if (p != 0)
                {
                    std::error_code err;
                    std::string     fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel(&(M.getFunction(it->first)->getEntryBlock())) + "-" + "RETURN";
                    raw_fd_ostream  fd(fileName, err);
                    for (std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                    {
                        for (std::set<llvm::BasicBlock*>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                            fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                    }
                }
                completeBBs.clear();
                completeEdges.clear();
                // keyBBreturn
                for (int i = 0; i < it->second.size(); i++)
                {
                    p = traversePath(M, *M.getFunction(it->first), (it->second)[i], nullptr, paths);
                    if (pathMap.find((it->second)[i]) == pathMap.end())
                    {
                        std::map<BasicBlock*, long> dest;
                        dest.insert(std::map<BasicBlock*, long>::value_type(nullptr, p));
                        pathMap.insert(std::map<BasicBlock*, std::map<BasicBlock*, long>>::value_type((it->second)[i], dest));
                    }
                    else
                    {
                        pathMap[(it->second)[i]].insert(std::map<BasicBlock*, long>::value_type(nullptr, p));
                    }
                    errs() << getBBLabel((it->second)[i]) << " ---> "
                           << "RETURN"
                           << ":";
                    errs() << p << "\n";
                    if (p != 0)
                    {
                        std::error_code err;
                        std::string     fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel((it->second)[i]) + "-" + "RETURN";
                        raw_fd_ostream  fd(fileName, err);
                        for (std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                        {
                            for (std::set<llvm::BasicBlock*>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                                fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                        }
                    }
                    completeBBs.clear();
                    completeEdges.clear();
                }
                for (int i = 0; i < it->second.size(); i++)
                {
                    for (int j = i + 1; j < it->second.size(); j++)
                    {
                        p = traversePath(M, *M.getFunction(it->first), (it->second)[i], (it->second)[j], paths);
                        if (pathMap.find((it->second)[i]) == pathMap.end())
                        {
                            std::map<BasicBlock*, long> dest;
                            dest.insert(std::map<BasicBlock*, long>::value_type((it->second)[j], p));
                            pathMap.insert(std::map<BasicBlock*, std::map<BasicBlock*, long>>::value_type((it->second)[i], dest));
                        }
                        else
                        {
                            pathMap[(it->second)[i]].insert(std::map<BasicBlock*, long>::value_type((it->second)[j], p));
                        }
                        errs() << getBBLabel((it->second)[i]) << " ---> " << getBBLabel((it->second)[j]) << ":";
                        errs() << p << "\n";
                        if (p != 0)
                        {
                            std::error_code err;
                            std::string     fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel((it->second)[i]) + "-" + getBBLabel((it->second)[j]);
                            raw_fd_ostream  fd(fileName, err);
                            for (std::map<llvm::BasicBlock*, std::set<llvm::BasicBlock*>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                            {
                                for (std::set<llvm::BasicBlock*>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                                    fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                            }
                        }
                        completeBBs.clear();
                        completeEdges.clear();
                    }
                }
            }

            // keyFuncs，keyBB，keyBBs
            for (std::set<std::string>::iterator it = keyFuncs.begin(); it != keyFuncs.end(); it++)
            {
                std::vector<keyBBPathWithoutCall> r;
                // BB，possiblePaths
                std::vector<std::vector<BasicBlock*>> possiblePaths;

                traverseFuncToReturnWithoutCall(M, *(M.getFunction(*it)), r);
                errs() << "\nPossible AnchorBBs on the path:\n";
                for (std::vector<keyBBPathWithoutCall>::iterator pit = r.begin(); pit != r.end(); pit++)
                {
                    if ((*pit).bb)
                    {
                        errs() << "☐ ";
                        errs() << *it << ":" << getBBLabel((*pit).bb) << "\n";
                    }
                    else
                    {
                        errs() << "☑ ";
                        errs() << *it << ":RETURN\n";
                    }
                    for (std::set<std::string>::iterator fit = (*pit).calledFuncs.begin(); fit != (*pit).calledFuncs.end(); fit++)
                    {
                        errs() << "    call:" << *fit << "\n";
                    }
                }
                for (int i = 0; i < (int)pow(2, r.size() - 1); i++)
                {
                    std::vector<BasicBlock*> path;

                    int n = i;
                    for (std::vector<keyBBPathWithoutCall>::iterator pit = r.begin(); pit != r.end(); pit++)
                    {
                        if ((*pit).bb)
                        {
                            if (n % 2 == 1)
                            {
                                path.push_back((*pit).bb);
                            }
                            n = n / 2;
                        }
                        else
                            path.push_back((*pit).bb);
                    }
                    possiblePaths.push_back(path);
                }
                int typeCount = 0;
                // pathtraverse
                for (std::vector<std::vector<BasicBlock*>>::iterator ppit = possiblePaths.begin(); ppit != possiblePaths.end(); ppit++)
                {
                    BasicBlock* origin = &(M.getFunction(*it)->getEntryBlock());
                    long        total = 1;
                    for (std::vector<BasicBlock*>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
                    {
                        if (origin == (*bit))
                        {
                            continue;
                        }
                        total = total * pathMap[origin][*bit];
                        if (total == 0)
                        {
                            break;
                        }
                        origin = *bit;
                    }
                    if (total)
                    {
                        std::error_code err;
                        std::string     fileName = outputDir + "/" + (*it) + "_Type_" + std::to_string(typeCount);
                        raw_fd_ostream  fd(fileName, err);
                        errs() << "\nType " << typeCount << "\nwith " << total << " paths\n";
                        typeCount++;
                        origin = &(M.getFunction(*it)->getEntryBlock());
                        for (std::vector<BasicBlock*>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
                        {
                            std::vector<std::vector<llvm::BasicBlock*>> results;
                            std::vector<llvm::BasicBlock*>              p;
                            if (*bit)
                                fd << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << (*bit)->getParent()->getName().str() << ":" << getBBLabel((*bit)) << "\n";
                            else
                                fd << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << *it << ":RETURN\n";
                            // traversePath(M, *(origin->getParent()), origin,
                            // *bit, p, results); for
                            // (std::vector<std::vector<llvm::BasicBlock
                            // *>>::iterator resultIt = results.begin();
                            // resultIt != results.end(); resultIt++)
                            // {
                            //     fd << "PATH-" << resultIt - results.begin()
                            //     << "\n"; for (std::vector<llvm::BasicBlock
                            //     *>::iterator pathIt =
                            //     (*resultIt).begin(); pathIt !=
                            //     (*resultIt).end(); pathIt++)
                            //     {
                            //         fd
                            //             <<
                            //             (*pathIt)->getParent()->getName().str()
                            //             << ":" << getBBLabel((*pathIt)) <<
                            //             "\n";
                            //     }
                            // }
                            origin = *bit;
                        }
                    }
                }
            }
        }
        return false;
    }
};

void CFGPass::identifyKeyBasicBlock(Module& M, Function& F)
{
    var_analyzer = new mqttactic::VarAnalysis(M);

    for (Module::iterator mi = M.begin(); mi != M.end(); ++mi)
    {
        Function& f = *mi;
        var_analyzer->SearchKeyVar(M, f);
    }

    for (auto key_var : var_analyzer->key_variables)
    {
        // dbgs() << "-----------------KEYVAR-----------------\n" << key_var->name << "\n\n\n\n";
        for (auto sbb : var_analyzer->SemanticKeyBasicBlocks[key_var])
        {
            KeyBasicBlocks.insert(sbb.first);
            // DebugLoc dbl = sbb.first->back().getDebugLoc();
            // if (dbl.get())
            // {
            //     auto* Scope = cast<DIScope>(dbl.getScope());
            //     dbgs() << Scope->getDirectory().str() + "/" + Scope->getFilename().str() << ": " << dbl->getLine() << ":" << dbl->getColumn() << "\n";
            // }
            // else
            // {
            //     errs() << "No debug info\n";
            // }

            // dbgs() << "[SEMANTIC]: " << sbb.second->semantics << "\n";
            // dbgs() << "[Value]: \n";
            // for (auto var : sbb.second->values)
            // {
            //     errs() << *var << "\n";
            // }

            // dbgs() << "[CONTEXTS]: \n";
            // for (auto kbb_c : sbb.second->contexts)
            // {
            //     for (auto bb : kbb_c)
            //     {
            //         // errs() << bb->getParent()->getName() << ":" <<
            //         //     getBBLabel(bb) << " --> ";
            //         dbl = bb->back().getDebugLoc();
            //         if (dbl.get())
            //         {
            //             auto* Scope = cast<DIScope>(dbl.getScope());
            //             dbgs() << Scope->getFilename().str() << ": " << dbl->getLine() << ":" << dbl->getColumn() << " --> ";
            //         }
            //     }
            //     dbgs() << "\n";
            // }

            // dbgs() << "[Basic Block]: \n" << *(sbb.first) << "\n\n";
            // dbgs() << "----------------------------------\n";
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
        Instruction* inst = *it;
        unsigned int opcode = inst->getOpcode();

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

            // (broker)
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
            // (broker)
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
                    case mqttactic::READ:
                        semantic += key_var->varType + "_read";
                        break;
                    case mqttactic::WRITE:
                        semantic += key_var->varType + "_write";
                        break;
                    case mqttactic::WRITE0:
                        semantic += key_var->varType + "_remove";
                        break;
                    case mqttactic::WRITE1:
                        semantic += key_var->varType + "_add";
                        break;
                    default:
                        errs() << "[ERROR]: Cannot parse semantic of: " << *(siit->first) << "\n";
                        break;
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
        // 
        if (L != NULL && L->getHeader() == Succ)
        {
            SmallVector<BasicBlock*, 8>                         ExitBlocks;
            SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
            L->getExitBlocks(ExitBlocks);
            L->getExitEdges(ExitEdges);
            //  e.g., %100->%30
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
            // origindest
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

void CFGPass::combinePathTypes(Module& M, Function& F, SemanticABB* origin, std::vector<SemanticPathType> paths, std::map<Function*, int> loopStatus, std::vector<BasicBlock*> contextPath)
{
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
                combinePathTypes(M, *calledFunc, FuncSliceGraphHT[calledFunc]->head, calledFuncPaths, loopStatus, contextPath);
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
            dbgs() << "[ERROR]: Loop in the path, loopStatus = " << loopStatus[calledFunc] << "\n";
            loopStatus[calledFunc] -= 1;
        }
    }

    // When encounter the virtual tail Node of a function, means we need to return to the last CALLSITE
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
    }


    for (auto succ : FuncSliceGraph[&F][origin])
    {
        if (succ.second != true)
            continue;

        combinePathTypes(M, F, succ.first, paths, loopStatus, contextPath);
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
                dbgs() << " -> "
                       << "HEAD";
            else if (s->isVirtualTail)
                dbgs() << " -> "
                       << "TAIL";
            else if (s->callSite)
            {

                dbgs() << " -> "
                       << "CALLSITE (" << s->callSite->getName().str() << ")";
            }
            else
            {
                for (auto SI : s->semanticInsts)
                {
                    dbgs() << " -> " << SI.second;
                }
            }
        }
        dbgs() << "\n";
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
            contexts.insert(contexts.end(), var_analyzer->SemanticKeyBasicBlocks[key_var][bb]->contexts.begin(), var_analyzer->SemanticKeyBasicBlocks[key_var][bb]->contexts.end());
        }
    }

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

void CFGPass::readKBBFile(std::string file)
{
    std::string   kbb_str;
    std::ifstream infile(file);
    if (infile.is_open())
    {
        while (!infile.eof())
        {
            std::getline(infile, kbb_str);
            if (ALLBasicBlocks.find(kbb_str) != ALLBasicBlocks.end())
                AnchorBBs.insert(ALLBasicBlocks[kbb_str]);
            else
            {
                errs() << "[ERROR]: can not find key basicblock: " << kbb_str << "\n";
            }
        }
    }
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
            Instruction* inst = &I;
            unsigned int opcode = inst->getOpcode();
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

void CFGPass::traverseFuncToReturn(Module& M, Function& F, std::vector<keyBBPath> path, std::vector<keyBBPath>& result)
{
    for (BasicBlock& BB : F)
    {
        if (AnchorBBs.find(&BB) != AnchorBBs.end())
        {
            struct keyBBPath k;
            k.bb = &BB;
            k.mustBePassed = false;
            path.push_back(k);
        }
        for (Instruction& I : BB)
        {
            Instruction* inst = &I;
            unsigned int opcode = inst->getOpcode();
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
                    std::vector<keyBBPath> r;
                    std::vector<keyBBPath> p;
                    traverseFuncToReturn(M, *(call->getCalledFunction()), p, r);
                    for (std::vector<keyBBPath>::iterator it = r.begin(); it != r.end(); it++)
                    {
                        path.push_back(*it);
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
                if (keyFuncs.find(calledFuncName) != keyFuncs.end() && AnchorBBs.find(&BB) != AnchorBBs.end())
                {
                    std::vector<keyBBPath> r;
                    std::vector<keyBBPath> p;
                    traverseFuncToReturn(M, *(call->getCalledFunction()), p, r);
                    for (std::vector<keyBBPath>::iterator it = r.begin(); it != r.end(); it++)
                    {
                        path.push_back(*it);
                    }
                }
                break;
            }
            case Instruction::Ret: {
                // ，null basicblock，
                if (path[path.end() - path.begin() - 1].bb != &BB)
                {
                    struct keyBBPath k;
                    k.bb = nullptr;
                    k.mustBePassed = false;
                    path.push_back(k);
                    for (std::vector<keyBBPath>::iterator it = path.begin(); it != path.end(); it++)
                    {
                        result.push_back(*it);
                    }
                }
                return;
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
            Instruction* inst = &I;
            unsigned int opcode = inst->getOpcode();
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
                // ，null basicblock，
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
    // 
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
        // 
        if (L != NULL && L->getHeader() == Succ)
        {
            SmallVector<BasicBlock*, 8>                         ExitBlocks;
            SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitEdges;
            L->getExitBlocks(ExitBlocks);
            L->getExitEdges(ExitEdges);
            //  e.g. %100->%30
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
                                   Succ);  // ，==
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
            // origindest
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
    // 
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
        // 
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
