

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
#include "../Include/CONFIG.h"
using namespace llvm;
namespace
{
    class CFGPass : public ModulePass
    {
    public:
        
        struct keyBBPath
        {
            BasicBlock *bb;
            std::string func;
            
            bool mustBePassed;
        };
        
        struct keyBBPathWithoutCall
        {
            BasicBlock *bb;
            
            std::set<std::string> calledFuncs;
        };
        static char ID;
        
        std::map<std::string, short> ALLFunctions;
        
        std::set<std::string> ALLKeyBranches;
        
        std::set<BasicBlock *> keyBBs;
        
        std::set<BasicBlock *> endBBs;
        
        std::set<std::string> keyFuncs;
        
        std::map<BasicBlock *, long> completeBBs;
        
        std::map<BasicBlock *, std::set<BasicBlock *>> completeEdges;
        
        int switchEnd = 0;
        std::string handlerName = handle__connect;
        std::string outputDir = "./OUTPUT";
        
        bool clearALLFunctions();
        
        std::string getBBLabel(const BasicBlock *Node);
        int getBBLabelIdx(const Function *func, const BasicBlock *Node);
        
        int traverseFunc(Module &M, Function &F);
        
        bool traverseFuncToEnd(Module &M, Function &F, BasicBlock *end, bool foundEnd, std::vector<keyBBPath> path, std::vector<std::vector<keyBBPath>> &endPath, std::vector<std::vector<keyBBPath>> &results);
        
        void traverseFuncToReturn(Module &M, Function &F, std::vector<keyBBPath> path, std::vector<keyBBPath> &result);
        void traverseFuncToReturnWithoutCall(Module &M, Function &F, std::vector<keyBBPathWithoutCall> &result);
        
        long traversePath(Module &M, Function &F, BasicBlock *origin, BasicBlock *dest, std::vector<BasicBlock *> paths);
        
        long traversePath(Module &M, Function &F, BasicBlock *origin, BasicBlock *dest, std::vector<BasicBlock *> paths, std::vector<std::vector<BasicBlock *>> &results);
        bool isRetBBs(BasicBlock *bb);
        int endOfHandler(CallBase *call);
        bool isKeyBBs(std::string str);
        std::string replaceKeyBBsOrEndName(std::string str);
        CFGPass() : ModulePass(ID)
        {
            
            std::string fname;
            std::ifstream infile("./ALLFunctions");
            if (infile.is_open())
            {
                while (!infile.eof())
                {
                    std::getline(infile, fname);
                    ALLFunctions.insert(std::map<std::string, short>::value_type(fname, 0));
                }
            }
            infile.close();
            
            fname = "";
            infile.open("./ALLKeyBranches");
            if (infile.is_open())
            {
                while (!infile.eof())
                {
                    std::getline(infile, fname);
                    ALLKeyBranches.insert(fname);
                }
            }
            infile.close();
        }
        void getAnalysisUsage(AnalysisUsage &AU) const override
        {
            AU.setPreservesCFG();
            AU.addRequired<LoopInfoWrapperPass>();
        }
        bool runOnModule(Module &M) override
        {
            Function &F = *M.getFunction(handlerName);
            std::vector<BasicBlock *> paths;
            
            std::map<std::string, std::vector<BasicBlock *>> keyVecs;
            
            std::map<BasicBlock *, std::map<BasicBlock *, long>> pathMap;
            errs()
                << "Analyzing Function: " << F.getName().str() << "\n";
            traverseFunc(M, F);
            for (std::set<BasicBlock *>::iterator it = keyBBs.begin(); it != keyBBs.end(); it++)
            {
                DebugLoc ACL_dbg_line;
                errs()
                    << "/*------------------------------KEY BASIC BLOCKS---------------------------------*/\n"
                    << (*it)->getParent()->getName() << ":" << getBBLabel(*it) << "\nCall:[";
                for (Instruction &I : *(*it))
                {
                    Instruction *inst = &I;
                    unsigned int opcode = inst->getOpcode();
                    switch (opcode)
                    {
                    case Instruction::Call:
                    {
                        CallInst *call = static_cast<CallInst *>(inst);
                        std::string calledFuncName = "";
                        if (call->isIndirectCall() || !(call->getCalledFunction()))
                        {
                            const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                                calledFuncName = GV->getAliasee()->getName().str();
                            else
                                break;
                        }
                        else
                        {
                            calledFuncName = call->getCalledFunction()->getName().str();
                        }
                        if (keyFuncs.find(calledFuncName) != keyFuncs.end())
                        {
                            errs() << calledFuncName << ", ";
                        }
                        break;
                    }
                    case Instruction::Invoke:
                    {
                        InvokeInst *call = static_cast<InvokeInst *>(inst);
                        std::string calledFuncName = "";
                        if (call->isIndirectCall() || !(call->getCalledFunction()))
                        {
                            const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                                calledFuncName = GV->getAliasee()->getName().str();
                            else
                                break;
                        }
                        else
                        {
                            calledFuncName = call->getCalledFunction()->getName().str();
                        }
                        if (keyFuncs.find(calledFuncName) != keyFuncs.end())
                        {
                            errs() << calledFuncName << ", ";
                        }
                        break;
                    }
                    default:
                        break;
                    }
                }
                errs()
                    << "]\n";
                for (Instruction &I : *(*it))
                {
                    Instruction *inst = &I;
                    unsigned int opcode = inst->getOpcode();
                    switch (opcode)
                    {
                    case Instruction::Call:
                    {
                        CallInst *call = static_cast<CallInst *>(inst);
                        std::string calledFuncName = "";
                        if (call->isIndirectCall() || !(call->getCalledFunction()))
                        {
                            const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                                calledFuncName = GV->getAliasee()->getName().str();
                            else
                                break;
                        }
                        else
                        {
                            calledFuncName = call->getCalledFunction()->getName().str();
                        }
                        if (replaceKeyBBsOrEndName(calledFuncName) != "ERROR")
                        {
                            errs() << replaceKeyBBsOrEndName(calledFuncName) << "-----";
                            ACL_dbg_line = call->getDebugLoc();
                            if (ACL_dbg_line.get())
                            {
                                auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
                                std::ifstream infile(Scope->getDirectory().str() + "/" + Scope->getFilename().str());
                                
                                if (infile.is_open())
                                {
                                    int line = 0;
                                    std::string content = "";
                                    
                                    int left = 0;
                                    int right = 0;
                                    while (!infile.eof())
                                    {
                                        std::getline(infile, content);
                                        line++;
                                        if (line == ACL_dbg_line.getLine())
                                        {
                                            errs() << content;
                                            left += count(content.begin(), content.end(), '(');
                                            right += count(content.begin(), content.end(), ')');
                                            while (left != right)
                                            {
                                                std::getline(infile, content);
                                                left += count(content.begin(), content.end(), '(');
                                                right += count(content.begin(), content.end(), ')');
                                                errs() << content;
                                            }
                                            errs() << '\n';
                                            break;
                                        }
                                    }
                                }
                                infile.close();
                            }
                        }
                        else
                        {
                            errs() << I << "\n";
                        }
                        break;
                    }
                    case Instruction::Invoke:
                    {
                        InvokeInst *call = static_cast<InvokeInst *>(inst);
                        std::string calledFuncName = "";
                        if (call->isIndirectCall() || !(call->getCalledFunction()))
                        {
                            const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                                calledFuncName = GV->getAliasee()->getName().str();
                            else
                                break;
                        }
                        else
                        {
                            calledFuncName = call->getCalledFunction()->getName().str();
                        }
                        if (replaceKeyBBsOrEndName(calledFuncName) != "ERROR")
                        {
                            errs() << replaceKeyBBsOrEndName(calledFuncName) << "-----";
                            ACL_dbg_line = call->getDebugLoc();
                            if (ACL_dbg_line.get())
                            {
                                auto *Scope = cast<DIScope>(ACL_dbg_line.getScope());
                                std::ifstream infile(Scope->getDirectory().str() + "/" + Scope->getFilename().str());
                                if (infile.is_open())
                                {
                                    int line = 0;
                                    std::string content = "";
                                    
                                    int left = 0;
                                    int right = 0;
                                    while (!infile.eof())
                                    {
                                        std::getline(infile, content);
                                        line++;
                                        if (line == ACL_dbg_line.getLine())
                                        {
                                            errs() << content;
                                            left += count(content.begin(), content.end(), '(');
                                            right += count(content.begin(), content.end(), ')');
                                            while (left != right)
                                            {
                                                std::getline(infile, content);
                                                left += count(content.begin(), content.end(), '(');
                                                right += count(content.begin(), content.end(), ')');
                                                errs() << content;
                                            }
                                            errs() << '\n';
                                            break;
                                        }
                                    }
                                }
                                infile.close();
                            }
                        }
                        else
                        {
                            errs() << I << "\n";
                        }
                        break;
                    }
                    default:
                    {
                        errs() << I << "\n";
                        break;
                    }
                    }
                }
            }
            
            for (std::set<BasicBlock *>::iterator it = keyBBs.begin(); it != keyBBs.end(); it++)
            {
                std::string funcName = (*it)->getParent()->getName().str();
                int label = getBBLabelIdx((*it)->getParent(), *it);
                std::map<std::string, std::vector<BasicBlock *>>::iterator keyVecit = keyVecs.find(funcName);
                if (keyVecit == keyVecs.end())
                {
                    std::vector<BasicBlock *> v;
                    v.push_back(*it);
                    keyVecs.insert(std::map<std::string, std::vector<BasicBlock *>>::value_type(funcName, v));
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
                std::vector<BasicBlock *> v;
                keyVecs.insert(std::map<std::string, std::vector<BasicBlock *>>::value_type(F.getName().str(), v));
            }
            
            for (std::map<std::string, std::vector<BasicBlock *>>::iterator it = keyVecs.begin(); it != keyVecs.end(); it++)
            {
                long p = 0;
                errs() << "\n"
                       << it->first << ":\n";
                
                for (int i = 0; i < it->second.size(); i++)
                {
                    p = traversePath(M, *M.getFunction(it->first), &(M.getFunction(it->first)->getEntryBlock()), (it->second)[i], paths);
                    if (pathMap.find(&(M.getFunction(it->first)->getEntryBlock())) == pathMap.end())
                    {
                        std::map<BasicBlock *, long> dest;
                        dest.insert(std::map<BasicBlock *, long>::value_type((it->second)[i], p));
                        pathMap.insert(std::map<BasicBlock *, std::map<BasicBlock *, long>>::value_type(&(M.getFunction(it->first)->getEntryBlock()), dest));
                    }
                    else
                    {
                        pathMap[&(M.getFunction(it->first)->getEntryBlock())].insert(std::map<BasicBlock *, long>::value_type((it->second)[i], p));
                    }
                    errs()
                        << it->first << " ---> " << getBBLabel((it->second)[i]) << ":";
                    errs() << p << "\n";
                    
                    if (p != 0)
                    {
                        std::error_code err;
                        std::string fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel(&(M.getFunction(it->first)->getEntryBlock())) + "-" + getBBLabel((it->second)[i]);
                        raw_fd_ostream fd(fileName, err);
                        for (std::map<llvm::BasicBlock *, std::set<llvm::BasicBlock *>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                        {
                            for (std::set<llvm::BasicBlock *>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                                fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                        }
                    }
                    completeBBs.clear();
                    completeEdges.clear();
                }
                
                p = traversePath(M, *M.getFunction(it->first), &(M.getFunction(it->first)->getEntryBlock()), nullptr, paths);
                if (pathMap.find(&(M.getFunction(it->first)->getEntryBlock())) == pathMap.end())
                {
                    std::map<BasicBlock *, long> dest;
                    dest.insert(std::map<BasicBlock *, long>::value_type(nullptr, p));
                    pathMap.insert(std::map<BasicBlock *, std::map<BasicBlock *, long>>::value_type(&(M.getFunction(it->first)->getEntryBlock()), dest));
                }
                else
                {
                    pathMap[&(M.getFunction(it->first)->getEntryBlock())].insert(std::map<BasicBlock *, long>::value_type(nullptr, p));
                }
                errs()
                    << it->first << " ---> "
                    << "RETURN"
                    << ":";
                errs() << p << "\n";
                if (p != 0)
                {
                    std::error_code err;
                    std::string fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel(&(M.getFunction(it->first)->getEntryBlock())) + "-" + "RETURN";
                    raw_fd_ostream fd(fileName, err);
                    for (std::map<llvm::BasicBlock *, std::set<llvm::BasicBlock *>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                    {
                        for (std::set<llvm::BasicBlock *>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                            fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                    }
                }
                completeBBs.clear();
                completeEdges.clear();
                
                for (int i = 0; i < it->second.size(); i++)
                {
                    p = traversePath(M, *M.getFunction(it->first), (it->second)[i], nullptr, paths);
                    if (pathMap.find((it->second)[i]) == pathMap.end())
                    {
                        std::map<BasicBlock *, long> dest;
                        dest.insert(std::map<BasicBlock *, long>::value_type(nullptr, p));
                        pathMap.insert(std::map<BasicBlock *, std::map<BasicBlock *, long>>::value_type((it->second)[i], dest));
                    }
                    else
                    {
                        pathMap[(it->second)[i]].insert(std::map<BasicBlock *, long>::value_type(nullptr, p));
                    }
                    errs()
                        << getBBLabel((it->second)[i]) << " ---> "
                        << "RETURN"
                        << ":";
                    errs()
                        << p << "\n";
                    if (p != 0)
                    {
                        std::error_code err;
                        std::string fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel((it->second)[i]) + "-" + "RETURN";
                        raw_fd_ostream fd(fileName, err);
                        for (std::map<llvm::BasicBlock *, std::set<llvm::BasicBlock *>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                        {
                            for (std::set<llvm::BasicBlock *>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
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
                            std::map<BasicBlock *, long> dest;
                            dest.insert(std::map<BasicBlock *, long>::value_type((it->second)[j], p));
                            pathMap.insert(std::map<BasicBlock *, std::map<BasicBlock *, long>>::value_type((it->second)[i], dest));
                        }
                        else
                        {
                            pathMap[(it->second)[i]].insert(std::map<BasicBlock *, long>::value_type((it->second)[j], p));
                        }
                        errs()
                            << getBBLabel((it->second)[i]) << " ---> " << getBBLabel((it->second)[j]) << ":";
                        errs()
                            << p << "\n";
                        if (p != 0)
                        {
                            std::error_code err;
                            std::string fileName = outputDir + "/KEYBBS/" + it->first + "-" + getBBLabel((it->second)[i]) + "-" + getBBLabel((it->second)[j]);
                            raw_fd_ostream fd(fileName, err);
                            for (std::map<llvm::BasicBlock *, std::set<llvm::BasicBlock *>>::iterator cBit = completeEdges.begin(); cBit != completeEdges.end(); cBit++)
                            {
                                for (std::set<llvm::BasicBlock *>::iterator destit = cBit->second.begin(); destit != cBit->second.end(); destit++)
                                    fd << it->first << ":" << getBBLabel(cBit->first) << "-" << getBBLabel(*destit) << "\n";
                            }
                        }
                        completeBBs.clear();
                        completeEdges.clear();
                    }
                }
            }
            if (endBBs.empty() || handlerName == handle__publish)
            {
                keyFuncs.insert(handlerName);
            }
            int publish_type = 0;
            
            for (std::set<std::string>::iterator it = keyFuncs.begin(); it != keyFuncs.end(); it++)
            {
                std::vector<keyBBPathWithoutCall> r;
                
                std::vector<std::vector<BasicBlock *>> possiblePaths;
                traverseFuncToReturnWithoutCall(M, *(M.getFunction(*it)), r);
                errs() << "\nPossible keyBBs on the path:\n";
                for (std::vector<keyBBPathWithoutCall>::iterator pit = r.begin(); pit != r.end(); pit++)
                {
                    if ((*pit).bb)
                    {
                        errs() << "??? ";
                        errs() << *it << ":" << getBBLabel((*pit).bb) << "\n";
                    }
                    else
                    {
                        errs() << "??? ";
                        errs() << *it << ":RETURN\n";
                    }
                    for (std::set<std::string>::iterator fit = (*pit).calledFuncs.begin(); fit != (*pit).calledFuncs.end(); fit++)
                    {
                        errs() << "    call:" << *fit << "\n";
                    }
                }
                for (int i = 0; i < (int)pow(2, r.size() - 1); i++)
                {
                    std::vector<BasicBlock *> path;
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
                
                for (std::vector<std::vector<BasicBlock *>>::iterator ppit = possiblePaths.begin(); ppit != possiblePaths.end(); ppit++)
                {
                    BasicBlock *origin = &(M.getFunction(*it)->getEntryBlock());
                    long total = 1;
                    for (std::vector<BasicBlock *>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
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
                        std::string fileName = outputDir + "/" + (*it) + "_Type_" + std::to_string(typeCount);
                        raw_fd_ostream fd(fileName, err);
                        errs() << "\nType " << typeCount << "\nwith "
                               << total << " paths\n";
                        typeCount++;
                        origin = &(M.getFunction(*it)->getEntryBlock());
                        for (std::vector<BasicBlock *>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
                        {
                            std::vector<std::vector<llvm::BasicBlock *>> results;
                            std::vector<llvm::BasicBlock *> p;
                            if (*bit)
                                fd
                                    << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << (*bit)->getParent()->getName().str() << ":" << getBBLabel((*bit)) << "\n";
                            else
                                fd
                                    << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << *it << ":RETURN\n";
                            
                            
                            
                            
                            
                            
                            
                            
                            
                            
                            origin = *bit;
                        }
                    }
                }
                if (handlerName == handle__publish)
                {
                    publish_type = typeCount;
                }
            }
            int typeCount = publish_type;
            
            for (std::set<BasicBlock *>::iterator it = endBBs.begin(); it != endBBs.end(); it++)
            {
                std::vector<keyBBPath> pathTmp;
                std::vector<std::vector<keyBBPath>> results;
                std::vector<std::vector<keyBBPath>> endPath;
                bool found_end = false;
                while (true)
                {
                    found_end = traverseFuncToEnd(M, F, *it, false, pathTmp, endPath, results);
                    if (found_end == false)
                    {
                        break;
                    }
                }
                errs() << "\nEND: " << (*it)->getParent()->getName().str() << ":" << getBBLabel(*it) << "\n";
                
                for (std::vector<std::vector<keyBBPath>>::iterator rit = results.begin(); rit != results.end(); rit++)
                {
                    int vCount = (*rit).size();
                    errs() << "\nPossible keyBBs on the path:\n";
                    std::string funcName = "";
                    for (std::vector<keyBBPath>::iterator pit = (*rit).begin(); pit != (*rit).end(); pit++)
                    {
                        if ((*pit).bb)
                        {
                            if ((*pit).bb == *it)
                            {
                                (*pit).mustBePassed = true;
                                vCount--;
                                errs() << "??? ";
                            }
                            else if (pit != (*rit).end() - 1 && (*(pit + 1)).bb && (*pit).bb->getParent() != (*(pit + 1)).bb->getParent())
                            {
                                (*pit).mustBePassed = true;
                                vCount--;
                                errs() << "??? ";
                            }
                            else
                            {
                                (*pit).mustBePassed = false;
                                errs() << "??? ";
                            }
                            errs() << (*pit).bb->getParent()->getName().str() << ":" << getBBLabel((*pit).bb) << "\n";
                            funcName = (*pit).bb->getParent()->getName().str();
                        }
                        else
                        {
                            (*pit).mustBePassed = true;
                            vCount--;
                            errs() << "??? ";
                            errs() << funcName << ":RETURN\n";
                        }
                    }
                    
                    std::vector<std::vector<BasicBlock *>> possiblePaths;
                    for (int i = 0; i < (int)pow(2, vCount); i++)
                    {
                        std::vector<BasicBlock *> path;
                        int n = i;
                        for (std::vector<keyBBPath>::iterator pit = (*rit).begin(); pit != (*rit).end(); pit++)
                        {
                            if ((*pit).mustBePassed == true)
                            {
                                path.push_back((*pit).bb);
                            }
                            else
                            {
                                if (n % 2 == 1)
                                {
                                    path.push_back((*pit).bb);
                                }
                                n = n / 2;
                            }
                        }
                        possiblePaths.push_back(path);
                    }
                    
                    for (std::vector<std::vector<BasicBlock *>>::iterator ppit = possiblePaths.begin(); ppit != possiblePaths.end(); ppit++)
                    {
                        BasicBlock *origin = &(F.getEntryBlock());
                        long total = 1;
                        std::vector<BasicBlock *> callStack;
                        for (std::vector<BasicBlock *>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
                        {
                            if (origin && origin == (*bit))
                            {
                                continue;
                            }
                            if (origin && (*bit) && origin->getParent() != (*bit)->getParent())
                            {
                                callStack.push_back(origin);
                                origin = &((*bit)->getParent()->getEntryBlock());
                            }
                            if (origin == nullptr)
                            {
                                origin = callStack[callStack.end() - callStack.begin() - 1];
                                callStack.pop_back();
                            }
                            total = total * pathMap[origin][*bit];
                            if (total == 0)
                            {
                                break;
                            }
                            origin = *bit;
                        }
                        callStack.clear();
                        if (total)
                        {
                            std::error_code err;
                            std::string fileName = outputDir + "/" + F.getName().str() + "_Type_" + std::to_string(typeCount);
                            raw_fd_ostream fd(fileName, err);
                            errs() << "\nType " << typeCount << "\nwith "
                                   << total << " paths\n";
                            typeCount++;
                            origin = &(F.getEntryBlock());
                            for (std::vector<BasicBlock *>::iterator bit = (*ppit).begin(); bit != (*ppit).end(); bit++)
                            {
                                std::vector<std::vector<llvm::BasicBlock *>> results;
                                std::vector<llvm::BasicBlock *> p;
                                if (origin && origin == (*bit))
                                {
                                    continue;
                                }
                                if (origin && (*bit) && origin->getParent() != (*bit)->getParent())
                                {
                                    callStack.push_back(origin);
                                    origin = &((*bit)->getParent()->getEntryBlock());
                                }
                                if (origin == nullptr)
                                {
                                    origin = callStack[callStack.end() - callStack.begin() - 1];
                                    callStack.pop_back();
                                }
                                
                                if (*bit)
                                    fd
                                        << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << (*bit)->getParent()->getName().str() << ":" << getBBLabel((*bit)) << "\n";
                                else
                                    fd
                                        << "* " << origin->getParent()->getName().str() << ":" << getBBLabel((origin)) << " ----> " << origin->getParent()->getName().str() << ":RETURN\n";
                                
                                
                                
                                
                                
                                
                                
                                
                                
                                origin = *bit;
                            }
                        }
                    }
                }
            }
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            
            return false;
        }
    };
    bool CFGPass::clearALLFunctions()
    {
        for (std::map<std::string, short>::iterator it = CFGPass::ALLFunctions.begin(); it != CFGPass::ALLFunctions.end(); it++)
        {
            it->second = 0;
        }
        return true;
    }
    std::string CFGPass::getBBLabel(const BasicBlock *Node)
    {
        if (!Node->getName().empty())
            return Node->getName().str();
        std::string Str;
        raw_string_ostream OS(Str);
        Node->printAsOperand(OS, false);
        return OS.str();
    }
    int CFGPass::getBBLabelIdx(const Function *func, const BasicBlock *Node)
    {
        int idx = 0;
        for (auto &iter : func->getBasicBlockList())
        {
            if (Node == &iter)
            {
                break;
            }
            idx++;
        }
        return idx;
    }
    bool CFGPass::traverseFuncToEnd(Module &M, Function &F, BasicBlock *end, bool foundEnd, std::vector<keyBBPath> path, std::vector<std::vector<keyBBPath>> &endPath, std::vector<std::vector<keyBBPath>> &results)
    {
        bool found_end = foundEnd;
        for (BasicBlock &BB : F)
        {
            int Bindex;
            if (keyBBs.find(&BB) != keyBBs.end())
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
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (!found_end && keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
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
                case Instruction::Invoke:
                {
                    InvokeInst *call = static_cast<InvokeInst *>(inst);
                    std::string calledFuncName = "";
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (!found_end && keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
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
                case Instruction::Ret:
                {
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
    void CFGPass::traverseFuncToReturn(Module &M, Function &F, std::vector<keyBBPath> path, std::vector<keyBBPath> &result)
    {
        for (BasicBlock &BB : F)
        {
            if (keyBBs.find(&BB) != keyBBs.end())
            {
                struct keyBBPath k;
                k.bb = &BB;
                k.mustBePassed = false;
                path.push_back(k);
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
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
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
                case Instruction::Invoke:
                {
                    InvokeInst *call = static_cast<InvokeInst *>(inst);
                    std::string calledFuncName = "";
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
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
                case Instruction::Ret:
                {
                    
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
    void CFGPass::traverseFuncToReturnWithoutCall(Module &M, Function &F, std::vector<keyBBPathWithoutCall> &result)
    {
        for (BasicBlock &BB : F)
        {
            if (keyBBs.find(&BB) != keyBBs.end())
            {
                struct keyBBPathWithoutCall k;
                std::set<std::string> F;
                k.bb = &BB;
                k.calledFuncs = F;
                result.push_back(k);
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
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
                    {
                        result[result.end() - result.begin() - 1].calledFuncs.insert(calledFuncName);
                    }
                    break;
                }
                case Instruction::Invoke:
                {
                    InvokeInst *call = static_cast<InvokeInst *>(inst);
                    std::string calledFuncName = "";
                    if (call->isIndirectCall() || !(call->getCalledFunction()))
                    {
                        const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                        if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                            calledFuncName = GV->getAliasee()->getName().str();
                        else
                            break;
                    }
                    else
                    {
                        calledFuncName = call->getCalledFunction()->getName().str();
                    }
                    if (keyFuncs.find(calledFuncName) != keyFuncs.end() && keyBBs.find(&BB) != keyBBs.end())
                    {
                        result[result.end() - result.begin() - 1].calledFuncs.insert(calledFuncName);
                    }
                    break;
                }
                case Instruction::Ret:
                {
                    
                    if (result.empty() || result[result.end() - result.begin() - 1].bb != &BB)
                    {
                        struct keyBBPathWithoutCall k;
                        std::set<std::string> F;
                        k.bb = nullptr;
                        k.calledFuncs = F;
                        result.push_back(k);
                    }
                    else
                    {
                        result[result.end() - result.begin() - 1].bb = nullptr;
                    }
                    return;
                }
                default:
                    break;
                }
            }
        }
    }
    int CFGPass::traverseFunc(Module &M, Function &F)
    {
        std::set<Instruction *> insts;
        std::set<Instruction *>::iterator it;
        int retval = 1;
        for (BasicBlock &BB : F)
            for (Instruction &I : BB)
            {
                insts.insert(&I);
            }
        for (it = insts.begin(); it != insts.end(); it++)
        {
            Instruction *inst = *it;
            
            unsigned int opcode = inst->getOpcode();
            
            
            
            
            
            
            
            
            
            
            
            switch (opcode)
            {
            case Instruction::Call:
            {
                CallInst *call = static_cast<CallInst *>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || !(call->getCalledFunction()))
                {
                    const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                    if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                        calledFuncName = GV->getAliasee()->getName().str();
                    else
                        break;
                }
                else
                {
                    calledFuncName = call->getCalledFunction()->getName().str();
                }
                bool isKeyFunc = false;
                bool hasEnd = false;
                std::map<std::string, short>::iterator Fit = ALLFunctions.find(calledFuncName);
                
                if (Fit != ALLFunctions.end() && calledFuncName != "log__printf")
                {
                    if (Fit->second == 1)
                        goto FINDKEYFUNCS;
                    else if (Fit->second == 2)
                    {
                        isKeyFunc = true;
                        goto FINDKEYFUNCS;
                    }
                    else if (Fit->second == 3)
                    {
                        isKeyFunc = true;
                        hasEnd = true;
                        goto FINDKEYFUNCS;
                    }
                    if (isKeyBBs(calledFuncName))
                    {
                        isKeyFunc = true;
                        Fit->second = 2;
                    }
                    else if (endOfHandler(call) == 2)
                    {
                        endBBs.insert(call->getParent());
                        isKeyFunc = true;
                        hasEnd = true;
                    }
                    else if (endOfHandler(call) == 1)
                    {
                        break;
                    }
                    else
                    {
                        
                        Function &calledFunc = *M.getFunction(calledFuncName);
                        Fit->second = 1;
                        int rt = traverseFunc(M, calledFunc);
                        if (rt == 2)
                        {
                            isKeyFunc = true;
                            Fit->second = 2;
                        }
                        else if (rt == 3)
                        {
                            isKeyFunc = true;
                            hasEnd = true;
                            Fit->second = 3;
                        }
                    }
                FINDKEYFUNCS:
                    if (isKeyFunc)
                    {
                        keyBBs.insert(call->getParent());
                        if (!(isKeyBBs(calledFuncName) || endOfHandler(call) == 2))
                            keyFuncs.insert(calledFuncName);
                        if (retval < 2)
                            retval = 2;
                    }
                    if (hasEnd)
                    {
                        retval = 3;
                    }
                }
                break;
            }
            case Instruction::Invoke:
            {
                InvokeInst *call = static_cast<InvokeInst *>(inst);
                std::string calledFuncName = "";
                if (call->isIndirectCall() || !(call->getCalledFunction()))
                {
                    const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
                    if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                        calledFuncName = GV->getAliasee()->getName().str();
                    else
                        break;
                }
                else
                {
                    calledFuncName = call->getCalledFunction()->getName().str();
                }
                bool isKeyFunc = false;
                bool hasEnd = false;
                std::map<std::string, short>::iterator Fit = ALLFunctions.find(calledFuncName);
                
                if (Fit != ALLFunctions.end() && calledFuncName != "log__printf")
                {
                    if (Fit->second == 1)
                        goto FINDKEYFUNCS_2;
                    else if (Fit->second == 2)
                    {
                        isKeyFunc = true;
                        goto FINDKEYFUNCS_2;
                    }
                    else if (Fit->second == 3)
                    {
                        isKeyFunc = true;
                        hasEnd = true;
                        goto FINDKEYFUNCS_2;
                    }
                    if (isKeyBBs(calledFuncName))
                    {
                        isKeyFunc = true;
                        Fit->second = 2;
                    }
                    else if (endOfHandler(call) == 2)
                    {
                        endBBs.insert(call->getParent());
                        isKeyFunc = true;
                        hasEnd = true;
                    }
                    else if (endOfHandler(call) == 1)
                    {
                        break;
                    }
                    else
                    {
                        
                        Function &calledFunc = *M.getFunction(calledFuncName);
                        Fit->second = 1;
                        int rt = traverseFunc(M, calledFunc);
                        if (rt == 2)
                        {
                            isKeyFunc = true;
                            Fit->second = 2;
                        }
                        else if (rt == 3)
                        {
                            isKeyFunc = true;
                            hasEnd = true;
                            Fit->second = 3;
                        }
                    }
                FINDKEYFUNCS_2:
                    if (isKeyFunc)
                    {
                        keyBBs.insert(call->getParent());
                        if (!(isKeyBBs(calledFuncName) || endOfHandler(call) == 2))
                            keyFuncs.insert(calledFuncName);
                        if (retval < 2)
                            retval = 2;
                    }
                    if (hasEnd)
                    {
                        retval = 3;
                    }
                }
                break;
            }
            
            
            
            
            
            
            
            
            
            
            
            
            case Instruction::Br:
            {
                BranchInst *br = static_cast<BranchInst *>(inst);
                try
                {
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                }
                catch (...)
                {
                }
                break;
            }
            case Instruction::Switch:
            {
                
                
                
                
                
                
                
                
                
                
                
                
                break;
            }
            case Instruction::Select:
            {
                break;
            }
            default:
                break;
            }
        }
        return retval;
    }
    long CFGPass::traversePath(Module &M, Function &F, BasicBlock *origin, BasicBlock *dest, std::vector<BasicBlock *> paths)
    {
        paths.push_back(origin);
        std::map<BasicBlock *, long>::iterator Bit = completeBBs.find(origin);
        if (Bit != completeBBs.end())
            return Bit->second;
        if (origin == dest)
        {
            if (Bit == completeBBs.end())
                completeBBs.insert(std::map<BasicBlock *, long>::value_type(origin, 1));
            return 1;
        }
        
        else if (paths.size() > 1 && keyBBs.find(origin) != keyBBs.end())
            return 0;
        long PathCount = 0;
        LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
        std::set<BasicBlock *> NextBBs;
        int succCount = 0;
        Loop *L = LI.getLoopFor(origin);
        for (BasicBlock *Succ : successors(origin))
        {
            succCount++;
            
            if (L != NULL && L->getHeader() == Succ)
            {
                SmallVector<BasicBlock *, 8> ExitBlocks;
                SmallVector<std::pair<BasicBlock *, BasicBlock *>, 8> ExitEdges;
                L->getExitBlocks(ExitBlocks);
                L->getExitEdges(ExitEdges);
                
                std::map<BasicBlock *, std::set<BasicBlock *>>::iterator eit = completeEdges.find(origin);
                if (eit == completeEdges.end())
                {
                    std::set<BasicBlock *> v;
                    v.insert(Succ);
                    completeEdges.insert(std::map<BasicBlock *, std::set<BasicBlock *>>::value_type(origin, v));
                }
                else
                {
                    eit->second.insert(Succ);
                }
                for (std::pair<BasicBlock *, BasicBlock *> ExitEdge : ExitEdges)
                {
                    eit = completeEdges.find(ExitEdge.first);
                    if (eit == completeEdges.end())
                    {
                        std::set<BasicBlock *> v;
                        v.insert(ExitEdge.second);
                        completeEdges.insert(std::map<BasicBlock *, std::set<BasicBlock *>>::value_type(ExitEdge.first, v));
                    }
                    else
                    {
                        eit->second.insert(ExitEdge.second);
                    }
                }
                for (llvm::BasicBlock *ExitBlock : ExitBlocks)
                {
                    NextBBs.insert(ExitBlock);
                }
            }
            else
                NextBBs.insert(Succ);
        }
        for (BasicBlock *Nextbb : NextBBs)
        {
            int c = traversePath(M, F, Nextbb, dest, paths);
            PathCount += c;
            if (c > 0)
            {
                
                std::map<BasicBlock *, std::set<BasicBlock *>>::iterator eit = completeEdges.find(origin);
                if (eit == completeEdges.end())
                {
                    std::set<BasicBlock *> v;
                    v.insert(Nextbb);
                    completeEdges.insert(std::map<BasicBlock *, std::set<BasicBlock *>>::value_type(origin, v));
                }
                else
                {
                    eit->second.insert(Nextbb);
                }
            }
        }
        if (dest == nullptr && succCount == 0 && isRetBBs(origin))
        {
            completeBBs.insert(std::map<BasicBlock *, long>::value_type(origin, 1));
            return 1;
        }
        completeBBs.insert(std::map<BasicBlock *, long>::value_type(origin, PathCount));
        return PathCount;
    }
    long CFGPass::traversePath(Module &M, Function &F, BasicBlock *origin, BasicBlock *dest, std::vector<BasicBlock *> paths, std::vector<std::vector<BasicBlock *>> &results)
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
        
        else if (paths.size() > 1 && keyBBs.find(origin) != keyBBs.end())
            return 0;
        long PathCount = 0;
        LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
        std::set<BasicBlock *> NextBBs;
        int succCount = 0;
        Loop *L = LI.getLoopFor(origin);
        for (BasicBlock *Succ : successors(origin))
        {
            succCount++;
            
            if (L != NULL && L->getHeader() == Succ)
            {
                SmallVector<BasicBlock *, 8> ExitBlocks;
                L->getExitBlocks(ExitBlocks);
                for (llvm::BasicBlock *ExitBlock : ExitBlocks)
                {
                    NextBBs.insert(ExitBlock);
                }
            }
            else
                NextBBs.insert(Succ);
        }
        for (BasicBlock *Nextbb : NextBBs)
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
    bool CFGPass::isRetBBs(BasicBlock *bb)
    {
        BasicBlock &BB = *bb;
        bool ret = false;
        for (Instruction &I : BB)
        {
            unsigned int opcode = I.getOpcode();
            switch (opcode)
            {
            case Instruction::Ret:
            {
                ret = true;
                break;
            }
            }
        }
        return ret;
    }
    bool CFGPass::isKeyBBs(std::string str)
    {
        if (acl_revoke.find(str) != std::string::npos || acl_check.find(str) != std::string::npos || deliver_to_subscribers.find(str) != std::string::npos || deliver.find(str) != std::string::npos || sub_remove.find(str) != std::string::npos || sub_add.find(str) != std::string::npos)
        {
            return true;
        }
        return false;
    }
    std::string CFGPass::replaceKeyBBsOrEndName(std::string str)
    {
        if (send__pubcomp.find(str) != std::string::npos)
            return "send__pubcomp";
        else if (send__puback.find(str) != std::string::npos)
            return "send__puback";
        else if (send__pubrec.find(str) != std::string::npos)
            return "send__pubrec";
        else if (send__connack.find(str) != std::string::npos)
            return "send__connack";
        else if (send__suback.find(str) != std::string::npos)
            return "send__suback";
        else if (send__unsuback.find(str) != std::string::npos)
            return "send__unsuback";
        else if (acl_revoke.find(str) != std::string::npos)
            return "acl_revoke";
        else if (acl_check.find(str) != std::string::npos)
            return "acl_check";
        else if (deliver_to_subscribers.find(str) != std::string::npos)
            return "deliver_to_subscribers";
        else if (deliver.find(str) != std::string::npos)
            return "deliver";
        else if (sub_remove.find(str) != std::string::npos)
            return "sub_remove";
        else if (sub_add.find(str) != std::string::npos)
            return "sub_add";
        else
            return "ERROR";
    }
    
    int CFGPass::endOfHandler(CallBase *call)
    {
        
        
        
        
        
        // MQTT_RC_SUCCESS = 0,						/
        // MQTT_RC_GRANTED_QOS0 = 0,					/
        // MQTT_RC_GRANTED_QOS1 = 1,					/
        // MQTT_RC_GRANTED_QOS2 = 2,					/
        std::string funcName = "";
        if (call->isIndirectCall() || !(call->getCalledFunction()))
        {
            const GlobalAlias *GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                funcName = GV->getAliasee()->getName().str();
            else
                return 0;
        }
        else
        {
            funcName = call->getCalledFunction()->getName().str();
        }
        if (send__pubcomp.find(funcName) != std::string::npos)
        {
            return 2;
        }
        else if ((send__puback.find(funcName) != std::string::npos || send__pubrec.find(funcName) != std::string::npos))
        {
            return 2;
            
            
            
            
            
            
            
            
            
            
            
            
            
            
        }
        else if (send__connack.find(funcName) != std::string::npos)
        {
            ConstantInt *CI = dyn_cast<ConstantInt>(call->getArgOperand(1));
            if (CI)
            {
                if (CI->getValue().getSExtValue() == 0)
                {
                    return 2;
                }
                else
                    return 1;
            }
            else
            {
                return 1;
            }
        }
        else if (send__suback.find(funcName) != std::string::npos)
        {
            return 2;
        }
        else if (send__unsuback.find(funcName) != std::string::npos)
        {
            return 2;
        }
        else
            return 0;
    }
}
char CFGPass::ID = 0;

static RegisterPass<CFGPass> X("CFG", "CFGPass");

static RegisterStandardPasses Y(PassManagerBuilder::EP_EarlyAsPossible,
                                [](const PassManagerBuilder &Builder, legacy::PassManagerBase &PM)
                                {
                                    PM.add(new CFGPass());
                                });
