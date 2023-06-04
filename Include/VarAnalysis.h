#ifndef VARANALYSIS
#define VARANALYSIS

#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "PTA.h"

using namespace llvm;

namespace mqttactic
{

// Mapping the source-code level variables (e.g., mosquitto__subhier::subs) to LLVM IR value
class VarAnalysis
{
public:
    // struct/class type
    std::vector<NamedStructType*> NamedStructTypes;
    // static/global variables
    std::map<std::string, const Metadata*> GlobalVars;
    // {"class:key_var":[Basicblock*, semantics]}
    std::map<KeyVariable*, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>> SemanticKeyBasicBlocks;
    mqttactic::PTA*                                                                    PointerAnalyzer;

    std::vector<mqttactic::KeyVariable*> key_variables;

    VarAnalysis(Module& M)
    {
        this->PointerAnalyzer = new mqttactic::PTA(M);
        DebugInfoFinder* dbgFinder = new DebugInfoFinder();
        dbgFinder->processModule(M);
        std::vector<llvm::StructType*> struct_set;
        struct_set = M.getIdentifiedStructTypes();
        for (std::vector<llvm::StructType*>::iterator sit = struct_set.begin(); sit != struct_set.end(); sit++)
        {
            mqttactic::NamedStructType* named_struct = new mqttactic::NamedStructType();
            NamedStructTypes.push_back(named_struct);
            named_struct->type = (*sit);
            named_struct->typeName = (*sit)->getName().str();
            // dbgs() << named_struct->typeName << "\n";
            for (auto* element_type : (*sit)->elements())
            {
                mqttactic::NamedField* named_field = new mqttactic::NamedField();
                named_field->type = element_type;
                named_field->typeID = element_type->getTypeID();
                named_struct->fields.insert(named_struct->fields.end(), named_field);
                // dbgs() << named_field->typeID << "\n";
            }

            GetStructDbgInfo(M, dbgFinder, named_struct);
        }
        for (auto global_var : dbgFinder->global_variables())
        {
            const auto* GV = global_var->getVariable();
            if (!GV->getLinkageName().empty())
            {
                GlobalVars.insert(std::pair<std::string, const llvm::Metadata*>(GV->getLinkageName().str(), GV));
            }
        }

        std::string              s;
        std::vector<std::string> s_split;

        s = mqttactic::Subs;
        s_split = split(s, "+");
        for (vector<string>::iterator it = s_split.begin(); it != s_split.end(); ++it)
        {
            mqttactic::KeyVariable* kv = new mqttactic::KeyVariable();
            kv->name = *it;
            kv->varType = "LIST:Subs";
            // check if the kv->name is an empty string
            if (kv->name != "")
            {
                this->key_variables.push_back(kv);
            }
        }
        s_split.clear();

        s = mqttactic::WillMsg;
        s_split = split(s, "+");
        for (vector<string>::iterator it = s_split.begin(); it != s_split.end(); ++it)
        {
            mqttactic::KeyVariable* kv = new mqttactic::KeyVariable();
            kv->name = *it;
            kv->varType = "WillMsg";
            if (kv->name != "")
            {
                this->key_variables.push_back(kv);
            }
        }
        s_split.clear();

        s = mqttactic::MsgQue;
        s_split = split(s, "+");
        for (vector<string>::iterator it = s_split.begin(); it != s_split.end(); ++it)
        {
            mqttactic::KeyVariable* kv = new mqttactic::KeyVariable();
            kv->name = *it;
            kv->varType = "LIST:MsgQue";
            if (kv->name != "")
            {
                this->key_variables.push_back(kv);
            }
        }
        s_split.clear();

        s = mqttactic::RetainedMsg;
        s_split = split(s, "+");
        for (vector<string>::iterator it = s_split.begin(); it != s_split.end(); ++it)
        {
            mqttactic::KeyVariable* kv = new mqttactic::KeyVariable();
            kv->name = *it;
            kv->varType = "LIST:RetainedMsg";
            // check if the kv->name is an empty string
            if (kv->name != "")
            {
                this->key_variables.push_back(kv);
            }
        }
        s_split.clear();

        // s = mqttactic::ClientID;
        // s_split = split(s, "+");
        // for (vector<string>::iterator it = s_split.begin(); it != s_split.end();
        // ++it)
        // {
        //     mqttactic::KeyVariable *kv = new mqttactic::KeyVariable();
        //     kv->name = *it;
        //     kv->varType = "ClientID";
        //     this->key_variables.push_back(kv);
        // }
        // s_split.clear();

        // s = mqttactic::MsgID;
        // s_split = split(s, "+");
        // for (vector<string>::iterator it = s_split.begin(); it != s_split.end();
        //     ++it) {
        //     mqttactic::KeyVariable* kv = new mqttactic::KeyVariable();
        //     kv->name = *it;
        //     kv->varType = "MsgID";
        //     this->key_variables.push_back(kv);
        // }

        // s = mqttactic::Permission;
        // s_split = split(s, "+");
        // for (vector<string>::iterator it = s_split.begin(); it != s_split.end();
        // ++it)
        // {
        //     mqttactic::KeyVariable *kv = new mqttactic::KeyVariable();
        //     kv->name = *it;
        //     kv->varType = "Permission";
        //     this->key_variables.push_back(kv);
        // }

        // ------------------------------------------ initiate
        // SemanticKeyBasicBlocks
        for (auto key_var : this->key_variables)
        {
            std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*> sbb_map;
            this->SemanticKeyBasicBlocks.insert(std::pair<KeyVariable*, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>>(key_var, sbb_map));
        }
    }

    vector<string> split(const string& str, const string& delim)
    {
        vector<string> res;
        if ("" == str)
            return res;
        char* strs = new char[str.length() + 1];
        strcpy(strs, str.c_str());

        char* d = new char[delim.length() + 1];
        strcpy(d, delim.c_str());

        char* p = strtok(strs, d);
        while (p)
        {
            string s = p;
            res.push_back(s);
            p = strtok(NULL, d);
        }

        return res;
    }

    void                  PrintDbgInfo();
    const DIType*         GetBasicDIType(const Metadata* MD);
    std::string           GetScope(const DIType* MD);
    void                  GetStructDbgInfo(Module& M, DebugInfoFinder* dbgFinder, NamedStructType* named_struct);
    llvm::GlobalVariable* GetStaticDbgInfo(Module& M, DIDerivedType* static_var);
    void                  SearchKeyVar(Module& M, Function& F);
    bool                  ParseVariables(Value* V, Module& M, const Function& F, std::string key_var);
};
}  // namespace mqttactic

#endif