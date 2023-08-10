#ifndef MQTTACTIC
#define MQTTACTIC
#define DEBUG_TYPE "foo"

#include <math.h>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <vector>
#include "CONFIG.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"


using namespace llvm;

namespace mqttactic
{
typedef std::vector<const llvm::BasicBlock*> KBBContext;

static std::string OperationFuncRead[] = {"back", "front", "find", "top", "contain"};
static std::string OperationFuncWrite0[] = {"pop_back", "erase", "pop", "delete", "Remove", "clear", "free", "_ZdlPv"};
static std::string OperationFuncWrite1[] = {"push_back", "insert", "push", "PushBack", "PushFront"};
static std::string OperationDeliver[] = {"send"};


// sotre the dbg name of each field
struct NamedField
{
    llvm::Type*         type;
    const llvm::DIType* typeMD;
    std::string         fieldName;
    int                 typeID;
};

// store fields' name of a STRUCT
struct NamedStructType
{
    llvm::StructType*        type;
    const llvm::DIType*      typeMD;
    std::string              typeName;
    std::vector<NamedField*> fields;
};

struct KeyVariable
{
    std::string name;
    std::string varType;
};

struct SemanticKBB
{
    const llvm::BasicBlock*                       bb;
    std::vector<const llvm::Value*>               values;
    std::vector<KBBContext>                       contexts;
    std::map<std::string, std::vector<Function*>> call_contexts;
    int                                           semantics;
    std::map<llvm::Instruction*, int>             semantic_inst;
};

enum KeyOperation
{
    // read
    READ,
    // write-
    WRITE0,
    // write+
    WRITE1,
    // Unknow write(LINK...)
    WRITE,
    DELIVER
};

class MQTTLLVMUtils
{
public:
    static std::string GetCalledFuncName(Instruction* inst)
    {
        std::string  calledFuncName = "";
        unsigned int opcode = inst->getOpcode();
        switch (opcode)
        {
        case Instruction::Call: {
            CallInst*                              call = static_cast<CallInst*>(inst);
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
            break;
        }

        default:
            break;
        }
        return calledFuncName;
    };
};

}  // namespace mqttactic

#endif
