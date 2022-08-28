#ifndef MQTTACTIC
#define MQTTACTIC

#include <iostream>
#include <set>
#include <vector>
#include <map>
#include <fstream>
#include <math.h>
#include <ranges>
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "CONFIG.h"

namespace mqttactic
{
    typedef std::vector<const llvm::BasicBlock *> KBBContext;

    // sotre the dbg name of each field
    struct NamedField
    {
        llvm::Type *type;
        const llvm::DIType *typeMD;
        std::string fieldName;
        int typeID;
    };

    // store fields' name of a STRUCT
    struct NamedStructType
    {
        llvm::StructType *type;
        const llvm::DIType *typeMD;
        std::string typeName;
        std::vector<NamedField *> fields;
    };

    struct KeyVariable
    {
        std::string name;
        std::string varType;
    };

    struct SemanticKBB
    {
        const llvm::BasicBlock *bb;
        std::vector<const llvm::Value *> values;
        std::vector<KBBContext> contexts;
        int semantics;
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
        WRITE
    };

}

#endif