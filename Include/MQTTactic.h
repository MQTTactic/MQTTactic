#ifndef MQTTACTIC
#define MQTTACTIC

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

namespace mqttactic
{
typedef std::vector<const llvm::BasicBlock*> KBBContext;

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
    const llvm::BasicBlock*           bb;
    std::vector<const llvm::Value*>   values;
    std::vector<KBBContext>           contexts;
    int                               semantics;
    std::map<llvm::Instruction*, int> semantic_inst;
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

}  // namespace mqttactic

#endif