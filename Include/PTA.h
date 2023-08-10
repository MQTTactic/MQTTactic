#ifndef ANDERSEN_PTA
#define ANDERSEN_PTA

#include "Graphs/SVFG.h"
#include "MemoryModel/PointerAnalysisImpl.h"
#include "SVF-FE/Graph2Json.h"
#include "SVF-FE/LLVMUtil.h"
#include "SVF-FE/SVFIRBuilder.h"
#include "Util/Options.h"
#include "Util/SVFBasicTypes.h"
#include "WPA/Andersen.h"
#include "WPA/FlowSensitive.h"
#include "llvm/Support/raw_ostream.h"


#include "MQTTactic.h"

using namespace llvm;
using namespace std;
using namespace SVF;

namespace mqttactic
{
// Andersen flow-insensitive pointer analysis
class PTA
{
public:
    SVFModule*            SvfModule;
    SVFIR*                Pag;
    PointerAnalysis*      Ander;
    SVFG*                 Svfg;
    std::set<std::string> ALLFunctions;

    PTA(llvm::Module& M)
    {
        this->SvfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
        this->SvfModule->buildSymbolTableInfo();

        // WPAPass *wpa = new WPAPass();
        // wpa->runOnModule(svfModule);

        /// Build Program Assignment Graph (SVFIR)
        SVFIRBuilder builder;
        this->Pag = builder.build(this->SvfModule);

        this->Ander = new Andersen(this->Pag);
        this->Ander->analyze();

        SVFGBuilder svfBuilder(true);
        // this->Svfg = svfBuilder.buildPTROnlySVFG(this->Ander);
        this->Svfg = svfBuilder.buildFullSVFG((BVDataPTAImpl*)(this->Ander));
        // this->Svfg->dump("../SVFG");


        std::string   fname;
        std::ifstream infile("../ALLFunctions");
        if (infile.is_open())
        {
            while (!infile.eof())
            {
                std::getline(infile, fname);
                ALLFunctions.insert(fname);
            }
        }
    }

    void TraverseOnVFG(KeyVariable* taint_var, llvm::Value* taint_value, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS);
    bool PTAConstraint(KeyVariable* taint_var, llvm::Value* taint_value, VFGNode* vNode);
    int  IdentifyOperationType(const llvm::Instruction* I, const Value* V, Set<const Value*>& pts_set);
    int  IdentifyCallFuncOperation(std::string func_name);
    // 根据taint_value (session)找出相关的values
    void FindSessionSet(llvm::Value* taint_value, std::set<Value*>& sess_set, std::map<Value*, std::map<Value*, bool>>&);
    // 为每个session value往上查找function call context
    void FindSessionContext(llvm::Value* taint_value, Type* taint_type, std::map<llvm::Value*, std::vector<Function*>>& contexts);
};
}  // namespace mqttactic
#endif
