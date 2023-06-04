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
#include "llvm/Support/raw_ostream.h"


#include "MQTTactic.h"

using namespace llvm;
using namespace std;
using namespace SVF;

namespace mqttactic {
    // Andersen flow-insensitive pointer analysis
    class PTA {
    public:
        SVFModule* SvfModule;
        SVFIR* Pag;
        Andersen* Ander;
        SVFG* Svfg;

        PTA(llvm::Module& M) {
            this->SvfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
            this->SvfModule->buildSymbolTableInfo();

            // WPAPass *wpa = new WPAPass();
            // wpa->runOnModule(svfModule);

            /// Build Program Assignment Graph (SVFIR)
            SVFIRBuilder builder;
            this->Pag = builder.build(this->SvfModule);

            this->Ander = new Andersen(this->Pag);
            this->Ander->analyze();

            SVFGBuilder svfBuilder;
            // this->Svfg = svfBuilder.buildPTROnlySVFG(this->Ander);
            this->Svfg = svfBuilder.buildFullSVFG(this->Ander);
            // this->Svfg->dump("../tests/Svfg");
        }

        void TraverseOnVFG(KeyVariable* taint_var, llvm::Value* taint_value, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS);
        bool PTAConstraint(KeyVariable* taint_var, llvm::Value* taint_value, VFGNode* vNode);
        int IdentifyOperationType(const Instruction* I, const Value* V, Set<const Value*>& pts_set);
        int IdentifyCallFuncOperation(std::string func_name);
    };
} // namespace mqttactic
#endif