#include "../../Include/PTA.h"

namespace mqttactic
{
void PTA::TraverseOnVFG(KeyVariable* taint_var, llvm::Value* taint_value, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS)
{
    SVFIR*                       pag = this->Ander->getPAG();
    FIFOWorkList<const VFGNode*> worklist;
    // Contains all the svfg nodes (with context) that are visited
    std::map<const VFGNode*, std::vector<KBBContext>>        svfg_nodes_with_context;
    std::map<const llvm::BasicBlock*, std::set<std::string>> KBB_with_context_str;
    // Contains all the points-to set of the taint_value
    Set<const Value*> pts_set;
    llvm::Type*       taint_value_type = taint_value->getType();

    // dbgs() << "key variable type: " << *taint_value_type << "\n";

    for (auto sbb : SKBBS)
    {
        for (auto v : sbb.second->values)
            pts_set.insert(pts_set.end(), v);
    }

    PAGNode* pNode = pag->getGNode(pag->getValueNode(taint_value));
    if (pNode->hasValue() && pNode->getValue() == taint_value && this->Svfg->hasDefSVFGNode(pNode))
    {
        const VFGNode* vNode = this->Svfg->getDefSVFGNode(pNode);
        // dbgs() << "DefSvfgNode id: " << vNode->getId() << "\n";
        if (vNode->getValue() != nullptr)
        {
            worklist.push(vNode);
            if (svfg_nodes_with_context.find(vNode) == svfg_nodes_with_context.end())
            {
                std::vector<KBBContext> kbb_contexts;
                svfg_nodes_with_context.insert(pair<const VFGNode*, std::vector<KBBContext>>(vNode, kbb_contexts));
            }
            pts_set.insert(vNode->getValue());
            while (!worklist.empty())
            {
                const VFGNode* vNode = worklist.pop();

                // dbgs() << "Value: " << *(vNode->getValue()) << "\n";
                // for (auto node_id : vNode->getDefSVFVars())
                // {
                //     PAGNode *pag_node = pag->getGNode(node_id);
                //     for (auto edge : pag_node->getOutEdges())
                //     {
                //         if (edge->getEdgeKind() == SVFStmt::Addr)
                //             pag_node = edge->getDstNode();
                //     }
                //     // dbgs() << pag_node->getId() << "\n";
                //     if (this->Svfg->hasDefSVFGNode(pag_node))
                //     {
                //         const VFGNode *succNode = this->Svfg->getDefSVFGNode(pag_node);
                //         // dbgs() << *(succNode->getValue()) << "\n";
                //         if (succNode->getValue() && svfg_nodes_with_context.find(succNode) == svfg_nodes_with_context.end())
                //         {
                //             svfg_nodes_with_context.insert(succNode);
                //             worklist.push(succNode);
                //             pts_set.insert(succNode->getValue());
                //         }
                //     }
                // }
                for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit = vNode->OutEdgeEnd(); it != eit; ++it)
                {
                    VFGEdge* edge = *it;
                    VFGNode* succNode = edge->getDstNode();

                    // Don't propagate to the key_operation function defined in "IdentifyCallFuncOperation"
                    if (const CallICFGNode* call_inst = dyn_cast<CallICFGNode>(vNode->getICFGNode()))
                    {
                        const Instruction* I = call_inst->getCallSite();
                        int                op_type = IdentifyOperationType(I, vNode->getValue(), pts_set);
                        if (op_type != -1)
                            break;
                    }

                    // if (edge->isCallVFGEdge())
                    // {
                    //     vfCond = ComputeInterCallVFGGuard(nodeBB, succBB, getCallSite(edge)->getParent());
                    // }
                    // else if (edge->isRetVFGEdge())
                    // {
                    //     vfCond = ComputeInterRetVFGGuard(nodeBB, succBB, getRetSite(edge)->getParent());
                    // }
                    // else
                    //     vfCond = ComputeIntraVFGGuard(nodeBB, succBB);

                    // SVFUtil::errs() << "src: " << *vNode << "\n"
                    //     << "dst: " << *succNode << "\n";

                    // MA node
                    if (succNode->getValue() == nullptr)
                    {
                        // ignore other memory region node: FPIN/FPOUT/APIN/APOUT/MPhi/MInterPhi
                        if (!(succNode->getNodeKind() == VFGNode::MIntraPhi) || (succNode->getNodeKind() == VFGNode::MIntraPhi && vNode->getNodeKind() == VFGNode::MIntraPhi))
                            continue;
                    }
                    // stmt node/param node
                    else
                    {
                        // 1. Decrease SemanticKeyBasicBlocks number: with SVFG propagation constraints
                        if (!PTAConstraint(taint_var, taint_value, succNode))
                        {
                            continue;
                        }
                        // else {
                        //     dbgs() << "Matched value: " << *(succNode->getValue()) << "\n";
                        // }
                    }

                    // Add the succNode to the svfg_nodes_with_context
                    if (svfg_nodes_with_context.find(succNode) == svfg_nodes_with_context.end())
                    {
                        if (svfg_nodes_with_context.find(vNode) == svfg_nodes_with_context.end())
                        {
                            llvm::errs() << "[ERROR]: can not find the source svfg node\n";
                            continue;
                        }
                        std::vector<KBBContext> kbb_contexts;

                        if (vNode->getNodeKind() != VFGNode::Addr)
                            kbb_contexts = std::vector<KBBContext>(svfg_nodes_with_context[vNode]);
                        if (kbb_contexts.size() == 0)
                        {
                            KBBContext kbb_c;
                            kbb_contexts.push_back(kbb_c);
                        }
                        if (vNode->getNodeKind() != VFGNode::Addr)
                        {
                            const llvm::BasicBlock* bb = vNode->getICFGNode()->getBB();
                            // context represent the condition of succNode. so if src_bb == dest_bb, we skip the insertion
                            if (bb != succNode->getICFGNode()->getBB())
                                for (auto kbb_c = kbb_contexts.begin(); kbb_c != kbb_contexts.end(); kbb_c++)
                                {
                                    if (find((*kbb_c).begin(), (*kbb_c).end(), bb) == (*kbb_c).end())
                                        (*kbb_c).push_back(bb);
                                }
                        }
                        else
                        {
                            kbb_contexts.clear();
                        }
                        svfg_nodes_with_context.insert(pair<const VFGNode*, std::vector<KBBContext>>(succNode, kbb_contexts));
                        worklist.push(succNode);
                        if (succNode->getValue() && StmtVFGNode::classof(succNode) && pts_set.find(succNode->getValue()) == pts_set.end())
                            pts_set.insert(succNode->getValue());
                    }
                    // else: if the succNode is already in the svfg_nodes_with_context, we only need to add the new context
                    else
                    {
                        if (svfg_nodes_with_context.find(vNode) == svfg_nodes_with_context.end())
                        {
                            llvm::errs() << "[ERROR]: can not find the source svfg node\n";
                            continue;
                        }
                        std::vector<KBBContext> kbb_contexts;

                        if (vNode->getNodeKind() != VFGNode::Addr)
                            kbb_contexts = std::vector<KBBContext>(svfg_nodes_with_context[vNode]);
                        if (kbb_contexts.size() == 0)
                        {
                            KBBContext kbb_c;
                            kbb_contexts.push_back(kbb_c);
                        }
                        if (vNode->getNodeKind() != VFGNode::Addr)
                        {
                            const llvm::BasicBlock* bb = vNode->getICFGNode()->getBB();
                            if (bb != succNode->getICFGNode()->getBB())
                            {
                                for (auto kbb_c = kbb_contexts.begin(); kbb_c != kbb_contexts.end(); kbb_c++)
                                {
                                    if (find((*kbb_c).begin(), (*kbb_c).end(), bb) == (*kbb_c).end())
                                        (*kbb_c).push_back(bb);
                                    svfg_nodes_with_context[succNode].push_back(*kbb_c);
                                }
                            }
                        }
                        else
                        {
                            svfg_nodes_with_context[succNode].clear();
                        }
                    }
                }
            }

            // Get the KBBs and semantics
            for (auto vit = svfg_nodes_with_context.begin(); vit != svfg_nodes_with_context.end(); vit++)
            {
                if (vit->first->getValue() && (StmtVFGNode::classof(vit->first) || ArgumentVFGNode::classof(vit->first)))
                {
                    const Instruction* I;
                    int                op_type = 0;
                    std::string        Str;
                    raw_string_ostream OS(Str);
                    vit->first->getValue()->printAsOperand(OS, false);

                    if (const IntraICFGNode* inst = dyn_cast<IntraICFGNode>((vit->first)->getICFGNode()))
                    {
                        I = inst->getInst();
                        op_type = IdentifyOperationType(I, (vit->first)->getValue(), pts_set);

                        // dbgs()
                        //     << "Value: " << OS.str()
                        //     << "Type: " << op_type << "      " << *I << "\n";
                    }
                    else if (const CallICFGNode* call_inst = dyn_cast<CallICFGNode>((vit->first)->getICFGNode()))
                    {
                        I = call_inst->getCallSite();
                        op_type = IdentifyOperationType(I, (vit->first)->getValue(), pts_set);
                        // dbgs() << "Value: " << OS.str() << "      " << *I << "\n";
                    }

                    if (op_type == -1)
                        op_type = KeyOperation::READ;

                    const llvm::BasicBlock* bb = (vit->first)->getICFGNode()->getBB();

                    if (SKBBS.find(bb) == SKBBS.end())
                    {
                        SemanticKBB* sbb = new SemanticKBB();
                        sbb->bb = bb;
                        sbb->values.push_back((vit->first)->getValue());
                        sbb->semantics = op_type;
                        sbb->semantic_inst.insert(std::map<llvm::Instruction*, int>::value_type(const_cast<llvm::Instruction*>(I), op_type));

                        std::set<std::string> context_str;
                        KBB_with_context_str.insert(pair<const llvm::BasicBlock*, std::set<std::string>>(bb, context_str));
                        for (auto kbb_c : vit->second)
                        {
                            std::string h = "";
                            for (const llvm::BasicBlock* b : kbb_c)
                            {
                                std::stringstream ss;
                                ss << (void*)b;
                                h += ss.str() + " --> ";
                            }
                            if (KBB_with_context_str[bb].find(h) == KBB_with_context_str[bb].end())
                            {
                                sbb->contexts.push_back(kbb_c);
                                KBB_with_context_str[bb].insert(KBB_with_context_str[bb].end(), h);
                            }
                        }

                        SKBBS.insert(std::pair<const llvm::BasicBlock*, mqttactic::SemanticKBB*>(bb, sbb));
                    }
                    else
                    {
                        mqttactic::SemanticKBB* sbb = SKBBS[bb];
                        sbb->values.push_back((vit->first)->getValue());
                        sbb->semantics |= op_type;
                        sbb->semantic_inst.insert(std::map<llvm::Instruction*, int>::value_type(const_cast<llvm::Instruction*>(I), op_type));
                        for (auto kbb_c : vit->second)
                        {
                            std::string h = "";
                            for (const llvm::BasicBlock* b : kbb_c)
                            {
                                std::stringstream ss;
                                ss << (void*)b;
                                h += ss.str() + " --> ";
                            }
                            if (KBB_with_context_str[bb].find(h) == KBB_with_context_str[bb].end())
                            {
                                sbb->contexts.push_back(kbb_c);
                                KBB_with_context_str[bb].insert(KBB_with_context_str[bb].end(), h);
                            }
                        }
                    }
                }
            }
            worklist.clear();
            svfg_nodes_with_context.clear();
        }
    }
}

// return false: the vNode should not be added to the worklist
bool PTA::PTAConstraint(KeyVariable* taint_var, llvm::Value* taint_value, VFGNode* vNode)
{
    bool        ret = false;
    llvm::Type* taint_value_type = taint_value->getType();
    // LIST or Array type variable
    if (taint_var->varType.find("LIST") == 0)
    {
        // ALLOW: list->next/prev, array[1], ...
        // DENY: list->other_value
        if (vNode->getNodeKind() == VFGNode::Gep)
        {
            bool _source = false;
            bool _result = false;
            if (const GEPOperator* GEP = dyn_cast<GEPOperator>(vNode->getValue()))
            {
                // check source element type == taint_value_type
                if (GEP->getSourceElementType() == taint_value_type)
                    _source = true;
                else
                {
                    llvm::Type* ty = taint_value_type;
                    while (PointerType* base_type = dyn_cast<PointerType>(ty))
                    {
                        if (!(base_type->isOpaque()))
                            ty = base_type->getElementType();

                        if (GEP->getSourceElementType() == ty)
                            _source = true;
                    }
                }
                // check result element type == taint_value_type
                if (_source)
                {
                    if (GEP->getResultElementType() == taint_value_type)
                        _result = true;
                    else
                    {
                        llvm::Type* ty = taint_value_type;
                        while (PointerType* base_type = dyn_cast<PointerType>(ty))
                        {
                            if (!(base_type->isOpaque()))
                                ty = base_type->getElementType();

                            if (GEP->getResultElementType() == ty)
                                _result = true;
                        }
                    }
                }
                if (_result)
                    ret = true;
            }
        }
        else
            ret = true;
    }
    else
    {
        // ALLOW: Session->clientID
        // DENY: Session->clientID->other_value
        if (vNode->getNodeKind() == VFGNode::Gep)
        {
            if (const GEPOperator* GEP = dyn_cast<GEPOperator>(vNode->getValue()))
            {
                // check source element type == taint_value_type
                if (GEP->getSourceElementType() == taint_value_type)
                    ret = true;
                else
                {
                    llvm::Type* ty = taint_value_type;
                    while (PointerType* base_type = dyn_cast<PointerType>(ty))
                    {
                        if (!(base_type->isOpaque()))
                            ty = base_type->getElementType();

                        if (GEP->getSourceElementType() == ty)
                            ret = true;
                    }
                }
            }
            else
                ret = true;
        }
        else
            ret = true;
    }

    return ret;
}

int PTA::IdentifyOperationType(const Instruction* I, const Value* V, Set<const Value*>& pts_set)
{
    unsigned int opcode = I->getOpcode();
    switch (opcode)
    {
    case Instruction::Call: {
        const CallInst* call = static_cast<const CallInst*>(I);
        std::string     calledFuncName = "";
        if (call->isIndirectCall() || !(call->getCalledFunction()))
        {
            const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                calledFuncName = GV->getAliasee()->getName().str();
            else
                break;
        }
        else
        {
            calledFuncName = call->getCalledFunction()->getName().str();
        }

        if (call->getArgOperand(0) == V && calledFuncName != "")
        {
            int op_type = IdentifyCallFuncOperation(calledFuncName);
            return op_type;
        }

        break;
    }
    case Instruction::Invoke: {
        const InvokeInst* call = static_cast<const InvokeInst*>(I);
        std::string       calledFuncName = "";
        if (call->isIndirectCall() || !(call->getCalledFunction()))
        {
            const GlobalAlias* GV = dyn_cast<GlobalAlias>(call->getCalledOperand());
            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                calledFuncName = GV->getAliasee()->getName().str();
            else
                break;
        }
        else
        {
            calledFuncName = call->getCalledFunction()->getName().str();
        }
        if (call->getArgOperand(0) == V && calledFuncName != "")
        {
            int op_type = IdentifyCallFuncOperation(calledFuncName);
            return op_type;
        }
        break;
    }
    case Instruction::Store: {
        const StoreInst* store = static_cast<const StoreInst*>(I);
        // If the value is the rvalue of the `store` instruction
        Value* RightV = store->getOperand(1);
        Value* leftV = store->getOperand(0);

        if (pts_set.find(RightV) != pts_set.end())
        {
            // Link w- operation or store null
            if (llvm::ConstantPointerNull::classof(leftV) || pts_set.find(leftV) != pts_set.end())
            {
                return KeyOperation::WRITE;
            }
            else
            {
                // dbgs() << "store: " << *leftV << "----" << *RightV << "\n";
                return KeyOperation::WRITE1;
            }
        }
        break;
    }
    default:
        break;
    }

    return -1;
}

// Identify operation type of STL function. e.g., vector::push_back
int PTA::IdentifyCallFuncOperation(std::string func_name)
{
    std::string OperationFuncRead[] = {"back", "front", "find", "top", "contain"};
    std::string OperationFuncWrite0[] = {"pop_back", "erase", "pop", "delete", "Remove", "clear", "free", "_ZdlPv"};
    std::string OperationFuncWrite1[] = {"push_back", "insert", "push", "PushBack", "PushFront"};

    std::string pos = "";
    int         op_type = -1;

    for (auto op : OperationFuncRead)
    {
        if (func_name.find(op) != std::string::npos)
        {
            pos = op;
            op_type = mqttactic::READ;
            break;
        }
    }
    for (auto op : OperationFuncWrite0)
    {
        if (func_name.find(op) != std::string::npos)
        {
            if (pos.size() < op.size())
                pos = op;
            op_type = mqttactic::WRITE0;
            break;
        }
    }
    for (auto op : OperationFuncWrite1)
    {
        if (func_name.find(op) != std::string::npos)
        {
            if (pos.size() < op.size())
                pos = op;
            op_type = mqttactic::WRITE1;
            break;
        }
    }

    if (func_name == "write")
    {
        op_type = mqttactic::WRITE;
    }

    return op_type;
}
}  // namespace mqttactic