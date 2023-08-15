#include "PTA.h"

namespace mqttactic
{

void PTA::GetPtsTo(PAGNode* p_node)
{
    SVFIR* pag = this->Ander->getPAG();
    if (pag->isValidTopLevelPtr(p_node))
    {
        const PointsTo& pts = this->Ander->getPts(p_node->getId());
        if (!pts.empty())
        {
            dbgs() << "\t\tPointsTo: { ";
            for (PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit; ++it)
            {
                NodeID   id = *it;
                VFGNode* vNode = this->Svfg->getSVFGNode(id);
                SVFUtil::errs() << *vNode << "\n";
            }
            dbgs() << "}\n\n";
        }
    }
}

void PTA::FindSessionSet(llvm::Value* taint_value, std::set<Value*>& sess_set, std::map<Value*, std::map<Value*, bool>>& sess_graph)
{
    SVFIR*                       pag = this->Ander->getPAG();
    FIFOWorkList<const VFGNode*> worklist;
    std::set<const VFGNode*>     complete_worklist;

    PAGNode* pNode = pag->getGNode(pag->getValueNode(taint_value));
    if (pNode->hasValue() && pNode->getValue() == taint_value)
    {
        const VFGNode* vNode = this->Svfg->getDefSVFGNode(pNode);
        if (vNode->getValue() != nullptr)
        {
            worklist.push(vNode);
            while (!worklist.empty())
            {
                const VFGNode* vNode = worklist.pop();
                Value*         _v = const_cast<Value*>(vNode->getValue());

                sess_set.insert(_v);
                complete_worklist.insert(vNode);

                for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit = vNode->OutEdgeEnd(); it != eit; ++it)
                {
                    VFGEdge*    edge = *it;
                    VFGNode*    succNode = edge->getDstNode();
                    std::string calledFuncName = "";

                    if (const CallICFGNode* call_inst = dyn_cast<CallICFGNode>(vNode->getICFGNode()))
                    {
                        const llvm::Instruction* I = call_inst->getCallSite();
                        std::string              calledFuncName = MQTTLLVMUtils::GetCalledFuncName(const_cast<Instruction*>(I));

                        if (ALLFunctions.find(calledFuncName) == ALLFunctions.end())
                            continue;
                    }
                    // MA node
                    if (succNode->getValue() == nullptr)
                    {
                        // ignore other memory region node: FPIN/FPOUT/APIN/APOUT/MPhi/MInterPhi
                        if (!(succNode->getNodeKind() == VFGNode::MIntraPhi) || (succNode->getNodeKind() == VFGNode::MIntraPhi && vNode->getNodeKind() == VFGNode::MIntraPhi))
                            continue;
                    }

                    if (complete_worklist.find(succNode) == complete_worklist.end())
                        worklist.push(succNode);
                    if (succNode->getValue() != nullptr && _v != nullptr)
                    {
                        Value* succ_value = const_cast<Value*>(succNode->getValue());
                        if (sess_graph.find(_v) == sess_graph.end())
                        {
                            std::map<llvm::Value*, bool> _y;
                            sess_graph.insert(std::map<llvm::Value*, std::map<llvm::Value*, bool>>::value_type(_v, _y));
                        }
                        if (sess_graph.find(succ_value) == sess_graph.end())
                        {
                            std::map<llvm::Value*, bool> _y;
                            sess_graph.insert(std::map<llvm::Value*, std::map<llvm::Value*, bool>>::value_type(succ_value, _y));
                        }
                        sess_graph[_v][succ_value] = true;
                        sess_graph[succ_value][_v] = true;
                    }
                }
            }
        }
    }
}

void PTA::FindSessionContext(llvm::Value* taint_value, Type* taint_type, std::map<llvm::Value*, std::vector<Function*>>& contexts)
{
    SVFIR*                                             pag = this->Ander->getPAG();
    std::vector<const VFGNode*>                        worklist;
    std::set<const VFGNode*>                           complete_worklist;
    std::map<const VFGNode*, std::set<const VFGNode*>> vNode_succs;
    PAGNode*                                           pNode = pag->getGNode(pag->getValueNode(taint_value));
    std::vector<const VFGNode*>                        path;


    if (pNode->hasValue() && pNode->getValue() == taint_value)
    {
        // 1. 通过taint_value(一般为socket, 存储于session内) 找到 session类型的vNode
        const VFGNode* taint_Node = this->Svfg->getDefSVFGNode(pNode);
        worklist.push_back(taint_Node);

        while (!worklist.empty())
        {
            const VFGNode* vNode = worklist.back();
            worklist.pop_back();
            const Value* _v = vNode->getValue();
            if (_v != nullptr)
            {
                bool        is_sess_var = false;
                llvm::Type* ty = _v->getType();
                if (ty == taint_type)
                    is_sess_var = true;
                else
                {
                    while (PointerType* base_type = dyn_cast<PointerType>(ty))
                    {
                        if (!(base_type->isOpaque()))
                            ty = base_type->getElementType();

                        if (taint_type == ty)
                            is_sess_var = true;
                    }
                }
                if (is_sess_var)
                {
                    taint_Node = vNode;
                    break;
                }
            }
            for (VFGNode::const_iterator it = vNode->InEdgeBegin(), eit = vNode->InEdgeEnd(); it != eit; ++it)
            {
                VFGEdge* edge = *it;
                VFGNode* succNode = edge->getSrcNode();

                if (succNode->getValue() == nullptr)
                {
                    // ignore other memory region node: FPIN/FPOUT/APIN/APOUT/MPhi/MInterPhi
                    if (!(succNode->getNodeKind() == VFGNode::MIntraPhi) || (succNode->getNodeKind() == VFGNode::MIntraPhi && vNode->getNodeKind() == VFGNode::MIntraPhi))
                        continue;
                }

                vNode_succs[vNode].insert(succNode);
                worklist.push_back(succNode);
            }
        }

        // 2. 寻找指定session value的callsite context
        worklist.clear();
        worklist.push_back(taint_Node);
        while (!worklist.empty())
        {
            const VFGNode* vNode = worklist.back();
            Function*      func = nullptr;
            worklist.pop_back();

            if (path.size() > 0)
            {
                const VFGNode* _last = path.back();
                if (vNode_succs.find(_last) != vNode_succs.end())
                {
                    while (vNode_succs[_last].find(vNode) == vNode_succs[_last].end())
                    {
                        path.pop_back();
                        _last = path.back();
                    }
                }
            }
            path.push_back(vNode);
            complete_worklist.insert(vNode);

            int succ_count = 0;

            if (vNode->getICFGNode()->getBB() != nullptr)
                func = const_cast<llvm::Function*>(vNode->getICFGNode()->getBB()->getParent());
            else if (vNode->getFun() != nullptr)
                func = vNode->getFun()->getLLVMFun();

            if (func != nullptr)
            {
                string _s = func->getName().str();
                if (_s == mqttactic::handle__connect || _s == mqttactic::handle__publish || _s == mqttactic::handle__pubrel || _s == mqttactic::handle__subscribe || _s == mqttactic::handle__unsubscribe || _s == mqttactic::handle__disconnect)
                {
                    goto FINDTHEBEGIN;
                }
            }

            for (VFGNode::const_iterator it = vNode->InEdgeBegin(), eit = vNode->InEdgeEnd(); it != eit; ++it)
            {
                VFGEdge* edge = *it;
                VFGNode* succNode = edge->getSrcNode();

                if (succNode->getValue() == nullptr)
                {
                    // ignore other memory region node: FPIN/FPOUT/APIN/APOUT/MPhi/MInterPhi
                    if (!(succNode->getNodeKind() == VFGNode::MIntraPhi) || (succNode->getNodeKind() == VFGNode::MIntraPhi && vNode->getNodeKind() == VFGNode::MIntraPhi))
                        continue;
                }
                else if (succNode->getNodeKind() == VFGNode::Addr)
                {
                    continue;
                }

                //[TODO]: 还是需要记录已经访问过的context
                if (complete_worklist.find(succNode) == complete_worklist.end() && std::find(worklist.begin(), worklist.end(), succNode) == worklist.end())
                {
                    vNode_succs[vNode].insert(succNode);
                    succ_count++;
                    worklist.push_back(succNode);
                    // SVFUtil::errs() << "PUSH:" << *succNode << "\n";
                }
            }

            // SVFUtil::errs() << *vNode << ":\n";
            // for (auto test : path)
            // {
            //     SVFUtil::errs() << "->" << test->getId();
            // }
            // dbgs() << "\n\n";

        FINDTHEBEGIN:
            if (succ_count == 0)
            {
                if (vNode->getValue() != nullptr)
                {
                    std::vector<Function*> call_stack;
                    Function*              func = nullptr;
                    for (auto bbit = path.rbegin(); bbit != path.rend(); ++bbit)
                    {
                        if ((*bbit)->getICFGNode()->getBB() != nullptr)
                            func = const_cast<llvm::Function*>((*bbit)->getICFGNode()->getBB()->getParent());
                        else if ((*bbit)->getFun() != nullptr)
                            func = (*bbit)->getFun()->getLLVMFun();

                        // Some vfg node have no function, e.g.,  @db = dso_local global %struct.mosquitto_db zeroinitializer, align 8, !dbg !761 { Glob ln: 59 fl: mosquitto.c }
                        if (func == nullptr)
                        {
                            // SVFUtil::errs() << "[ERROR]: " << *(*bbit) << "\n";
                            continue;
                        }
                        if (call_stack.size() == 0 || (call_stack.size() > 0 && func != call_stack.back()))
                            call_stack.push_back(func);
                    }
                    contexts[const_cast<llvm::Value*>(vNode->getValue())] = call_stack;
                }
                path.pop_back();
            }
        }
    }
}


void PTA::TraverseOnVFG(KeyVariable* taint_var, llvm::Value* taint_value, std::map<const llvm::BasicBlock*, mqttactic::SemanticKBB*>& SKBBS)
{
    SVFIR*                      pag = this->Ander->getPAG();
    std::vector<const VFGNode*> worklist;
    // Contains all the svfg nodes (with context) that are visited
    std::map<const VFGNode*, std::vector<KBBContext>>        svfg_nodes_with_context;
    std::map<const llvm::BasicBlock*, std::set<std::string>> KBB_with_context_str;
    // 记录所有遍历的vNode以及其后继节点
    std::map<const VFGNode*, std::set<const VFGNode*>> vNode_succs;
    std::vector<const VFGNode*>                        vNode_path;
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
    if (pNode->hasValue() && pNode->getValue() == taint_value)
    {
        const VFGNode* vNode = this->Svfg->getDefSVFGNode(pNode);
        // dbgs() << "DefSvfgNode id: " << vNode->getId() << "\n";
        if (vNode->getValue() != nullptr)
        {
            worklist.push_back(vNode);
            if (svfg_nodes_with_context.find(vNode) == svfg_nodes_with_context.end())
            {
                std::vector<KBBContext> kbb_contexts;
                svfg_nodes_with_context.insert(pair<const VFGNode*, std::vector<KBBContext>>(vNode, kbb_contexts));
            }
            pts_set.insert(vNode->getValue());
            while (!worklist.empty())
            {
                const VFGNode* vNode = worklist.back();
                worklist.pop_back();

                for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit = vNode->OutEdgeEnd(); it != eit; ++it)
                {
                    VFGEdge* edge = *it;
                    VFGNode* succNode = edge->getDstNode();
                    vNode_succs[vNode].insert(succNode);
                }

                // 如果一个节点所有后继节点都遍历完了
                if (vNode_path.size() > 0)
                {
                    const VFGNode* _last = vNode_path.back();
                    if (vNode_succs.find(_last) != vNode_succs.end())
                    {
                        while (vNode_succs[_last].find(vNode) == vNode_succs[_last].end())
                        {
                            vNode_path.pop_back();
                            _last = vNode_path.back();
                        }
                    }
                }
                vNode_path.push_back(vNode);
                // for (auto vv : vNode_path)
                // {
                //     dbgs() << vv->getId() << "->";
                // }
                // dbgs() << "\n";
                // for (auto succs : vNode_succs[vNode])
                // {
                //     dbgs() << succs->getId() << ",";
                // }
                // dbgs() << "\n";

                if (vNode_succs[vNode].size() == 0)
                    vNode_path.pop_back();

                for (const VFGNode* succNode : vNode_succs[vNode])
                {

                    // Don't propagate to the key_operation function defined in "IdentifyCallFuncOperation"
                    if (MRSVFGNode::classof(vNode) == false)
                        if (const CallICFGNode* call_inst = dyn_cast<CallICFGNode>(vNode->getICFGNode()))
                        {
                            const llvm::Instruction* I = call_inst->getCallSite();
                            int                      op_type = IdentifyOperationType(I, vNode->getValue(), pts_set);
                            if (op_type != -1)
                                break;
                        }

                    // if (taint_var->varType == "Msg")
                    // {
                    //     SVFUtil::errs() << "src: " << *vNode << "\n"
                    //                     << "dst: " << *succNode << "\n";
                    // }


                    // MR node
                    if (succNode->getValue() == nullptr)
                    {
                        // ignore other memory region node: FPIN/FPOUT/APIN/APOUT/MPhi/MInterPhi
                        if (!(succNode->getNodeKind() == VFGNode::MIntraPhi) || (succNode->getNodeKind() == VFGNode::MIntraPhi && vNode->getNodeKind() == VFGNode::MIntraPhi))
                        {
                            // [TODO]: 会导致重复的KBB太多
                            if (taint_var->varType == "Msg")
                            {
                                if ((succNode->getNodeKind() == VFGNode::FPIN) || (succNode->getNodeKind() == VFGNode::APIN))
                                {
                                }
                                else if ((succNode->getNodeKind() == VFGNode::FPOUT) || (succNode->getNodeKind() == VFGNode::APOUT))
                                {
                                }
                                else
                                    continue;
                            }
                            else
                                continue;
                        }
                    }
                    // stmt node/param node
                    else
                    {
                        // 1. Decrease SemanticKeyBasicBlocks number: with SVFG propagation constraints
                        if (!PTAConstraint(taint_var, taint_value, succNode))
                        {
                            continue;
                        }
                    }

                    // 保证一个函数被多次调用时，APOUT Node不会继续向别的位置遍历
                    if (succNode->getNodeKind() == VFGNode::APOUT || succNode->getNodeKind() == VFGNode::ARet)
                    {
                        const VFGNode* prev_Aparam = nullptr;
                        for (auto vnodeit = vNode_path.rbegin(); vnodeit != vNode_path.rend(); ++vnodeit)
                        {
                            const VFGNode* vn = *vnodeit;
                            if (vn && vn->getNodeKind() == VFGNode::AParm)
                            {
                                prev_Aparam = vn;
                                break;
                            }
                        }
                        if (prev_Aparam && succNode->getFun() != prev_Aparam->getFun())
                            continue;
                        // [TODO]: 那些没有经过Aparam节点的路径， 不能直接删除
                        // else if (prev_Aparam == nullptr)
                        // {
                        //     continue;
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
                            if (!(vNode->getNodeKind() == VFGNode::FPIN || vNode->getNodeKind() == VFGNode::FPOUT || vNode->getNodeKind() == VFGNode::APIN || vNode->getNodeKind() == VFGNode::APOUT))
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
                        }
                        else
                        {
                            kbb_contexts.clear();
                        }
                        svfg_nodes_with_context.insert(pair<const VFGNode*, std::vector<KBBContext>>(succNode, kbb_contexts));
                        worklist.push_back(succNode);
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
                        if (vNode->getNodeKind() == VFGNode::FPIN || vNode->getNodeKind() == VFGNode::FPOUT || vNode->getNodeKind() == VFGNode::APIN || vNode->getNodeKind() == VFGNode::APOUT)
                        {
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
                            if (!(vNode->getNodeKind() == VFGNode::FPIN || vNode->getNodeKind() == VFGNode::FPOUT || vNode->getNodeKind() == VFGNode::APIN || vNode->getNodeKind() == VFGNode::APOUT))
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
                    const llvm::Instruction* I;
                    int                      op_type = 0;
                    std::string              Str;
                    raw_string_ostream       OS(Str);
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


                    // [TODO]: 暂时只关注deliver里的msg变量以及msg的定义的位置（用于检查是否是其他的send_connack等）
                    if (taint_var->varType == "Msg" && op_type != KeyOperation::DELIVER)
                        continue;


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
bool PTA::PTAConstraint(KeyVariable* taint_var, llvm::Value* taint_value, const VFGNode* vNode)
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

int PTA::IdentifyOperationType(const llvm::Instruction* I, const Value* V, Set<const Value*>& pts_set)
{
    unsigned int opcode = I->getOpcode();
    switch (opcode)
    {
    case Instruction::Call: {
        const CallInst* call = static_cast<const CallInst*>(I);
        std::string     calledFuncName = "";
        if (call->isIndirectCall() || !(call->getCalledFunction()))
        {
            const llvm::GlobalAlias* GV = dyn_cast<llvm::GlobalAlias>(call->getCalledOperand());
            if (GV && GV->getAliasee() && GV->getAliasee()->hasName())
                calledFuncName = GV->getAliasee()->getName().str();
            else
                break;
        }
        else
        {
            calledFuncName = call->getCalledFunction()->getName().str();
        }

        // e.g., obj->push_back()
        if (call->getArgOperand(0) == V && calledFuncName != "")
        {
            int op_type = IdentifyCallFuncOperation(calledFuncName);
            return op_type;
        }
        // For DELIVER： e.g., send(msg)
        else
        {
            for (int s = 0; s < call->arg_size(); s++)
            {
                if (call->getArgOperand(s) == V && calledFuncName != "")
                {
                    int op_type = -1;
                    for (auto op : mqttactic::OperationDeliver)
                    {
                        if (calledFuncName == op)
                        {
                            op_type = mqttactic::DELIVER;
                            break;
                        }
                    }
                    return op_type;
                }
            }
        }

        break;
    }
    case Instruction::Invoke: {
        const InvokeInst* call = static_cast<const InvokeInst*>(I);
        std::string       calledFuncName = "";
        if (call->isIndirectCall() || !(call->getCalledFunction()))
        {
            const llvm::GlobalAlias* GV = dyn_cast<llvm::GlobalAlias>(call->getCalledOperand());
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
        else
        {
            for (int s = 0; s < call->arg_size(); s++)
            {
                if (call->getArgOperand(s) == V && calledFuncName != "")
                {
                    int op_type = -1;
                    for (auto op : mqttactic::OperationDeliver)
                    {
                        if (calledFuncName == op)
                        {
                            op_type = mqttactic::DELIVER;
                            break;
                        }
                    }
                    return op_type;
                }
            }
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
            // [TODO] 完善operation type的类型判断
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

    std::string pos = "";
    int         op_type = -1;

    for (auto op : mqttactic::OperationFuncRead)
    {
        if (func_name.find(op) != std::string::npos)
        {
            pos = op;
            op_type = mqttactic::READ;
            break;
        }
    }
    for (auto op : mqttactic::OperationFuncWrite0)
    {
        if (func_name.find(op) != std::string::npos)
        {
            if (pos.size() < op.size())
                pos = op;
            op_type = mqttactic::WRITE0;
            break;
        }
    }
    for (auto op : mqttactic::OperationFuncWrite1)
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
