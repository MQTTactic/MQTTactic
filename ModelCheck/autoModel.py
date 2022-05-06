import re
import os
import sys
import pathTypes
from termcolor import *
BASE_DIR = os.path.dirname(os.path.abspath(__file__))  
sys.path.append(BASE_DIR + "/../")
from Include.CONFIG import config
path_types = pathTypes.pathTypes
broker_config = {
    "acl_check_pattern": config["acl_check_pattern"],
    "authorization_pub": config["authorization_pub"],
    "authorization_sub": config["authorization_sub"],
    "authorization_read": config["authorization_read"],
    "authorization_store": config["authorization_store"],
    "authorization_load": config["authorization_load"],
    "will": "removeQueuedClients",
    "handle__connect_end": "send__connack-----",
    "handle__publish_qos1_end": "send__puback-----",
    "handle__publish_qos2_end": "send__pubrec-----",
    "handle__pubrel_end": "send__pubcomp-----",
    "handle__subscribe_end": "send__suback-----",
    "handle__unsubscribe_end": "send__unsuback-----",
    "acl_check": "acl_check-----",
    "deliver_to_subscribers": "deliver_to_subscribers-----",
    "deliver": "deliver-----",
    "sub_add": "sub_add-----",
    "sub_remove": "sub_remove-----",
    "acl_revoke": "acl_revoke-----",
}
class Model:
    def __init__(self, broker_name, basemodel_file, output_file):
        self.broker_name = broker_name
        self.config = broker_config
        self.label = 0
        self.source_code = []
        self.source_code_funcs = {}
        self.paths = {}
        self.param = {
            'handle__publish_qos0': 'index, t',
            'handle__publish_qos1': 'index, t',
            'handle__publish_qos2': 'index, t',
            'handle__publish_qos0_retained': 'index, t',
            'handle__pubrel': 'index',
            'handle__subscribe': 'index, t',
            'handle__connect_cleanStartT': 'index',
            'handle__connect_cleanStartF': 'index',
            'handle__disconnect': 'index',
            'handle__unsubscribe': 'index, t',
            'ACL_revoke': 'index, revokeAcl'
        }
        self.output = open(output_file, 'w', encoding='utf-8')
        with open(basemodel_file, encoding='utf-8') as f:
            handler_begin_idx = 0
            handler_end_idx = 0
            handler = ''
            while (True):
                line = f.readline()
                if (line != ''):
                    self.source_code.append(line)
                    if (re.search('/\*\*+?[ \w]+\*+?\*/', line)):
                        handler_end_idx = len(self.source_code) - 1
                        if (handler != ''):
                            handler(handler_begin_idx, handler_end_idx)
                        handler_begin_idx = 0
                        handler_end_idx = 0
                        handler = ''
                    if (re.search('/\*+? (PUBLISH) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandlePublish
                    elif (re.search('/\*+? (PUBREL) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandlePubrel
                    elif (re.search('/\*+? (CONNECT) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandleConnect
                    elif (re.search('/\*+? (SUBSCRIBE) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandleSubscribe
                    elif (re.search('/\*+? (DISCONNECT) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandleDisconnect
                    elif (re.search('/\*+? (UNSUBSCRIBE) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseHandleUnSubscribe
                    elif (re.search('/\*+? (ACL revoke) \*+?/', line)):
                        handler_begin_idx = len(self.source_code)
                        handler = self.BaseAclRevoke
                else:
                    break
    def AuthorizationPub(self, client, topic, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ" or self.broker_name == "emitter"):
            return (code, label)
    def AuthorizationSub(self, client, topic, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ" or self.broker_name == "emitter"):
            return (code, label)
    def AuthorizationRead(self, client, topic, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ"):
            return (code, label)
    def AuthorizationStore(self, client, topic, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "emitter"):
            return (code, label)
    def AuthorizationLoad(self, client, topic, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "emitter"):
            return (code, label)
    def AuthorizationConnect(self, client, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ"):
            return (code, -1)
    def AclRevoke(self, client, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ"):
            return (code, label)
        elif (self.broker_name == "emitter"):
            return (code, label)
    def CreateMessage(self, client, topic, qos, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ" or self.broker_name == "emitter"):
            return (code, label)
    def CreateDeliverToSubscribers(self, client, topic, qos, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ" or self.broker_name == "emitter"):
            return (code, label)
    def CreateDeliverToSubscribersForWillmsg(self, client, label='undefinedType'):
        label = f'LABEL_{self.label}_{label}'
        self.label += 1
        if (self.broker_name == "mosquitto" or self.broker_name == "FlashMQ" or self.broker_name == "emitter"):
            return (code, label)
    def GetAclCheck(self, op):
        acl = re.findall(self.config['acl_check_pattern'], op)
        if (acl != []):
            if (acl[0] == self.config['authorization_pub']):
                return self.AuthorizationPub
            elif (acl[0] == self.config['authorization_sub']):
                return self.AuthorizationSub
            elif (acl[0] == self.config['authorization_read']):
                return self.AuthorizationRead
            elif (acl[0] == self.config['authorization_store']):
                return self.AuthorizationRead
            elif (acl[0] == self.config['authorization_load']):
                return self.AuthorizationRead
        return None
    def SplitFunction(self, begin_line, end_line):
        funcs = []
        func_begin_idx = 0
        func_end_idx = 0
        func_stack = []
        func_stack_flag = False
        for i in range(begin_line, end_line):
            if ("atomic" in self.source_code[i]):
                func_stack_flag = True
            if (func_stack_flag):
                for c in self.source_code[i]:
                    if (c == '{'):
                        func_stack.append(i)
                        if (len(func_stack) == 1):
                            func_begin_idx = i + 1
                    elif (c == '}'):
                        func_stack.pop()
                if (len(func_stack) == 0):
                    func_end_idx = i
                    funcs.append((func_begin_idx, func_end_idx))
                    func_begin_idx = 0
                    func_end_idx = 0
                    func_stack_flag = False
        return funcs
    def GetInsertionPoint(self, begin_line, end_line):
        points = [begin_line, end_line]
        for i in range(begin_line, end_line):
            if ("Deliver_to_Subscribers" in self.source_code[i] or "Deliver" in self.source_code[i]):
                points.insert(-1, i)
                points.insert(-1, i + 1)
        return points
    def Insert(self, handler, content):
        results = []
        func_begin_line = self.source_code_funcs[handler][0]
        func_end_line = self.source_code_funcs[handler][1] + 1
        without_dup_code = []
        without_dup_paths = {}
        for c in content:
            path = self.source_code[func_begin_line:func_end_line]
            insert_pos = {}
            if (c[0] != []):
                will_flag = False
                will_deliver = '''        if
            :: (Sessions[Clients[index].clientId].willmessage.topic != -1) ->
'''
                goto_label = -1
                for insert_code in c[0]:
                    if ('authorization_result' in insert_code[1][0] and 'willmessage' in insert_code[1][0]):
                        goto_label = insert_code[1][1]
                        will_deliver += '\n' + insert_code[1][0] + '\n'
                        will_flag = True
                    elif (will_flag and 'Deliver_to_Subscribers' in insert_code[1][0]):
                        will_flag = False
                        will_deliver += insert_code[1][0] + '\n'
                        will_deliver += goto_label + ":\n skip; \n"
                        will_deliver += '''                    :: else -> skip;

                        if (insert_code[0] - func_begin_line not in list(insert_pos.keys())):
                            insert_pos[insert_code[0] - func_begin_line] = [will_deliver]
                        else:
                            insert_pos[insert_code[0] - func_begin_line].append(will_deliver)
                        continue
                    elif (will_flag):
                        print(colored(f"Error: Bad will message delivery: {c}", "red"))
                        exit()
                    elif ('authorization_result' in insert_code[1][0]):
                        goto_label = insert_code[1][1]
                        if (insert_code[0] - func_begin_line not in list(insert_pos.keys())):
                            insert_pos[insert_code[0] - func_begin_line] = [insert_code[1][0]]
                        else:
                            insert_pos[insert_code[0] - func_begin_line].append(insert_code[1][0])
                        if (goto_label != -1):
                            label_str = goto_label + ":\n skip; \n"
                            pos = insert_code[0] - func_begin_line
                            if ('Deliver_to_Subscribers' in path[pos] or 'Deliver' in path[pos]):
                                pos = pos + 1
                            else:
                                pos = func_end_line - func_begin_line - 1
                            if ('RetainedMessages' in path[pos]):
                                pos = pos + 4
                            if (pos not in list(insert_pos.keys())):
                                insert_pos[pos] = [label_str]
                            else:
                                insert_pos[pos].append(label_str)
                    else:
                        if (insert_code[0] - func_begin_line not in list(insert_pos.keys())):
                            insert_pos[insert_code[0] - func_begin_line] = [insert_code[1][0]]
                        else:
                            insert_pos[insert_code[0] - func_begin_line].append(insert_code[1][0])
                if (will_flag):
                    goto_label = insert_code[1][1]
                    if (insert_code[0] - func_begin_line not in list(insert_pos.keys())):
                        insert_pos[insert_code[0] - func_begin_line] = [insert_code[1][0]]
                    else:
                        insert_pos[insert_code[0] - func_begin_line].append(insert_code[1][0])
                    if (goto_label != -1):
                        label_str = goto_label + ":\n skip; \n"
                        pos = insert_code[0] - func_begin_line
                        if ('Deliver_to_Subscribers' in path[pos] or 'Deliver' in path[pos]):
                            pos = pos + 1
                        else:
                            pos = func_end_line - func_begin_line - 1
                        if (pos not in list(insert_pos.keys())):
                            insert_pos[pos] = [label_str]
                        else:
                            insert_pos[pos].append(label_str)
            for idx in insert_pos:
                path[idx] = '\n'.join(insert_pos[idx]) + '\n' + path[idx]
            code = '\n'.join(path)
            code = re.sub('LABEL_[_0-9A-Za-z]*_[0-9]+', '', code)
            if (code not in without_dup_code):
                without_dup_code.append(code)
                without_dup_paths[code] = [path, f'{handler}_{c[1]}']
            else:
                without_dup_paths[code][1] += f'_{c[1]}'
        for code in without_dup_paths:
            results.append((without_dup_paths[code][0], without_dup_paths[code][1]))
        return results
    def BaseHandlePubrel(self, begin_line, end_line):
        edges = {"PUBREL_entry_point": [], "PUBREL": [], "PUBREL_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.pubrel_insert_point = edges
        self.source_code_funcs['handle__pubrel'] = (edges['PUBREL'][0], edges['PUBREL'][-1])
    def BaseHandleConnect(self, begin_line, end_line):
        edges = {"CONNECT_entry_point": [], "CONNECT_auth_success": [], "CONNECT_cleanStart_true": [], "CONNECT_cleanStart_false": [], "CONNECT_will_message": [], "CONNECT_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.connect_insert_point = edges
        self.source_code_funcs['handle__connect_cleanStartT'] = (edges['CONNECT_cleanStart_true'][0], edges['CONNECT_cleanStart_true'][-1])
        self.source_code_funcs['handle__connect_cleanStartF'] = (edges['CONNECT_cleanStart_false'][0], edges['CONNECT_cleanStart_false'][-1])
    def BaseHandlePublish(self, begin_line, end_line):
        edges = {"PUBLISH_entry_point": [], "PUBLISH": [], "PUBLISH_QoS0_step2": [], "PUBLISH_QoS1_step2": [], "PUBLISH_QoS2_step2": [], "PUBLISH_retained_QoS0_step2": [], "PUBLISH_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.publish_insert_point = edges
        self.source_code_funcs['handle__publish_qos0'] = (edges['PUBLISH_QoS0_step2'][0], edges['PUBLISH_QoS0_step2'][-1])
        self.source_code_funcs['handle__publish_qos1'] = (edges['PUBLISH_QoS1_step2'][0], edges['PUBLISH_QoS1_step2'][-1])
        self.source_code_funcs['handle__publish_qos2'] = (edges['PUBLISH_QoS2_step2'][0], edges['PUBLISH_QoS2_step2'][-1])
        self.source_code_funcs['handle__publish_qos0_retained'] = (edges['PUBLISH_retained_QoS0_step2'][0], edges['PUBLISH_retained_QoS0_step2'][-1])
    def BaseHandleSubscribe(self, begin_line, end_line):
        edges = {"SUBSCRIBE_entry_point": [], "SUBSCRIBE": [], "SUBSCRIBE_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.subscribe_insert_point = edges
        self.source_code_funcs['handle__subscribe'] = (edges['SUBSCRIBE'][0], edges['SUBSCRIBE'][-1])
    def BaseHandleUnSubscribe(self, begin_line, end_line):
        edges = {"UNSUBSCRIBE_entry_point": [], "UNSUBSCRIBE": [], "UNSUBSCRIBE_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.unsubscribe_insert_point = edges
        self.source_code_funcs['handle__unsubscribe'] = (edges['UNSUBSCRIBE'][0], edges['UNSUBSCRIBE'][-1])
    def BaseAclRevoke(self, begin_line, end_line):
        edges = {"ACL_revoke": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.aclrevoke_insert_point = edges
        self.source_code_funcs['ACL_revoke'] = (edges['ACL_revoke'][0], edges['ACL_revoke'][-1])
    def BaseHandleDisconnect(self, begin_line, end_line):
        edges = {"DISCONNECT_entry_point": [], "DISCONNECT": [], "DISCONNECT_end": []}
        funcs = self.SplitFunction(begin_line, end_line)
        for idx, f in enumerate(funcs):
            end = f[1]
            if ('end' not in list(edges.keys())[idx]):
                while (end != f[0]):
                    found_end = False
                    for e in list(edges.keys()):
                        if (e in self.source_code[end]):
                            found_end = True
                            break
                    if (found_end):
                        break
                    end = end - 1
                if (end == f[0]):
                    end = f[1] - 1
            edges[list(edges.keys())[idx]] = self.GetInsertionPoint(f[0], end)
        self.disconnect_insert_point = edges
        self.source_code_funcs['handle__disconnect'] = (edges['DISCONNECT'][0], edges['DISCONNECT'][-1])
    def CompleteHandlePubrel(self):
        handle__pubrel = []
        for path in path_types['handle__pubrel']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            acl_check_stack = []
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                            else:
                                insert_code = foo(client='index', topic='Sessions[Clients[index].clientId].messages[lastMessage].topic', label=type)
                                acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__pubrel_end'] in op):
                        end_flag = True
                    elif (self.config['deliver_to_subscribers'] in op):
                        if (acl_check_stack != [] and self.config['acl_check'] in acl_check_stack[-1] and self.config['will'] in acl_check_stack[-1]):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            acl_check_stack.append(op)
                    if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                        insert_flag = 1
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.pubrel_insert_point['PUBREL'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.pubrel_insert_point['PUBREL'][2], insert_code))
            if (not end_flag):
                print(colored(f"Error: can not find the end of handle__pubrel : {path}", "red"))
            else:
                handle__pubrel.append((insert, type))
        self.paths['handle__pubrel'] = self.Insert("handle__pubrel", handle__pubrel)
    def CompleteHandleConnect(self):
        handle__connect_cleanStartT = []
        handle__connect_cleanStartF = []
        for path in path_types['handle__connect_cleanStartT']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            acl_check_stack = []
            will_count = 0
            will_flag = False
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                                    will_count += 1
                            else:
                                insert_code = self.AuthorizationConnect(client='index', label=type)
                                acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__connect_end'] in op):
                        end_flag = True
                    elif (self.config['deliver_to_subscribers'] in op):
                        if (acl_check_stack != [] and self.config['acl_check'] in acl_check_stack[-1] and self.config['will'] in acl_check_stack[-1]):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            acl_check_stack.append(op)
                            will_count -= 1
                        elif (will_count == 0 and self.config['will'] in op):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            will_count += 1
                    if (insert_flag == 0 and self.config['deliver'] in op):
                        insert_flag = 1
                    elif (insert_code != ''):
                        insert.append((self.connect_insert_point['CONNECT_cleanStart_true'][0], insert_code))
            if (not end_flag):
                print(colored(f"Error: can not find the end of handle__connect_cleanStartT : {path}", "red"))
            elif (insert_flag == 0):
                pass
            else:
                handle__connect_cleanStartT.append((insert, type))
        for path in path_types['handle__connect_cleanStartF']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            acl_check_stack = []
            will_count = 0
            will_flag = False
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                                    will_count += 1
                                    will_flag = True
                            else:
                                insert_code = self.AuthorizationConnect(client='index', label=type)
                                acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__connect_end'] in op):
                        end_flag = True
                    elif (self.config['deliver_to_subscribers'] in op):
                        if (acl_check_stack != [] and self.config['acl_check'] in acl_check_stack[-1] and self.config['will'] in acl_check_stack[-1]):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            acl_check_stack.append(op)
                            will_count -= 1
                            will_flag = True
                        elif (will_count == 0 and self.config['will'] in op):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            will_count += 1
                            will_flag = True
                    if (insert_flag == 0 and self.config['deliver'] in op):
                        insert_flag = 1
                    elif (will_flag):
                        insert.append((self.connect_insert_point['CONNECT_cleanStart_false'][0], insert_code))
                        will_flag = False
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.connect_insert_point['CONNECT_cleanStart_false'][0], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.connect_insert_point['CONNECT_cleanStart_false'][2], insert_code))
            if (not end_flag):
                print(colored(f"Error: can not find the end of handle__connect_cleanStartF : {path}", "red"))
            elif (insert_flag == 0):
                pass
            else:
                handle__connect_cleanStartF.append((insert, type))
        self.paths['handle__connect_cleanStartT'] = self.Insert("handle__connect_cleanStartT", handle__connect_cleanStartT)
        self.paths['handle__connect_cleanStartF'] = self.Insert("handle__connect_cleanStartF", handle__connect_cleanStartF)
    def CompleteHandlePublish(self):
        handle__publish_qos0 = []
        handle__publish_qos1 = []
        handle__publish_qos2 = []
        handle__publish_qos0_retained = []
        for path in path_types['handle__publish_qos0']:
            type = ''
            insert = []
            insert_flag = 0
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            insert_code = foo(client='index', topic='t', label=type)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__publish_qos1_end'] in op):
                        pass
                    elif (self.config['handle__publish_qos2_end'] in op):
                        insert_code = self.CreateMessage(client='index', topic='t', qos='2', label=type)
                    elif (insert_flag == 1 and self.config['deliver_to_subscribers'] in op):
                        insert_code = self.CreateDeliverToSubscribers(client='index', topic='t', qos='0', label=type)
                    if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                        insert_flag = 1
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_QoS0_step2'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_QoS0_step2'][2], insert_code))
            if (insert_flag == 0):
                print(colored(f"Error: error/uncomplete path type of handle__publish_qos0 : {path}", "red"))
            else:
                handle__publish_qos0.append((insert, type))
        for path in path_types['handle__publish_qos1']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            insert_code = foo(client='index', topic='t', label=type)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__publish_qos1_end'] in op):
                        end_flag = True
                    elif (self.config['handle__publish_qos2_end'] in op):
                        insert_code = self.CreateMessage(client='index', topic='t', qos='2', label=type)
                    elif (insert_flag == 1 and self.config['deliver_to_subscribers'] in op):
                        insert_code = self.CreateDeliverToSubscribers(client='index', topic='t', qos='1', label=type)
                    if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                        insert_flag = 1
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_QoS1_step2'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_QoS1_step2'][2], insert_code))
            if (insert_flag == 0 or not end_flag):
                print(colored(f"Error: can not find the end of handle__publish_qos1 : {path}", "red"))
            else:
                handle__publish_qos1.append((insert, type))
        for path in path_types['handle__publish_qos2']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            if (len(self.publish_insert_point['PUBLISH_QoS2_step2']) == 4):
                for op in path:
                    if ('Type-' in op):
                        type = op.replace('-', '_').replace(',', '_')
                    else:
                        insert_code = ''
                        if (self.config['acl_check'] in op):
                            foo = self.GetAclCheck(op)
                            if (foo):
                                insert_code = foo(client='index', topic='t', label=type)
                            else:
                                print(colored(f"Error: Bad acl check in path: {path}", "red"))
                                exit()
                        elif (self.config['handle__publish_qos1_end'] in op):
                            pass
                        elif (self.config['handle__publish_qos2_end'] in op):
                            if (not end_flag):
                                end_flag = True
                            else:
                                insert_code = self.CreateMessage(client='index', topic='t', qos='2', label=type)
                        elif (insert_flag == 1 and self.config['deliver_to_subscribers'] in op):
                            insert_code = self.CreateDeliverToSubscribers(client='index', topic='t', qos='2', label=type)
                        if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                            insert_flag = 1
                        elif (insert_flag == 0 and insert_code != ''):
                            insert.append((self.publish_insert_point['PUBLISH_QoS2_step2'][1], insert_code))
                        elif (insert_flag == 1 and insert_code != ''):
                            insert.append((self.publish_insert_point['PUBLISH_QoS2_step2'][2], insert_code))
                if (insert_flag == 0 or not end_flag):
                    print(colored(f"Error: can not find the end of handle__publish_qos2 : {path}", "red"))
                else:
                    handle__publish_qos2.append((insert, type))
            elif (len(self.publish_insert_point['PUBLISH_QoS2_step2']) == 2):
                for op in path:
                    if ('Type-' in op):
                        type = op.replace('-', '_').replace(',', '_')
                    else:
                        insert_code = ''
                        if (self.config['acl_check'] in op):
                            foo = self.GetAclCheck(op)
                            if (foo):
                                insert_code = foo(client='index', topic='t', label=type)
                            else:
                                print(colored(f"Error: Bad acl check in path: {path}", "red"))
                                exit()
                        elif (self.config['handle__publish_qos2_end'] in op):
                            if (not end_flag):
                                end_flag = True
                            else:
                                insert_code = self.CreateMessage(client='index', topic='t', qos='2', label=type)
                        elif (self.config['deliver_to_subscribers'] in op):
                            insert_code = self.CreateDeliverToSubscribers(client='index', topic='t', qos='2', label=type)
                        if (insert_code != ''):
                            insert.append((self.publish_insert_point['PUBLISH_QoS2_step2'][0], insert_code))
                if (not end_flag):
                    print(colored(f"Error: can not find the end of handle__publish_qos2 : {path}", "red"))
                else:
                    handle__publish_qos2.append((insert, type))
        for path in path_types['handle__publish_qos0_retained']:
            type = ''
            insert = []
            insert_flag = 0
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            insert_code = foo(client='index', topic='t', label=type)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__publish_qos1_end'] in op):
                        pass
                    elif (self.config['handle__publish_qos2_end'] in op):
                        insert_code = self.CreateMessage(client='index', topic='t', qos='2', label=type)
                    elif (insert_flag == 1 and self.config['deliver_to_subscribers'] in op):
                        insert_code = self.CreateDeliverToSubscribers(client='index', topic='t', qos='0', label=type)
                    if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                        insert_flag = 1
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_retained_QoS0_step2'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.publish_insert_point['PUBLISH_retained_QoS0_step2'][2], insert_code))
            if (insert_flag == 0):
                print(colored(f"Error: error path type of handle__publish_qos0_retained : {path}", "red"))
            else:
                handle__publish_qos0_retained.append((insert, type))
        self.paths['handle__publish_qos0'] = self.Insert("handle__publish_qos0", handle__publish_qos0)
        self.paths['handle__publish_qos1'] = self.Insert("handle__publish_qos1", handle__publish_qos1)
        self.paths['handle__publish_qos2'] = self.Insert("handle__publish_qos2", handle__publish_qos2)
        self.paths['handle__publish_qos0_retained'] = self.Insert("handle__publish_qos0_retained", handle__publish_qos0_retained)
    def CompleteHandleSubscribe(self):
        handle__subscribe = []
        for path in path_types['handle__subscribe']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            sub_flag = False
            acl_check_stack = []
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                            else:
                                c = ''
                                t = ''
                                if (self.config['authorization_sub'] in op or self.config['authorization_read'] in op):
                                    c = 'index'
                                    t = 't'
                                elif (self.config['authorization_pub'] in op):
                                    c = 'message.srcClientIndex'
                                    t = 't'
                                insert_code = foo(client=c, topic=t, label=type)
                                acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__subscribe_end'] in op):
                        end_flag = True
                    elif (self.config['sub_add'] in op):
                        sub_flag = True
                    elif (self.config['deliver_to_subscribers'] in op):
                        if (acl_check_stack != [] and self.config['acl_check'] in acl_check_stack[-1] and self.config['will'] in acl_check_stack[-1]):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            acl_check_stack.append(op)
                    if (self.config['deliver'] in op and insert_flag == 0):
                        insert_flag = 1
                    if (insert_code != '' and 'Authorization_subscribe_allowed' in insert_code[0]):
                        insert.append((self.subscribe_insert_point['SUBSCRIBE'][0], insert_code))
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.subscribe_insert_point['SUBSCRIBE'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.subscribe_insert_point['SUBSCRIBE'][2], insert_code))
            if (not end_flag):
                print(colored(f"Error: can not find the end of handle__subscribe : {path}", "red"))
            elif (insert_flag == 0 or not sub_flag):
                pass
            else:
                handle__subscribe.append((insert, type))
        self.paths['handle__subscribe'] = self.Insert("handle__subscribe", handle__subscribe)
    def CompleteHandleUnSubscribe(self):
        handle__unsubscribe = []
        for path in path_types['handle__unsubscribe']:
            type = ''
            insert = []
            end_flag = False
            sub_flag = False
            acl_check_stack = []
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                            else:
                                c = ''
                                t = ''
                                if (self.config['authorization_sub'] in op or self.config['authorization_read'] in op):
                                    c = 'index'
                                    t = 't'
                                elif (self.config['authorization_pub'] in op):
                                    c = 'message.srcClientIndex'
                                    t = 't'
                                insert_code = foo(client=c, topic=t, label=type)
                                acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    elif (self.config['handle__unsubscribe_end'] in op):
                        end_flag = True
                    elif (self.config['sub_remove'] in op):
                        sub_flag = True
                    elif (self.config['deliver_to_subscribers'] in op):
                        if (acl_check_stack != [] and self.config['acl_check'] in acl_check_stack[-1] and self.config['will'] in acl_check_stack[-1]):
                            insert_code = self.CreateDeliverToSubscribersForWillmsg(client='index', label=type)
                            acl_check_stack.append(op)
                    if (insert_code != ''):
                        insert.append((self.unsubscribe_insert_point['UNSUBSCRIBE'][0], insert_code))
            if (not end_flag):
                print(colored(f"Error: can not find the end of handle__unsubscribe : {path}", "red"))
            elif (not sub_flag):
                pass
            else:
                handle__unsubscribe.append((insert, type))
        self.paths['handle__unsubscribe'] = self.Insert("handle__unsubscribe", handle__unsubscribe)
    def CompleteHandleDisconnect(self):
        handle__disconnect = []
        for path in path_types['handle__disconnect']:
            type = ''
            insert = []
            insert_flag = 0
            end_flag = False
            acl_check_stack = []
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    if (insert_flag == 0 and self.config['deliver_to_subscribers'] in op):
                        insert_flag = 1
                    elif (insert_flag == 0 and insert_code != ''):
                        insert.append((self.disconnect_insert_point['DISCONNECT'][1], insert_code))
                    elif (insert_flag == 1 and insert_code != ''):
                        insert.append((self.disconnect_insert_point['DISCONNECT'][2], insert_code))
            if (insert_flag == 0):
                handle__disconnect.append((insert, type))
            else:
                handle__disconnect.append((insert, type))
        self.paths['handle__disconnect'] = self.Insert("handle__disconnect", handle__disconnect)
    def CompleteAclRevoke(self):
        ACL_revoke = []
        for path in path_types['handle__ACL_revoke']:
            type = ''
            insert = []
            insert_flag = 0
            acl_check_stack = []
            for op in path:
                if ('Type-' in op):
                    type = op.replace('-', '_').replace(',', '_')
                else:
                    insert_code = ''
                    if (self.config['acl_check'] in op):
                        foo = self.GetAclCheck(op)
                        if (foo):
                            if (self.config['will'] in op):
                                insert_code = foo(client='Sessions[Clients[index].clientId].willmessage.srcClientIndex', topic='Sessions[Clients[index].clientId].willmessage.topic', label=type)
                                if (op in acl_check_stack):
                                    insert_code = ''
                                else:
                                    acl_check_stack.append(op)
                        else:
                            print(colored(f"Error: Bad acl check in path: {path}", "red"))
                            exit()
                    if (self.config['acl_revoke'] in op):
                        insert_flag = 1
                        insert_code = self.AclRevoke(client='index')
                    if (insert_flag == 1 and insert_code != ''):
                        insert.append((self.aclrevoke_insert_point['ACL_revoke'][0], insert_code))
            ACL_revoke.append((insert, type))
        self.paths['ACL_revoke'] = self.Insert("ACL_revoke", ACL_revoke)
    def CompleteModel(self):
        self.CompleteHandlePublish()
        self.CompleteHandleConnect()
        self.CompleteHandleDisconnect()
        self.CompleteHandlePubrel()
        self.CompleteHandleSubscribe()
        self.CompleteHandleUnSubscribe()
        self.CompleteAclRevoke()
        line = -1
        for idx, code in enumerate(self.source_code):
            for h in self.source_code_funcs:
                if (idx == self.source_code_funcs[h][0]):
                    func_names = []
                    for func in self.paths[h]:
                        func_names.append(f':: {func[1]}({self.param[h]});')
                    branchs = 'if\n' + '\n'.join(func_names) + '\nfi;\n'
                    self.output.write(branchs)
                    line = self.source_code_funcs[h][1]
            if ('inline Deliver(message, subscriber)' in code):
                for h in self.paths:
                    for func in self.paths[h]:
                        func_content = f'inline {func[1]}({self.param[h]})' + '{\n atomic{\n'
                        func_content += f'printf("Enter function {func[1]}' + '\\n");'
                        func_content += '\n' + ''.join(func[0]) + '\n' + '}\n}\n\n'
                        self.output.write(func_content)
            if (line == -1):
                self.output.write(code)
            elif (line == idx):
                line = -1
        self.output.close()
if __name__ == "__main__":
    model = Model('FlashMQ', 'BaseModel/BaseModel.pml', 'ConcreteModel/ConcreteModel.pml')
    model.CompleteModel()
