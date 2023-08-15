import re
import os
import sys
import json

from nbformat import read
from sqlalchemy import false
BASE_DIR = os.path.dirname(os.path.abspath(__file__))  #存放c.py所在的绝对路径

sys.path.append(BASE_DIR + "/../")
from Include.CONFIG import config

handlers = {"handle__publish": ('qos0', 'qos1', 'qos2', 'qos0_retained'), "handle__pubrel": (), "handle__subscribe": (), "handle__connect": ('cleanStartT', 'cleanStartF'), "handle__disconnect": (), "handle__unsubscribe": (), "handle__revoke": ()}

mosquitto_config = {
    "handle__publish": config["handle__publish"],
    "handle__pubrel": config["handle__pubrel"],
    "handle__subscribe": config["handle__subscribe"],
    "handle__unsubscribe": config["handle__unsubscribe"],
    "handle__connect": config["handle__connect"],
    "handle__disconnect": config["handle__disconnect"],
    "handle__revoke": config["handle__ACL_revoke"]
}

output = open("./pathTypes.py", 'w')
output.write("pathTypes = {")

for h in handlers:
    pathTypes = {}
    pathIdx = {}

    if not os.path.exists(f"./SymbolicExecutionResults/{h}.type"):
        continue
    with open(f"./SymbolicExecutionResults/{h}.type") as f:
        read_str = f.readline()
        type_idx = 0
        type = ''
        while (read_str):
            a = re.findall('Type-([0-9]+)', read_str)
            b = re.findall('\((.*),[ ]*?\)', read_str)
            if (a != []):
                type_idx = a[0]
            if (b != []):
                type = b[0].replace(f'Type-{type_idx}', 'Type-').replace(' ', '')
                # FlashMQ send__xxack
                op_list = json.loads("[" + type.replace("'", '"') + "]")
                op_list_result = []
                for idx, t in enumerate(op_list):
                    if ("deliver-----" in t and idx != 0):
                        ack = re.match(f'(send__connack|send__puback|send__pubrec|send__pubcomp|send__suback|send__unsuback)-----', op_list[idx - 1])
                        if (ack != None):
                            continue
                    op_list_result.append(t)
                type = json.dumps(op_list_result)[1:-1]
                # re.sub(f'\'({config["send__connack"]}|{config["send__puback"]}|{config["send__pubrec"]}|{config["send__pubcomp"]}|{config["send__suback"]}|{config["send__unsuback"]})')
                # type = type.replace(f"packet_id);','deliver", "packet_id);deliver")
                pathIdx[type_idx] = type

                if (type not in list(pathTypes.keys())):
                    pathTypes[type] = [type_idx]
                else:
                    pathTypes[type].append(type_idx)
            read_str = f.readline()

    if (handlers[h] != ()):
        for constrain in handlers[h]:
            key = f"{h}_{constrain}"
            output.write(f"\"{key}\":[")
            for ty in pathTypes:
                idx = []
                for i in pathTypes[ty]:
                    if (os.path.exists(f"./SymbolicExecutionResults/{h}/Type-{i}_{constrain}.log")):
                        with open(f"./SymbolicExecutionResults/{h}/Type-{i}_{constrain}.log") as f:
                            if ('OK' in f.read()):
                                idx.append(i)
                if (idx != []):
                    x = ty.replace('Type-', f"Type-{','.join(idx)}")
                    output.write(f'({x},),')
            output.write("],")
    else:
        key = h
        output.write(f"\"{key}\":[")
        for ty in pathTypes:
            idx = []
            for i in pathTypes[ty]:
                if (os.path.exists(f"./SymbolicExecutionResults/{h}/Type-{i}.log")):
                    with open(f"./SymbolicExecutionResults/{h}/Type-{i}.log") as f:
                        if ('OK' in f.read()):
                            idx.append(i)
            if (idx != []):
                x = ty.replace('Type-', f"Type-{','.join(idx)}")
                output.write(f'({x},),')
        output.write("],")
output.write("}")
