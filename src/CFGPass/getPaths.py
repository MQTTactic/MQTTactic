import os
import re
import shutil
import sys
from copy import deepcopy
BASE_DIR = os.path.dirname(os.path.abspath(__file__))  #存放c.py所在的绝对路径

sys.path.append(BASE_DIR + "/../")
from Include.CONFIG import config

DIR = BASE_DIR + "/OUTPUT/"
OUTPUTDIR = BASE_DIR + "/../ModelCheck/SymbolicExecutionResults/"
handlers = {
    "handle__publish": config["handle__publish"],
    "handle__pubrel": config["handle__pubrel"],
    "handle__subscribe": config["handle__subscribe"],
    "handle__unsubscribe": config["handle__unsubscribe"],
    "handle__connect": config["handle__connect"],
    "handle__disconnect": config["handle__disconnect"],
    "handle__revoke": config["handle__revoke"]
}
#handlers = ("handle__connect", "handle__publish", )
operations = {
    "send__connack": config["send__connack"],
    "send__puback": config["send__puback"],
    "send__pubrec": config["send__pubrec"],
    "send__pubcomp": config["send__pubcomp"],
    "send__suback": config["send__suback"],
    "send__unsuback": config["send__unsuback"],
    # key operations
    "acl_check": config["acl_check"],
    "deliver_to_subscribers": config["deliver_to_subscribers"],
    "deliver": config["deliver"],
    "sub_add": config["sub_add"],
    "sub_remove": config["sub_remove"],
    "acl_revoke": config["acl_revoke"],
}

# {keyBB: [calledFuncs]}
keyBBs = {}

keyOps = {}

# set: {"db__message_write_queued_in", "db__message_write_queued_in"}
keyFuncs = set()
# {startBB: {endBB: [paths]}}
paths = {}

# {funcName: [keyBBPaths]}
pathTypes = {}


# 读取函数类型文件中，所有路径类型(pathTypes)，以及所有keyBBs之间的路径(paths)
def readPaths(func):
    global keyBBs, keyOps, keyFuncs, paths, pathTypes
    pathTypes[func] = []
    for file in os.listdir(DIR):
        if (re.match(func + "_Type_[\d]+", file)):
            with open(DIR + file, encoding="utf-8") as f:
                readStr = f.readline()
                path = []
                pathType = []
                endOfPath = False
                dupFlag = False
                startBB = ""
                endBB = ""
                while (readStr):
                    if (not readStr.startswith("*") and dupFlag):
                        readStr = f.readline()
                        continue
                    if (readStr.startswith("*")):
                        dupFlag = False
                        startBB = re.findall("(((?![ ]).)*?:((?![ ]).)+)", readStr)[0][0]
                        endBB = re.findall("(((?![ ]).)*?:((?![ ]).)+)", readStr)[1][0]
                        if (len(pathType) == 0 or pathType[-1] != startBB):
                            pathType.append(startBB)
                        pathType.append(endBB)
                        if (startBB not in paths.keys()):
                            paths[startBB] = {endBB: []}
                        elif (endBB not in paths[startBB].keys()):
                            paths[startBB][endBB] = []
                        elif (len(paths[startBB][endBB]) > 0):
                            dupFlag = True
                    elif (readStr.startswith("PATH")):
                        s = f.readline()
                        while (s):
                            if (s.startswith("*") or s.startswith("PATH")):
                                paths[startBB][endBB].append(deepcopy(path))
                                path.clear()
                                readStr = s
                                endOfPath = True
                                break
                            else:
                                path.append(s.strip())
                                s = f.readline()
                                if (not s):
                                    paths[startBB][endBB].append(deepcopy(path))
                                    path.clear()
                    if (endOfPath):
                        endOfPath = False
                        continue
                    readStr = f.readline()

                pathTypes[func].append(pathType)


def getFullPathTypes(keyBBPath, results):
    global keyBBs, keyOps, keyFuncs, paths, pathTypes
    for bb in keyBBPath:
        for r in results:
            r.append(bb)
        # 在bb中存在关键函数调用
        if (bb in keyBBs.keys()):
            for call in keyBBs[bb]:
                inMainPath = False
                for n in keyBBPath:
                    if (re.match(f"{call}:.*?", n)):
                        inMainPath = True
                        break
                if (inMainPath):
                    continue
                resultsTmp = []
                for p in pathTypes[call]:
                    r = deepcopy(results)
                    r = getFullPathTypes(p, r)
                    resultsTmp += r
                results = resultsTmp
    return results


def typeFilter(list):
    result = []
    for i in list:
        if (len(result) == 0):
            result.append(i)
        elif (result[-1] != i):
            result.append(i)
        else:
            continue
    return result


for h in handlers:
    keyBBs.clear()
    keyFuncs.clear()
    keyOps.clear()
    paths.clear()
    pathTypes.clear()
    try:
        if not os.path.exists(DIR + "PATHS/" + h):
            os.mkdir(DIR + "PATHS/" + h)
        else:
            shutil.rmtree(DIR + "PATHS/" + h)
            os.mkdir(DIR + "PATHS/" + h)
    except:
        pass

    if not os.path.exists(DIR + h + ".output"):
        continue
    # 读取keyBBs与其调用关系，以及keyFuncs
    with open(DIR + h + ".output", encoding="utf-8") as f:
        readStr = f.readline()
        keyBB = ''
        while (readStr):
            if ("KEY BASIC BLOCKS" in readStr):
                keyBB = f.readline().strip()
                keyFunc = keyBB.split(":")[0]
                calledFuncs = [i.strip() for i in f.readline().strip()[6:-1].split(',') if (i.strip() != '')]
                keyBBs[keyBB] = set(calledFuncs)
                keyFuncs.add(keyFunc)
            readStr = f.readline()
            for op in operations:
                if (op + "-----" in readStr):
                    if (keyBB not in keyOps.keys()):
                        keyOps[keyBB] = []
                    opSource = readStr.strip().replace(' ', '')
                    opSource = opSource.replace('\t', '')
                    keyOps[keyBB].append(opSource)
    if (len(keyFuncs) == 0):
        keyFuncs.add(handlers[h])
    for f in keyFuncs:
        readPaths(f)

    # print(keyFuncs)
    # print(pathTypes)
    results = []
    for Type in pathTypes[handlers[h]]:
        r = [[]]
        ret = getFullPathTypes(Type, r)
        for t in ret:
            x = typeFilter(t)
            if (x not in results):
                results.append(x)

    outputFile = open(f"{OUTPUTDIR}/{h}.type", 'w')
    for Type in results:
        bbPath = []
        print(f"********************************Type-{str(results.index(Type))}********************************",
              file=outputFile)
        with open(DIR + "PATHS/" + h + "/Type-" + str(results.index(Type)), 'w', encoding="utf-8") as f:
            bbStack = []
            for bb in Type:
                if (len(bbStack) >= 1 and bbStack[-1].split(':')[0] == bb.split(':')[0] and
                        bbStack[-1].split(':')[1] == bb.split(':')[1]):
                    continue
                if (len(bbStack) >= 1 and bbStack[-1].split(':')[0] == bb.split(':')[0]):
                    print(f"{bbStack[-1]} --> {bb}", file=outputFile)
                    if (bbStack[-1] not in bbPath):
                        bbPath.append(bbStack[-1])
                    bbPath.append(bb)
                    originFunc, originbb = bbStack[-1].split(':')
                    destFunc, destbb = bb.split(':')
                    if (originFunc == destFunc):
                        fName = DIR + "KEYBBS/" + f"{originFunc}-{originbb}-{destbb}"
                        with open(fName) as rf:
                            f.write(rf.read())
                    else:
                        continue
                    bbStack.pop()
                if (bb.split(':')[1] != "RETURN"):
                    bbStack.append(bb)
        print(f"('Type-{str(results.index(Type))}', ", end='', file=outputFile)
        for j in [keyOps[i] for i in Type if i in list(keyOps.keys())]:
            for k in j:
                print(f"'{k}'", end=',', file=outputFile)
        print(')', end='\n', file=outputFile)
    outputFile.close()
    # bbStack = []
    # outputs = [[]]
    # for bb in Type:
    #     if (len(bbStack) >= 1 and bbStack[-1].split(':')[0] == bb.split(':')[0]):
    #         print(f"{bbStack[-1]} --> {bb} has {len(paths[bbStack[-1]][bb])} paths")
    #         y = []
    #         for i in paths[bbStack[-1]][bb]:
    #             x = deepcopy(outputs)
    #             for j in x:
    #                 j += i
    #             y += x
    #         outputs = y
    #         bbStack.pop()
    #     if (bb.split(':')[1] != "RETURN"):
    #         bbStack.append(bb)

    # for i, o in enumerate(outputs):
    #     if (i >= 1000):
    #         break
    #     with open(DIR + "PATHS/" + h + "/Type-" + str(results.index(Type)) + "/path." + str(i), 'w', encoding="utf-8") as f:
    #         for bb in o:
    #             f.write(bb + "\n")
