import re
import os
import time


def ParseMsgSeq(file):
    results = {}
    s = ''
    with open(file, 'r') as f:
        s = f.read()
        lines = s.split("\n")
        for idx, l in enumerate(lines):
            if ("Error: assertion violated" in l):
                mid = re.findall("(Message_[0-9]+):", lines[idx - 2])[0]
                results[mid] = []
        for r in results:
            for idx, l in enumerate(lines):
                if (r in l):
                    funcName = ''
                    pos = idx
                    while ("Enter function" not in lines[pos]):
                        pos = pos - 1
                    results[r].append(lines[pos].strip())
                    results[r].append(l.strip().replace(r, ''))
                elif (" revoke " in l):
                    results[r].append(l.strip())
    return (s, results)


# ParseMsgSeq("SpinResults/NEW_ConcreteModel.pml40.trail.txt")

actions = []
with open('./build/result.txt', 'r') as f1:
    content = f1.read()
    # pan: wrote mosquitto.pml1.trail
    trailFiles = re.findall('pan: wrote (.*?\.trail)\n', content)
    dir = f'./SpinResults/'
    if (trailFiles != []):
        if not os.path.exists(dir):
            os.mkdir(dir)
        for t in trailFiles:
            os.system(f'spin -k ./build/{t} -t ConcreteModel/ConcreteModel.pml > {dir}/{t}.txt')
            s, results = ParseMsgSeq(f'{dir}/{t}.txt')
            repeatFlag = True
            for r in results:
                if (results[r] not in actions):
                    repeatFlag = False
                    actions.append(results[r])
                    break
            if (not repeatFlag):
                with open(f'{dir}/NEW_{t}.txt', 'w') as f3:
                    f3.write(s)
            # with open(f'{dir}/{t}.txt', 'r') as f2:
            #     s = f2.read()
            #     actionsPub = re.findall('(PUBLISHER_0:.*?)\n', s)
            #     actionsPub2 = re.findall('(PUBLISHER_2:.*?)\n', s)
            #     actionsSub = re.findall('(SUBSCRIBER_1:.*?)\n', s)
            #     if (actionsPub + actionsSub + actionsPub2 not in actions):
            #         actions.append(actionsPub + actionsSub + actionsPub2)
            #         with open(f'{dir}/NEW_{t}.txt', 'w') as f3:
            #             f3.write(s)
