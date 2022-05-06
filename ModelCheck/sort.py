import re
import os
import time

actions = []
with open('./build/result.txt', 'r') as f1:
    content = f1.read()
    # pan: wrote mosquitto.pml1.trail
    trailFiles = re.findall('pan: wrote (.*?\.trail)\n', content)
    dir = f'./result_{time.time()}'
    if (trailFiles != []):12
        os.mkdir(dir)
        for t in trailFiles:
            os.system(f'spin -k ./build/{t} -t ConcreteModel.pml > {dir}/{t}.txt')
            with open(f'{dir}/{t}.txt', 'r') as f2:
                s = f2.read()
                actionsPub = re.findall('(PUBLISHER_0:.*?)\n', s)
                actionsPub2 = re.findall('(PUBLISHER_2:.*?)\n', s)
                actionsSub = re.findall('(SUBSCRIBER_1:.*?)\n', s)
                if (actionsPub + actionsSub + actionsPub2 not in actions):
                    actions.append(actionsPub + actionsSub + actionsPub2)
                    with open(f'{dir}/NEW_{t}.txt', 'w') as f3:
                        f3.write(s)
