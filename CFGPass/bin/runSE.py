import subprocess
import time
import re
import os
count = 0
process = []
end = False
handler = "handle__connect"
def run(type):
    global process, handler
    tyPath = f'../OUTPUT/PATHS/{handler}/Type-{type}'
    if (os.path.exists(tyPath)):
        starttime = time.time()
        if not os.path.exists("../../ModelCheck/SymbolicExecutionResults/" + handler):
            os.mkdir("../../ModelCheck/SymbolicExecutionResults/" + handler)
        f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_cleanStartF.log', 'w')
        popen = subprocess.Popen(["./SE", handler, "_ZN10MqttPacket13handleConnectEv", str(type), "/Experiments/FlashMQ/CFGPass/"], stdout=f, stderr=subprocess.STDOUT)
        process.append((f, popen, starttime, str(type)))
        return True
    else:
        return False
while (1):
    for idx, p in enumerate(process):
        if (p != -1):
            f = p[0]
            proc = p[1]
            starttime = p[2]
            type = p[3]
            if (proc.poll() is not None):
                f.close()
                process[idx] = -1
            else:
                now = time.time()
                if (now - starttime >= 1800):
                    print(f"ERROR: timeout---- Type-{f.name}")
                    proc.kill()
                    proc.wait()
                    f.close()
                    process[idx] = -1
    alive_process = 0
    for p in process:
        if (p != -1):
            alive_process += 1
    while (alive_process < 5):
        if (end and alive_process == 0):
            print("OKKKKKKKKKKK!")
            exit()
        if (run(count)):
            count += 1
        else:
            end = True
        alive_process += 1
    time.sleep(5)
