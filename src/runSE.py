import subprocess
import time
import re
import os
import sys


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.append(BASE_DIR)

LANG = ''
handlers = {
    "handle__publish": ('qos0', 'qos1', 'qos2', 'qos0_retained'),
    "handle__pubrel": (),
    "handle__subscribe": (),
    "handle__connect": ('cleanStartT', 'cleanStartF'),
    "handle__disconnect": (),
    "handle__unsubscribe": (),
    "handle__revoke": ()
}
count = 0
process = []
end = False

handler = "handle__publish"


def runSE(type, handler, sub_cond, entry_func, bc):
    tyPath = f'{BASE_DIR}/CFGPass/OUTPUT/PATHS/{handler}/Type-{type}'
    if (os.path.exists(tyPath)):
        if not os.path.exists(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler):
            os.mkdir(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler)
        f = open(f'{BASE_DIR}/ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_{sub_cond}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_qos0_retained.log', 'w')
        popen = subprocess.Popen([f"{BASE_DIR}/CFGPass/bin/SE", handler, entry_func,
                                  str(type), f"{BASE_DIR}/CFGPass/", bc],
                                 stdout=f,
                                 stderr=subprocess.STDOUT)
        popen.wait()
        print(f"{handler} Type-{type} Done")

def runSE_2(type, handler, entry_func, bc):
    tyPath = f'{BASE_DIR}/CFGPass/OUTPUT/PATHS/{handler}/Type-{type}'
    if (os.path.exists(tyPath)):
        if not os.path.exists(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler):
            os.mkdir(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler)
        f = open(f'{BASE_DIR}/ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_qos0_retained.log', 'w')
        popen = subprocess.Popen([f"{BASE_DIR}/CFGPass/bin/SE", handler, entry_func,
                                  str(type), f"{BASE_DIR}/CFGPass/", bc],
                                 stdout=f,
                                 stderr=subprocess.STDOUT)
        popen.wait()
        print(f"{handler} Type-{type} Done")

def ModelGenerator(bc_dir):
    for sub_cond in handlers["handle__publish"]:
        for t in range(8):
            runSE(t, "handle__publish", sub_cond, "_ZN10MqttPacket13handlePublishEv", f"{bc_dir}/FlashMQ_{sub_cond}.bc")
    for t in range(8):
            runSE_2(t, "handle__pubrel", "_ZN10MqttPacket12handlePubRelEv", f"{bc_dir}/FlashMQ_qos0.bc")
    for t in range(18):
            runSE_2(t, "handle__subscribe", "_ZN10MqttPacket15handleSubscribeEv", f"{bc_dir}/FlashMQ_qos0.bc")
    for sub_cond in handlers["handle__connect"]:
        for t in range(48):
            runSE(t, "handle__connect", sub_cond, "_ZN10MqttPacket13handleConnectEv", f"{bc_dir}/FlashMQ_{sub_cond}.bc")
    for t in range(2):
            runSE_2(t, "handle__disconnect", "_ZN10MqttPacket16handleDisconnectEv", f"{bc_dir}/FlashMQ_qos0.bc")
    for t in range(3):
            runSE_2(t, "handle__unsubscribe", "_ZN10MqttPacket17handleUnsubscribeEv", f"{bc_dir}/FlashMQ_qos0.bc")

def run(type):
    global process, handler
    tyPath = f'../OUTPUT/PATHS/{handler}/Type-{type}'
    if (os.path.exists(tyPath)):
        starttime = time.time()
        if not os.path.exists("../../ModelCheck/SymbolicExecutionResults/" + handler):
            os.mkdir("../../ModelCheck/SymbolicExecutionResults/" + handler)
        #f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_cleanStartT.log', 'w')
        f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_qos0_retained.log', 'w')
        popen = subprocess.Popen([
            "./SE", handler, "_ZN10MqttPacket13handlePublishEv",
            str(type), "/root/Documents/mqttdemo.com/Tools/MQTTactic/CFGPass",
            "/root/Documents/mqttdemo.com/Tools/MQTTactic/CFGPass/complete_cleanStartT.bc"
        ],
                                 stdout=f,
                                 stderr=subprocess.STDOUT)
        process.append((f, popen, starttime, str(type)))
        return True
    else:
        return False

def multiProcess():
    T1 = time.time()
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
                T2 = time.time()
                print('RUN TIME:%s ms' % ((T2 - T1) * 1000))
                exit()
            if (run(count)):
                count += 1
            else:
                end = True
            alive_process += 1
        time.sleep(5)




if __name__ == "__main__":
    if not os.path.exists(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/"):
        os.mkdir(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/")
    ModelGenerator(f"{BASE_DIR}/CFGPass")
