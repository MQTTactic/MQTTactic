import re
import os
import sys
import json
import argparse
import cxxfilt
import subprocess
import time

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


def ParseBitcode(bc):
    pass


def Demangle(funcs):
    global LANG
    result = {}
    if (LANG == "c++"):
        for func in funcs:
            try:
                result[cxxfilt.demangle(func)] = func
            except:
                pass
    elif (LANG == "c"):
        for func in funcs:
            result[func] = func
    elif (LANG == "golang"):
        # TODO: rewrite
        # https://go.googlesource.com/gofrontend/+/refs/heads/master/libgo/go/runtime/symtab.go#281
        pass

    return result


def ParseConfig(conf, funcs):
    all_functions = {}
    config = {}
    config_result = {}
    with open(funcs, "r") as f:
        all_functions = Demangle(f.read().split('\n'))
    with open(conf, "r") as f:
        config = json.loads(f.read())
        config_result = config
    for c in config:
        if ("handle__" in c or "permission_check" == c):
            try:
                c_tripped = re.findall(" (.*?)\(", config[c])[0]
            except:
                if (config[c] == ""):
                    config_result[c] = ""
                    continue
            for func in all_functions:
                # [TODO]: Not sure if this work in other languages
                if (c_tripped == func):
                    config_result[c] = all_functions[func]
    with open(BASE_DIR + "/Include/CONFIG.h", 'w') as f:
        f.write("using namespace std;\nnamespace mqttactic{\n")
        for c in config_result:
            f.write(f"static std::string {c} = \"{config_result[c]}\";\n")
        f.write("\n}")

    with open(BASE_DIR + "/Include/CONFIG.py", 'w') as f:
        f.write("config = {\n")
        for c in config_result:
            f.write(f"\"{c}\" : \"{config_result[c]}\",\n")
        f.write("}\n")


def runSE(type, handler, sub_cond, entry_func, bc):
    if (sub_cond != ""):
        sub_cond = "_" + sub_cond
    tyPath = f'{BASE_DIR}/CFGPass/OUTPUT/PATHS/{handler}/Type-{type}'
    #print([f"{BASE_DIR}/CFGPass/bin/SE", handler, entry_func, str(type), f"{BASE_DIR}/CFGPass/", bc])
    if (os.path.exists(tyPath)):
        if not os.path.exists(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler):
            os.mkdir(f"{BASE_DIR}/ModelCheck/SymbolicExecutionResults/" + handler)
        f = open(f'{BASE_DIR}/ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}{sub_cond}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}.log', 'w')
        # f = open(f'../../ModelCheck/SymbolicExecutionResults/{handler}/Type-{type}_qos0_retained.log', 'w')
        popen = subprocess.Popen([f"{BASE_DIR}/CFGPass/bin/SE", handler, entry_func,
                                  str(type), f"{BASE_DIR}/CFGPass/", bc],
                                 stdout=f,
                                 stderr=subprocess.STDOUT)
        out, err = popen.communicate()
        p_status = popen.wait()


# TODO: 
def ModelGenerator(bc_dir):
    # for h in handlers:
    #     if(handlers[h] != ()):
    #         for sub_cond in handlers[h]:
    #             runSE()
    T1 = time.time()
    for sub_cond in handlers["handle__connect"]:
        for t in range(48):
            runSE(t, "handle__connect", sub_cond, "_ZN10MqttPacket13handleConnectEv", f"{bc_dir}/complete_{sub_cond}.bc")
    T2 = time.time()
    print('handle__connect RUN TIME:%s ms' % ((T2 - T1) * 1000))

    T1 = time.time()
    sub_cond = ""
    for t in range(2):
        runSE(t, "handle__disconnect", sub_cond, "_ZN10MqttPacket16handleDisconnectEv", f"{bc_dir}/complete.bc")
    T2 = time.time()
    print('handle__disconnect RUN TIME:%s ms' % ((T2 - T1) * 1000))

    T1 = time.time()
    for sub_cond in handlers["handle__publish"]:
        for t in range(8):
            runSE(t, "handle__publish", sub_cond, "_ZN10MqttPacket13handlePublishEv", f"{bc_dir}/complete_{sub_cond}.bc")
    T2 = time.time()
    print('handle__publish RUN TIME:%s ms' % ((T2 - T1) * 1000))

    T1 = time.time()
    sub_cond = ""
    for t in range(1):
        runSE(t, "handle__pubrel", sub_cond, "_ZN10MqttPacket12handlePubRelEv", f"{bc_dir}/complete.bc")
    T2 = time.time()
    print('handle__pubrel RUN TIME:%s ms' % ((T2 - T1) * 1000))

    T1 = time.time()
    sub_cond = ""
    for t in range(18):
        runSE(t, "handle__subscribe", sub_cond, "_ZN10MqttPacket15handleSubscribeEv", f"{bc_dir}/complete.bc")
    T2 = time.time()
    print('handle__subscribe RUN TIME:%s ms' % ((T2 - T1) * 1000))

    T1 = time.time()
    sub_cond = ""
    for t in range(3):
        runSE(t, "handle__unsubscribe", sub_cond, "_ZN10MqttPacket17handleUnsubscribeEv", f"{bc_dir}/complete.bc")
    T2 = time.time()
    print('handle__unsubscribe RUN TIME:%s ms' % ((T2 - T1) * 1000))

    pass


def ModelChecker():
    spin = subprocess.Popen([f"{BASE_DIR}/ModelCheck/ModelChecker.sh"], stderr=subprocess.STDOUT)
    out, err = spin.communicate()
    p_status = spin.wait()


def Run():
    pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-c', '--config', default=BASE_DIR + "/Include/CONFIG.json", help="The configuration file")
    parser.add_argument('-b', '--bitcode', default=BASE_DIR + "/CFGPass/complete.bc", help="The LLVM bitcode to analyze")
    parser.add_argument('-Cd', '--CFGPassDir', default=BASE_DIR + "/CFGPass/", help="The LLVM bitcode directory")
    parser.add_argument('-L', '--language', default="c++", help="Language of the project. e.g., c++, c, java, golang")
    parser.add_argument('-F',
                        '--funcs',
                        default=BASE_DIR + "/CFGPass/ALLFunctions",
                        help="All functions defined in LLVM bitcode")
    parser.add_argument('-s', '--start', default="none", help="MG/MC")
    args = parser.parse_args()
    LANG = args.language.lower()

    ParseConfig(args.config, args.funcs)
    if (args.start == "MG"):
        ModelGenerator(args.CFGPassDir)
    elif (args.start == "MC"):
        ModelChecker()
