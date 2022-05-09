import re
import os
import sys
import json
import argparse
import cxxfilt

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.append(BASE_DIR)

LANG = ''


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
        if ("handle__" in c):
            try:
                c_tripped = re.findall(" (.*?)\(", config[c])[0]
            except:
                print(c)
                exit()
            for func in all_functions:
                if (c_tripped in func):
                    config_result[c] = all_functions[func]
    with open(BASE_DIR + "/Include/CONFIG.h", 'w') as f:
        f.write("using namespace std;\n")
        for c in config_result:
            f.write(f"std::string {c} = \"{config_result[c]}\";\n")

    with open(BASE_DIR + "/Include/CONFIG.py", 'w') as f:
        f.write("config = {\n")
        for c in config_result:
            f.write(f"\"{c}\" : \"{config_result[c]}\",\n")
        f.write("}\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-c', '--config', default=BASE_DIR + "/Include/CONFIG.json", help="The configuration file")
    parser.add_argument('-b', '--bitcode', default=BASE_DIR + "/CFGPass/complete.bc", help="The LLVM bitcode to analyze")
    parser.add_argument('-L', '--language', default="c++", help="Language of the project. e.g., c++, c, java, golang")
    parser.add_argument('-F', '--funcs', default=BASE_DIR + "/CFGPass/ALLFunctions", help="All functions defined in LLVM bitcode")
    args = parser.parse_args()
    LANG = args.language.lower()

    ParseConfig(args.config, args.funcs)
