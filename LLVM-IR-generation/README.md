# LLVM-IR-generation


## Frontends for LLVM
> Some projects are still in the development stage and may not fully support language features.

| Language   | Tool(s)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| ---------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| python     | - [Numba](https://numba.readthedocs.io/en/stable/reference/envvars.html#envvar-NUMBA_DUMP_LLVM)<br />- [numba/llvmlite: A lightweight LLVM python binding for writing JIT compilers (github.com)](https://github.com/numba/llvmlite)                                                                                                                                                                                                                                                                                                                                                                            |
| java       | - [polyglot-compiler/JLang: JLang: Ahead-of-time compilation of Java programs to LLVM](https://github.com/polyglot-compiler/JLang)<br />- [superblaubeere27/masxinlingvonta: Compiles Java ByteCode to LLVM IR (for obfuscation purposes)](https://github.com/superblaubeere27/masxinlingvonta)<br />- https://vmkit.llvm.org/<br />- [mirkosertic/Bytecoder: Framework to interpret and transpile JVM bytecode to JavaScript, OpenCL or WebAssembly.](https://github.com/mirkosertic/Bytecoder)<br />- [Kotlin/Native libraries \| Kotlin (kotlinlang.org)](https://kotlinlang.org/docs/native-libraries.html) |
| javascript | - [SirJosh3917/jssat: Compile JS into LLVM IR - JavaScript Static Analysis Tool](https://github.com/SirJosh3917/jssat)<br />- [wizardpisces/js-ziju: Compile javascript to LLVM IR, x86 assembly and self interpreting](https://github.com/wizardpisces/js-ziju)                                                                                                                                                                                                                                                                                                                                                |
| erlang     | - [lumen/lumen: An alternative BEAM implementation, designed for WebAssembly](https://github.com/lumen/lumen)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| golang     | - [gollvm - Git at Google](https://go.googlesource.com/gollvm/)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| rust       | - [rust-osdev/cargo-xbuild: Automatically cross-compiles the sysroot crates core, compiler_builtins, and alloc.](https://github.com/rust-osdev/cargo-xbuild)                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| Kotlin     | - [Kotlin/Native libraries \| Kotlin (kotlinlang.org)](https://kotlinlang.org/docs/native-libraries.html)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |


------------------------

## Instruction

> The installation of tools and LLVM enviroments will not be repeated here.

* Test Enviroment
> $ cat /etc/os-release
```
NAME="Ubuntu"
VERSION="20.04.3 LTS (Focal Fossa)"
ID=ubuntu
ID_LIKE=debian
PRETTY_NAME="Ubuntu 20.04.3 LTS"
VERSION_ID="20.04"
HOME_URL="https://www.ubuntu.com/"
SUPPORT_URL="https://help.ubuntu.com/"
BUG_REPORT_URL="https://bugs.launchpad.net/ubuntu/"
PRIVACY_POLICY_URL="https://www.ubuntu.com/legal/terms-and-policies/privacy-policy"
VERSION_CODENAME=focal
UBUNTU_CODENAME=focal
```

> $ uname -a
```
5.15.0-69-generic #76~20.04.1-Ubuntu SMP Mon Mar 20 15:54:19 UTC 2023 x86_64 x86_64 x86_64 GNU/Linux
```

##### C/C++

```bash
# install wllvm
$ pip3 install wllvm

# generate LLVM IR for a single file
$ clang  -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone  -fno-discard-value-names example.c -o example.bc

# generate llvm ir for a project
# 1. Change the compiler to `clang`/`clang++` and change the compiler flags. You also can add compiler flags to CMakeLists.txt.
$ export CFLAGS="-g -O0 -Xclang -disable-O0-optnone  -fno-discard-value-names"
# 2. Compile and link multiple files
$ export LLVM_COMPILER=clang CC=wllvm make
# 3. Extract LLVM bitcode
$ extract-bc {bin/xx}

```


##### Golang
> https://go.googlesource.com/gollvm/
```bash
# Record the instructions compiled by Go compiler
$ go build -gccgoflags "-static-libgo -S" -work -x 1> transcript.txt 2>&1

# Extract gollvm instructions, remember to delete the cache before compiling
$ egrep '(WORK=|llvm-goc -c|cd)' transcript.txt > compile.sh

# clean the cache
$ rm -rf ~/.cache/go-build/*
$ go clean --modcache

# modify the instructions in compile.sh to generate LLVM IR:
/usr/local/bin/llvm-goc -c -O2 -g -m64 -fdebug-prefix-map=$WORK=/tmp/go-build -gno-record-gcc-switches -fgo-relative-import-path=_/build-debug/bin "-S -emit-llvm" -o test.ll -I $WORK/b001/_importcfgroot_ -static-libgo ./mypackage2.go $WORK/b001/_gomod_.go
```

And here is a simple script for the last step.
```python
import re

origin = open("compile.sh")
x = origin.read().split("\n")

result = []
count = 0
for i in x:
     m = re.findall("-fgo-pkgpath=(.*) -o", i)
     print(m)
     if(m == [] or m == None):
          result.append(i)
     elif("VolantMQ" in m[0]):
          n = re.sub("-o \$WORK/.*/_go_.o",f"-S -emit-llvm -fno-inline -o /tmp/{count}.ll",i)
          n = re.sub("-O2","-O1", n)
          n = re.sub("\./","`pwd`/",n)
          result.append(n)
          count += 1

output = open("result.sh",'w')
for i in result:
     output.write(i+'\n')
output.close()
origin.close()
```


##### Rust

```bash
$ cargo rustc -- --emit=llvm-ir -g -C no-prepopulate-passes -C link-dead-code=yes -C default-linker-libraries=no
```


##### Kotlin
> [Get started with Kotlin/Native using the command-line compiler | Kotlin (kotlinlang.org)](https://kotlinlang.org/docs/native-command-line-compiler.html#write-hello-kotlin-native-program)
> [Release Kotlin 1.7.10 · JetBrains/kotlin (github.com)](https://github.com/JetBrains/kotlin/releases/tag/v1.7.10)

```bash
$ kotlinc-native hello.kt -o hello -p bitcode
```

## Open-source MQTT brokers (date:2023-06-23)

**The tool for counting lines of code:**

https://github.com/AlDanial/cloc



| Repository                          | Stars | Lang       | Lines of Code |
| ----------------------------------- | ----- | ---------- | ------------- |
| eclipse/mosquitto                   | 7.4k  | C          | 45,706        |
| emqx/nanomq                         | 928   | C          | 19,223        |
| martin-ger/uMQTTBroker              | 400   | C          | 2,473         |
| codepr/sol                          | 90    | C          | 5,818         |
| nopnop2002/esp-idf-mqtt-broker      | 97    | C          | 789           |
| eclipse/amlen                       | 37    | C          | 497,707       |
| dotnet/MQTTnet                      | 3.6k  | C#         | 31,671        |
| xamarin/MQTT                        | 296   | C#         | 12,474        |
| gnatmq/gnatmq                       | 122   | C#         | 5,669         |
| halfgaar/FlashMQ                    | 91    | C++        | 14,689        |
| hsaturn/TinyMqtt                    | 137   | C++        | 4,343         |
| homewsn/whsnbg                      | 42    | C++        | 58,083        |
| atilaneves/mqttcpp                  | 40    | C++        | 11,728        |
| atilaneves/mqtt                     | 59    | D          | 1,156         |
| hansonkd/skyline                    | 40    | Elixir     | 2,619         |
| ConnorRigby/creep                   | 13    | Elixir     | 1,684         |
| processone/ejabberd                 | 5.5k  | Erlang     | 107,074       |
| emqx/emqx                           | 11.8k | Erlang     | 222,999       |
| rabbitmq/rabbitmq-server            | 10.8k | Erlang     | 215,758       |
| vernemq/vernemq                     | 3k    | Erlang     | 51,254        |
| alekras/erl.mqtt.server             | 18    | Erlang     | 4,994         |
| gbour/wave                          | 25    | Erlang     | 3,103         |
| emitter-io/emitter                  | 3.6k  | Golang     | 14,886        |
| mainflux/mainflux                   | 2.1k  | Golang     | 997,652       |
| fhmq/hmq                            | 1.2k  | Golang     | 3,714         |
| VolantMQ/volantmq                   | 951   | Golang     | 9,037         |
| DrmagicE/gmqtt                      | 877   | Golang     | 27,687        |
| mochi-co/mqtt                       | 614   | Golang     | 288,471       |
| luanjunyi/gossipd                   | 101   | Golang     | 1,477         |
| hb-chen/gmqtt                       | 78    | Golang     | 5,702         |
| c16a/hermes                         | 56    | Golang     | 1,789         |
| alsm/hrotti                         | 124   | Golang     | 2,389         |
| TheThingsIndustries/mystique        | 22    | Golang     | 3,717         |
| zentures/surgemq                    | 1.8k  | Golang     | 4,755         |
| funkygao/mhub                       | 32    | Golang     | 2,899         |
| lpeterse/haskell-hummingbird        | 21    | Haskell    | 1,647         |
| hivemq/hivemq-community-edition     | 927   | Java       | 136,356       |
| Cicizz/jmqtt                        | 485   | Java       | 5,569         |
| moquette-io/moquette                | 2.2k  | Java       | 14,767        |
| Wizzercn/MqttWk                     | 511   | Java       | 3,192         |
| mtsoleimani/cassandana              | 65    | Java       | 5,410         |
| apache/activemq                     | 2.2k  | Java       | 415,820       |
| apache/activemq-artemis             | 865   | Java       | 584,802       |
| iitsoftware/swiftmq-ce              | 13    | Java       | 160,869       |
| quickmsg/smqtt                      | 861   | Java       | 9,380         |
| EnMasseProject/enmasse              | 190   | Java       | 1,201,834     |
| lets-mica/mica-mqtt                 | 171   | Java       | 12,242        |
| joey-happy/jo-mqtt                  | 137   | Java       | 5,195         |
| ShiCloud/iot-mqtt                   | 60    | Java       | 4,517         |
| MrHKing/mmqtt                       | 70    | Java       | 22,660        |
| longkerdandy/mithqtt                | 39    | Java       | 5,565         |
| oci-pronghorn/PronghornGateway      | 15    | Java       | 3,135         |
| Dovakin-IO/DovakinMQ                | 15    | Java       | 2,952         |
| anyflow/lannister                   | 22    | Java       | 7,148         |
| [JoramMQ](https://joram.ow2.io/)    | N/A   | java       | 131,755       |
| moscajs/mosca                       | 3.2k  | JavaScript | 9,514         |
| FarmBot-Labs/mqtt-gateway           | 41    | JavaScript | 864           |
| moscajs/aedes                       | 1.6k  | JavaScript | 8,490         |
| ioBroker/ioBroker.mqtt              | 45    | JavaScript | 4,964         |
| martin-doyle/node-red-contrib-aedes | 52    | JavaScript | 1,225         |
| PatrickKalkman/clima-link           | 20    | JavaScript | 8,782         |
| davidepianca98/KMQTT                | 73    | Kotlin     | 9,748         |
| LabVIEW-Open-Source/LV-MQTT-Broker  | 40    | LabVIEW    | 1,710         |
| GRIDSystemSAS/GS.GRID               | 24    | Pascal     | 204,569       |
| beerfactory/hbmqtt                  | 785   | Python     | 6207          |
| crossbario/crossbar                 | 2k    | Python     | 66,991        |
| eerimoq/mqttools                    | 57    | Python     | 4,396         |
| bytebeamio/rumqtt                   | 1.1k  | Rust       | 24,891        |
| bschwind/mqtt-broker                | 116   | Rust       | 5,207         |
| rmqtt/rmqtt                         | 249   | Rust       | 16,588        |
| pyrinas-iot/pyrinas-server-rs       | 38    | Rust       | 3,267         |
| butaji/JetMQ                        | 45    | Scala      | 2,944         |
