
#### 0x01 Enviroment
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

#### 0x02 Dependency

```bash
$ git clone https://github.com/eclipse/mosquitto.git

# install llvm
$ sudo apt-get install clang-9 llvm-9 llvm-9-dev llvm-9-tools
$ sudo apt install build-essential cmake git

# install wllvm
$ pip3 install wllvm -i https://pypi.tuna.tsinghua.edu.cn/simple

# install dependencies for mosquitto
$ apt install libc-ares-dev libwebsockets-dev  libevent-pthreads-2.1-7  uthash-dev  xsltproc libcjson-dev libcjson-dev 

```

#### 0x03 Compile

```bash

# modify the compile flags in mosquitto-2.0.11/config.mk
BROKER_CFLAGS:=${CFLAGS} -stdlib=libc++ -static -g -O0 -Xclang -disable-O0-optnone  -fno-discard-value-names -disable-llvm-passes 


$ export  CFLAGS="-g -O0 -Xclang -disable-O0-optnone  -fno-discard-value-names"
$ export LLVM_COMPILER=clang CC=wllvm & make WITH_DOCS=no
$ extract-bc src/mosquitto

# link mosquitto.bc and lib.a.bc
$ llvm-link ./mosquitto.bc ./libc.a.bc -o complete.bc
```
