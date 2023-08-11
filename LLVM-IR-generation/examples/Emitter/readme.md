#### Install Gollvm

```bash
# llvm 14
LLVM: 2c5590adfe09

gollvm: f17ba8c7708356ef447525e05cd6f2770845c7d7

gofrontend: e3bfc0889237a5bb8aa7ae30e1cff14f90a5f941

libffi: 0f2dd369cd5edcefad29b3fca4e1d08cb34f8f19

libbacktrace: d0f5e95a87a4d3e0a1ed6c069b5dae7cbab3ed2a



# llvm 12
LLVM: d055e3a0eb4e

gollvm: 87ea10c170f27b2efefab5796de60bf5632e7ff4

gofrontend: c948c2d770122932a05b62f653efa2c51f72d3ae 

libffi: e70bf987daa7b7b5df2de7579d5c51a888e8bf7d

libbacktrace: f24e9f401fde0249ca48fa98493a672e83b0f3dc


$ /bin/bash -c cd /llvm-project && git checkout 96b0b9a5e &&    cd llvm/tools/gollvm && git checkout d30fc0bf &&    cd gofrontend && git checkout ae20684902 &&    git apply /tmp/gollvm.patch &&    cd ../libgo/libffi && git checkout 8111cd0692 &&    cd ../libbacktrace && git checkout f24e9f4

$ /bin/bash -c mkdir /build-debug &&    cd /build-debug &&    cmake -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_BUILD_TYPE=RelWithDebInfo -DLLVM_USE_LINKER=gold -G Ninja ../llvm-project/llvm &&    ninja gollvm &&    ninja install-gollvm &&    ninja llvm-link


$ export PATH=$PATH:/goroot/bin/
$ export LD_LIBRARY_PATH=/build-debug/lib/:/build-debug/tools/gollvm/libgo:/goroot/lib64/
$ export GO111MODULE=on
```


#### Compile
```bash
$ git pull https://github.com/emitter-io/emitter.git
$ cd emitter
$ git checkout --progress --force -B dependabot/go_modules/github.com/valyala/fasthttp-1.34.0 refs/remotes/origin/dependabot/go_modules/github.com/valyala/fasthttp-1.34.0
$ go mod download


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
