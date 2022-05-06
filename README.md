### MQTTactic
The MQTTactic is our tool for evaluating the security of the MQTT Broker with static analyses. More details and instructions will be uploaded/updated later.


### Getting started
#### 1. Install
* The MQTTactic works on LLVM IR, So LLVM must be available in your system. Currently, the supported LLVM versions are `llvm-9`, `llvm-10`, `llvm-11`, `llvm-12`, and `llvm-13`.
* Haybale for symbolic execution
`git clone https://github.com/MQTTactic/Haybale`


#### 2. Usage
* Configuration
	A simple example can be found in `Include/`.
* CFG analysis
```
$ clang  -Wl,-znodelete -fno-rtti -fPIC -shared AllFunctions.cpp -o AllFunctions.so
$ opt -load ./AllFunctions.so -funcs ./complete.bc -enable-new-pm=0 -o complete.bc 2> ./ALLFunctions


$ clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o CFGPass.so
$ opt -load ./CFGPass.so -CFG ./complete.bc -enable-new-pm=0 -o /dev/null 2> OUTPUT/xxx.output
```

* Symbolic Execution
```
$ cd SymbolicExecution/ && cargo build
$ cd target/debug/
$ ./SE "handle__pubrel" "{config_handle__pubrel}" "{type_num}" "{LLVM_bitcode_dir}" > ModelCheck/SymbolicExecutionResults/handle__pubrel/Type-{type_num}.log 2>&1
```

* Model Check
```
spin -a ConcreteModel.pml
mkdir build
gcc -DMEMLIM=16384 -DVECTORSZ=4096 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan ../pan.c
./pan -m40000 -E -c0 -e -n  > result.txt
```
