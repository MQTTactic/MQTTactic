.PHONY:clean


CFGPass.so: PTA.cpp.o VarAnalysis.cpp.o CFGPass.cpp
	clang  -Wl,-znodelete -fno-rtti -fPIC -g -shared CFGPass.cpp -o ../bin/CFGPass.so $(SVF_DIR)/Release-build/lib/libSvf.a PTA.cpp.o VarAnalysis.cpp.o
PTA.cpp.o: PTA.cpp
	clang -fPIC -fno-rtti -Wno-deprecated  -g -o PTA.cpp.o -c PTA.cpp
VarAnalysis.cpp.o:  VarAnalysis.cpp
	clang -fPIC -fno-rtti -Wno-deprecated -g -o VarAnalysis.cpp.o -c VarAnalysis.cpp

config:
	clang  -Wl,-znodelete -fno-rtti -fPIC -shared AllFunctions.cpp -lLLVMDemangle -o ../bin/AllFunctions.so
	opt -load ../bin/AllFunctions.so -funcs ../complete.bc -enable-new-pm=0 -o ../complete.bc 2> ../ALLFunctions
	python3 ../../setup.py


SCA: PTA.cpp.o VarAnalysis.cpp.o CFGPass.so
	opt -load ../bin/CFGPass.so -CFG ../complete.bc -Handler=handle__pubrel -enable-new-pm=0 2> ../ALLKBBs


clean:
	rm -rf *.o
	rm -rf ../bin/*.so
