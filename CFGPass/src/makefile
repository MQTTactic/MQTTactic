.PHONY:clean


CFGPass.so: PTA.cpp.o VarAnalysis.cpp.o CFGPass.cpp
	clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o  ../bin/CFGPass.so /home/szx/Documents/tools/SVF/Release-build/lib/libSvf.a PTA.cpp.o VarAnalysis.cpp.o
PTA.cpp.o: PTA.cpp
	clang -fPIC -fno-rtti -Wno-deprecated -o PTA.cpp.o -c PTA.cpp
VarAnalysis.cpp.o:  VarAnalysis.cpp
	clang -fPIC -fno-rtti -Wno-deprecated -o VarAnalysis.cpp.o -c VarAnalysis.cpp

config:
	clang  -Wl,-znodelete -fno-rtti -fPIC -shared AllFunctions.cpp -o ../bin/AllFunctions.so
	opt -load ../bin/AllFunctions.so -funcs ../complete.bc -enable-new-pm=0 -o ../complete.bc 2> ../ALLFunctions
	python3 ../../setup.py


varpass: PTA.cpp.o VarAnalysis.cpp.o VarAnalysisPass.cpp
	clang  -Wl,-znodelete -fno-rtti -fPIC -shared VarAnalysisPass.cpp -o  ../bin/VarAnalysisPass.so /home/szx/Documents/tools/SVF/Release-build/lib/libSvf.a PTA.cpp.o VarAnalysis.cpp.o
	opt -load ../bin/VarAnalysisPass.so -VarAnalysisPass ../complete.bc -enable-new-pm=0 2> ../ALLKBBs


clean:
	rm -rf *.o
	rm -rf ../bin/*.so