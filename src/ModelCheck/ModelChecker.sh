#! /bin/bash

cd $(dirname $(readlink -f "$0"))
echo "Model Checking...\n"
spin -a ConcreteModel/ConcreteModel.pml
mkdir build
cd build
gcc -DMEMLIM=16384 -DVECTORSZ=4096 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan ../pan.c
./pan -m4000 -E -c0 -e -n  > result.txt
cd ../
python3 sort.py
echo "Analyzing done!\n"
echo "see Spinresults/New_*"


