#!/bin/bash

set -e

# make sure redis server and DB are in the right state

# run this in a clean dir

# -mllvm -stats

if [ -z "$SOUPER" ]; then
    echo "Need to set SOUPER"
    exit 1
fi

export MY_LLVM_SRC=$HOME/work/llvm

if [ -z "$MY_LLVM_SRC" ]; then
    echo "Need to set MY_LLVM_SRC"
    exit 1
fi

#######################################################################

# export SOUPER_NO_SOUPER=1

#######################################################################

ulimit -m 16000000 -v 16000000

#export SOUPER_STATIC_PROFILE=1
#export SOUPER_DYNAMIC_PROFILE=1
#export SOUPER_NO_HARVEST_DATAFLOW_FACTS=1
#export SOUPER_NO_EXPLOIT_UB=1
#export SOUPER_EXPLOIT_BLOCKPCS=1

#export SOUPER_SOLVER=-stp-path=/usr/local/bin/stp
#export SOUPER_SOLVER="-z3-path=/usr/local/bin/z3"

export SOUPER_IGNORE_SOLVER_ERRORS=1

#export SOUPER_INFER_INT=1

export SOUPER_NO_INFER=1

#export CFLAGS='-O -fsanitize=signed-integer-overflow -fsanitize=shift'
#export CXXFLAGS=$CFLAGS

#${MY_LLVM_SRC}/configure --disable-bindings --enable-optimized --enable-assertions CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++"
#time make VERBOSE=1 CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++" -j10

#CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++" cmake -G  "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_ASSERTIONS=ON ${MY_LLVM_SRC}
#time make VERBOSE=1 -j20
#make check -j20
#CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++" cmake -G  "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_ASSERTIONS=ON ${MY_LLVM_SRC} # -DLLVM_ENABLE_LTO=Thin
#time make VERBOSE=1 -j1
#make check -j1

#CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++" cmake -G Ninja -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_ASSERTIONS=ON -DLLVM_ENABLE_LIBCXX=ON ${MY_LLVM_SRC}
CC="${SOUPER}/build/sclang" CXX="${SOUPER}/build/sclang++" cmake -G Ninja -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_ASSERTIONS=ON ${MY_LLVM_SRC}
time ninja
ninja check

#########################################################################
