set -e

TYPE=$1

rm -rf third_party build

if [ -z "$TYPE" ]; then
    echo "Need to specify Release or Debug"
    exit 1
fi

if [ -z "$SOUPER_SOLVER" ]; then
    echo "Need to specify SOUPER_SOLVER"
    exit 1
fi

export CC=clang
export CXX=clang++

# -DLLVM_ENABLE_ASSERTIONS=true \
# -DLLVM_BINUTILS_INCDIR=/usr/include

./update_deps.sh ${TYPE} -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_C_COMPILER=$CC

mkdir build
cd build
cmake -G Ninja -DTEST_SOLVER=${SOUPER_SOLVER} -DTEST_SYNTHESIS=ON \
-DCMAKE_BUILD_TYPE=${TYPE} -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_C_COMPILER=$CC ..
ninja check

