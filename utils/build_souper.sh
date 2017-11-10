set -e

TYPE=$1

if [ -z "$TYPE" ]; then
    echo "Need to specify Release or Debug"
    exit 1
fi

if [ -z "$SOUPER_SOLVER" ]; then
    echo "Need to specify SOUPER_SOLVER"
    exit 1
fi

if [ -z "$SOUPER" ]; then
    echo "Need to specify SOUPER path"
    exit 1
fi

export CC=clang
export CXX=clang++

cd $SOUPER
rm -rf build
mkdir build
cd build
cmake -G Ninja -DTEST_SOLVER=${SOUPER_SOLVER} -DTEST_SYNTHESIS=ON \
-DCMAKE_BUILD_TYPE=${TYPE} -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_C_COMPILER=$CC ..
ninja check

