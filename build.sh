#!/usr/bin/env bash

echo > config.h
platform="$(uname -srm)"
LDFLAGS="$LDFLAGS -L/usr/local/lib/ -lurcu -lpthread -rdynamic"
CC=${CC:-cc}
CPP=${CPP:-c++}
CFLAGS="-I/usr/local/include -march=native -g2 -fno-omit-frame-pointer -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -Wno-sign-conversion $CFLAGS"
cc="$($CC -v 2>&1)"
OPTFLAGS="-O6"

function cadd() {
    echo $* >> config.h
}

case "$platform" in ####################### Linux #############################
    *Linux*)
        ROCKSDB_LDFLAGS="-lrocksdb -lsnappy -lz -lbz2 -lzstd -llz4 -ldl -lstdc++"
        MAP_LDFLAGS="-lstdc++"
        LDFLAGS="$LDFLAGS -lm"
        cadd '#define ON_LINUX  (1)'
        cadd '#define ON_DARWIN (0)'
        cadd '#include "os-linux.h"'
        ;;
esac

case "$platform" in ####################### Linux x86_64 ######################
    *Linux*x86_64*)
        ;;
esac

case "$platform" in ####################### Darwin #############################
    *Darwin*)
        ROCKSDB_LDFLAGS="-lrocksdb"
        MAP_LDFLAGS="-lstdc++"
        cadd '#define ON_LINUX  (0)'
        cadd '#define ON_DARWIN (1)'
        cadd '#include "os-darwin.h"'
        ;;
esac

case "$platform" in ####################### Darwin x86_64 ######################
    *Darwin*x86_64*)
        ;;
esac

case "$cc" in *gcc*13.1.0*)
    CFLAGS="$CFLAGS -Wno-stringop-overflow -Wno-array-bounds"
esac

case "$cc" in *gcc*)
    cadd '#include "cc-gcc.h"'
esac

case "$cc" in *clang*)
    cadd '#include "cc-clang.h"'
    OPTFLAGS="-O3"
    CFLAGS="$CFLAGS -Wno-assume"
    MAP_CFLAGS="$MAP_CFLAGS -std=gnu++11"
esac

function run() {
    echo "$* "
    $*
    rc="$?"
    if [ $rc != 0 ]
    then
        echo "failed: $rc"
        exit $?
    fi
}

runut=0
runbn=0
rocksdb=0
map=0
while [ $# != 0 ] ;do
      case "$1" in
          '-o')
              options="$options $2"
              shift
      ;;  '-u')
	      runut=1
      ;;  '-r')
	      rocksdb=1
      ;;  '-m')
	      map=1
      ;;  '-f')
	      options="$options nodebug nocounters opt"
      ;;  '-d')
	      options="$options debug counters noopt profile"
      ;;  '-D')
	      CFLAGS="$CFLAGS -D$2"
	      shift
      ;;  '-b')
	      runbn=1
      ;;  *)
	      echo "Unknown argument $1"
	      exit 1
      esac
      shift
done

for o in $options ;do
    case $o in 
       *profile*)
        LDFLAGS="$LDFLAGS -lprofiler"
    ;; *nodebug*)
       cadd '#define DEBUG  (0)'
    ;; *debug*)
       cadd '#define DEBUG  (1)'
    ;; *nocounters*)
       cadd '#define COUNTERS  (0)'
    ;; *counters*)
       cadd '#define COUNTERS  (1)'
    ;; *noopt*)
       CFLAGS="$CFLAGS -O0"
    ;; *opt*)
       CFLAGS="$CFLAGS $OPTFLAGS"
    ;; *)
       echo "Unknown option '$o'"
       exit 1
    esac       
done

run $CC $CFLAGS -DUT=1 -BN=0 t2.c $LDFLAGS -o ut
run $CC $CFLAGS -DUT=0 -DBN=1 -c t2.c
if [ $rocksdb == 1 ] ;then
   BN_CFLAGS="-DUSE_ROCKSDB=1 $ROCKSDB_LDFLAGS"
else
   BN_CFLAGS="-DUSE_ROCKSDB=0"
fi
if [ $map == 1 ] ;then
   run $CPP $MAP_CFLAGS -c map.cpp -o map.o
   BN_CFLAGS="$BN_CFLAGS -DUSE_MAP=1 map.o $MAP_LDFLAGS"
else
   BN_CFLAGS="$BN_CFLAGS -DUSE_MAP=0"
fi
run $CC $CFLAGS $BN_CFLAGS bn.c t2.o $LDFLAGS -o bn
if [ $runut == 1 ] ;then
   ./ut
fi
if [ $runbn == 1 ] ;then
   run rm -fr pages testdb/
   run ./bn -h15 -n12 -t16 -N16 -kt2 -f '1*10000000*100:insert$rnd1-6/seq0-20;1*10000000*100:lookup$rnd1-6/20;1*10000000*100:delete$rnd1-6'
fi
