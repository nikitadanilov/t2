#!/usr/bin/env bash

echo > config.h
platform="$(uname -srm)"
LDFLAGS="$LDFLAGS -L/usr/local/lib/ -ltcmalloc -lurcu -lpthread -ldl -rdynamic"
CC=${CC:-cc}
CXX=${CXX:-c++}
CFLAGS="-I/usr/local/include -g2 -fno-omit-frame-pointer -foptimize-sibling-calls -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -Wno-sign-conversion $CFLAGS"
cc="$($CC -v 2>&1)"
OPTFLAGS="-O6 -Ofast"
distro=unknown

function cadd() {
    echo $* >> config.h
}

function cundef() {
    sym="$1"
    cadd "#if defined($sym)"
    cadd "#undef $sym"
    cadd "#endif"
}

function cpuflag() {
        :
}

case "$platform" in ####################### Linux #############################
    (*Linux*)
        ROCKSDB_LDFLAGS="-lrocksdb -lsnappy -lz -lbz2 -lzstd -llz4 -ldl -lstdc++"
        LMDB_LDFLAGS="-L/usr/local/lib -llmdb"
        MAP_LDFLAGS="-lstdc++"
        LDFLAGS="$LDFLAGS -lm -latomic -lunwind"
        cadd '#define ON_LINUX  (1)'
        cadd '#define ON_DARWIN (0)'
        cadd '#include "os-linux.h"'
        function cpuflag() {
                flag="$1"
                if command -v lscpu >/dev/null 2>/dev/null ;then
                        lscpu | grep " $flag " >/dev/null 2>/dev/null && echo "-m$flag"
                else
                        cat /proc/cpuinfo | grep " $flag " >/dev/null 2>/dev/null && echo "-m$flag"
                fi
        }
	grep -q Ubuntu /etc/os-release 2>/dev/null && distro=ubuntu
        ;;
esac

case "$platform" in ####################### Linux x86_64 ######################
    (*Linux*x86_64*)
        ;;
esac

case "$platform" in
    (*x86_64*)
	# popcnt for ilog2()
	# cx16 for mag_{get,put}() (128-bit CAS)
        MFLAGS="popcnt cx16"
        ;;
esac

case "$platform" in ####################### Darwin #############################
    (*Darwin*)
        ROCKSDB_LDFLAGS="-lrocksdb"
        LMDB_LDFLAGS="-L/usr/local/lib -llmdb"
        MAP_LDFLAGS="-lstdc++"
        cadd '#define ON_LINUX  (0)'
        cadd '#define ON_DARWIN (1)'
        cadd '#include "os-darwin.h"'
        function cpuflag() {
                sysctl -a | grep machdep.cpu.features | grep -i " $1 " >/dev/null 2>/dev/null && echo "-m$flag"
        }
	distro=darwin
        ;;
esac

case "$platform" in ####################### Darwin x86_64 ######################
    (*Darwin*x86_64*)
        ;;
esac

case "$cc" in (*gcc*13.1.0*)
    CFLAGS="$CFLAGS -Wno-stringop-overflow -Wno-array-bounds"
esac

case "$cc" in (*gcc\ version*)
    cadd '#include "cc-gcc.h"'
esac

case "$cc" in (*clang*)
    cadd '#include "cc-clang.h"'
    OPTFLAGS="-O3 -Ofast"
    CFLAGS="$CFLAGS -Wno-assume"
    MAP_CFLAGS="$MAP_CFLAGS -std=gnu++11"
esac

for flag in $MFLAGS ;do
    OPTFLAGS="$OPTFLAGS $(cpuflag $flag)"
done

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

function setup_prereq() {
    case "$distro" in
	(ubuntu)
	    run sudo apt install -y gcc make automake autoconf libtool g++ libunwind-dev libgoogle-perftools-dev liblmdb0 liblmdb-dev
    ;;  (darwin)
	    run brew install automake autoconf libtool gcc gperftools
    ;;  (*)
	    echo "Unknown distro '$distro'"
	    exit 1
    esac
}

function setup() {
    setup_prereq
    echo Installing userspace-rcu
    run rm -fr userspace-rcu
    run git clone git://git.liburcu.org/userspace-rcu.git
    run cd userspace-rcu
    run ./bootstrap
    run ./configure
    run make
    run sudo make install
    run cd ..
    run rm -fr userspace-rcu
}

runut=0
runbn=0
rocksdb=0
lmdb=0
map=0
while [ $# != 0 ] ;do
      case "$1" in
          ('-o')
              options="$options $2"
              shift
      ;;  ('-u')
	      runut=1
      ;;  ('-r')
	      rocksdb=1
      ;;  ('-l')
	      lmdb=1
      ;;  ('-m')
	      map=1
      ;;  ('-f')
	      options="$options nodebug nocounters opt"
      ;;  ('-d')
	      options="$options debug counters noopt profile"
      ;;  ('-D')
	      CFLAGS="$CFLAGS -D$2"
	      shift
      ;;  ('-b')
	      runbn=1
      ;;  ('-S')
	      setup
	      exit 0
      ;;  (*)
	      echo "Unknown argument $1"
	      exit 1
      esac
      shift
done

for o in $options ;do
    case $o in 
       (*profile*)
        LDFLAGS="$LDFLAGS -lprofiler"
    ;; (*nodebug*)
       cundef DEBUG
       cadd '#define DEBUG  (0)'
    ;; (*debug*)
       cundef DEBUG
       cadd '#define DEBUG  (1)'
    ;; (*nocounters*)
       cundef COUNTERS
       cadd '#define COUNTERS  (0)'
    ;; (*counters*)
       cundef COUNTERS
       cadd '#define COUNTERS  (1)'
    ;; (*noopt*)
       CFLAGS="$CFLAGS -O0"
    ;; (*opt*)
       CFLAGS="$CFLAGS $OPTFLAGS"
    ;; (*)
       echo "Unknown option '$o'"
       exit 1
    esac       
done

run $CC $CFLAGS -DUT=1 -BN=0 t2.c $LDFLAGS -o ut
run $CC $CFLAGS -DUT=0 -DBN=1 -c t2.c
if [ $rocksdb == 1 ] ;then
   BN_CFLAGS="-DUSE_ROCKSDB=1"
   BN_LDFLAGS="$ROCKSDB_LDFLAGS"
else
   BN_CFLAGS="-DUSE_ROCKSDB=0"
fi
if [ $lmdb == 1 ] ;then
   BN_CFLAGS="$BN_CFLAGS -DUSE_LMDB=1"
   BN_LDFLAGS="$BN_LDFLAGS $LMDB_LDFLAGS"
else
   BN_CFLAGS="$BN_CFLAGS -DUSE_LMDB=0"
fi
if [ $map == 1 ] ;then
   run $CXX $MAP_CFLAGS -c map.cpp -o map.o
   BN_CFLAGS="$BN_CFLAGS -DUSE_MAP=1"
   BN_LDFLAGS="$BN_LDFLAGS map.o $MAP_LDFLAGS"
else
   BN_CFLAGS="$BN_CFLAGS -DUSE_MAP=0"
fi
run $CC $CFLAGS $BN_CFLAGS bn.c t2.o $BN_LDFLAGS $LDFLAGS -o bn
if [ $runut == 1 ] ;then
    export LD_LIBRARY_PATH=/usr/local/lib
    run ulimit -n 32000
    run ulimit -c unlimited
    run mkdir pages log
    run ./ut
fi
if [ $runbn == 1 ] ;then
    run rm -fr pages log testdb
    run mkdir pages log
    run ./bn -h22 -n12 -t14 -N16 -kt2 -f '1*10000000*100:insert$rnd1-6/seq0-20;1*10000000*100:lookup$rnd1-6/20;1*10000000*100:delete$rnd1-6'
fi
