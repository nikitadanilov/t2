#!/usr/bin/env bash

echo > config.h
platform="$(uname -srm)"
LDFLAGS="$LDFLAGS -L/usr/local/lib/ -lurcu -lpthread -rdynamic"
CC=${CC:-cc}
CFLAGS="-I/usr/local/include -march=native -g2 -fno-omit-frame-pointer -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -Wno-sign-conversion $CFLAGS"

function cadd() {
    echo $* >> config.h
}

case "$platform" in ####################### Linux #############################
    *Linux*)
        ROCKSDB_LDFLAGS="-lrocksdb -lsnappy -lz -lbz2 -lzstd -llz4 -ldl -lstdc++"
        LDFLAGS="$LDFLAGS -lm"
        cadd '#define ON_LINUX  (1)'
        cadd '#define ON_DARWIN (0)'
        cadd '#include <sys/syscall.h>'
        cadd '#include <sys/time.h>'
        ;;
esac

case "$platform" in ####################### Linux x86_64 ######################
    *Linux*x86_64*)
        ;;
esac

case "$platform" in ####################### Darwin #############################
    *Darwin*)
        ROCKSDB_LDFLAGS="-lrocksdb"
        cadd '#define ON_LINUX  (0)'
        cadd '#define ON_DARWIN (1)'
        cadd '#include <sys/uio.h>'
        cadd '#include <mach/mach.h>'
        cadd '#include <mach/mach_vm.h>'
        ;;
esac

case "$platform" in ####################### Darwin x86_64 ######################
    *Darwin*x86_64*)
        ;;
esac

function run() {
    echo "$* "
    $*
    if [ $? != 0 ]
    then
        log 0 "failed: $* ($?)"
        exit $?
    fi
}

runut=0

while [ $# != 0 ] ;do
      case "$1" in
          '-o')
              options="$options $2"
              shift
      ;;  '-u')
	      runut=1
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
       CFLAGS="$CFLAGS -O6"
    ;; *)
       echo "Unknown option '$o'"
       exit 1
    esac       
done

run $CC $CFLAGS -DUT=1 -BN=0 t2.c $LDFLAGS -o ut
run $CC $CFLAGS -DUT=0 -DBN=1 -c t2.c
run $CC $CFLAGS bn.c t2.o $LDFLAGS -lrocksdb $ROCKSDB_LDFLAGS -o bn
if [ $runut == 1 ] ;then
   ./ut
fi
