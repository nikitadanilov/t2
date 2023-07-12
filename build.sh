#!/usr/bin/env bash

verbose=3

function log() {
	local level=$1
	shift
	if [ $level -le $verbose ]
	then
		echo $*
	fi
}

function tryconfig() {
    local cfg=$(echo $1 | tr ' /' '--')
    file="config-$cfg.h"
    if [ -f "$file" ]
    then
	log 1 "Using $file."
	cp "$file" config.h
	return 0
    else
	log 2 "No config for $1 (looked for $file)."
	return 1
    fi
}

function run() {
	local label=$1
	shift
	echo -n "$label: "
	log 2 $*
	$* > /tmp/build.log 2>&1
	if [ $? -eq 0 ]
	then
		echo "ok."
	else
		log 0 "failed: $* ($?)"
		echo "Log:"
		cat /tmp/build.log
		exit $?
	fi
}

function build() {
    CFLAGS="-O0 -I/usr/local/include -march=native -g3 -fno-omit-frame-pointer -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -Wno-sign-conversion"
    LDFLAGS="-L/usr/local/lib/ -lurcu -lpthread -rdynamic -lprofiler"
    run ut ${CC:-cc} $CFLAGS -DUT=1 -DBN=0 t2.c $LDFLAGS -o ut
    run bench ${CC:-cc} $CFLAGS -DUT=0 -DBN=1 t2.c $LDFLAGS -o bn
    run object ${CC:-cc} $CFLAGS -DUT=0 -DBN=0 -c t2.c
}

for cfg in "$(uname -a)" "$(uname -srm)" "$(uname -sm)" "$(uname -s)" "$(uname -m)" "default"
do
    tryconfig "$cfg"
    if [ $? -eq 0 ]
    then
	build
	exit
    fi
done
log 0 "No config found."
exit 1
