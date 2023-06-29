#!/bin/sh

function tryconfig() {
    local cfg=$(echo $1 | tr ' ' '-')
    file="config-$cfg.h"
    if [ -f "$file" ]
    then
	echo "Using $file."
	cp "$file" config.h
	return 0
    else
	echo "No config for $1 (looked for $file)."
	return 1
    fi
}

function build() {
    cc -g2 -O0 t2.c -L/usr/local/lib/ -lurcu
    if [ $? -eq 0 ]
    then
	echo "Done."
	exit 0
    else
	echo "Build failed."
	exit 1
    fi
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
echo "No config found."
exit 1
