#!/usr/bin/env python3

import sys
from collections import defaultdict

def trace(fname):
    S = defaultdict(list)
    T = defaultdict(list)
    L = defaultdict(int)
    with open(fname, 'r') as f:
        for line in f:
            # 0         1         2         3         4
            # 01234567890123456789012345678901234567890123456789
            # N   2430467499187000 00006e0000000200 0 L
            if line[0] == 'N':
                time  = int(line[ 4:20])
                addr  = int(line[21:37], 16)
                level = int(line[38:39])
                state =     line[40:41]
                T[addr].append(time)
                S[addr].append(state)
                L[addr] = max(L[addr], level)
    for addr in S:
        rep = ""
        for idx, state in enumerate(S[addr]):
            if idx > 0 and T[addr][idx - 1] != 0:
                diff = int((T[addr][idx] - T[addr][idx - 1]) / 100000000)
                rep += diff * "."
            rep += state
        print("%016x %1d %s" % (addr, L[addr], rep))

if __name__ == "__main__":
    trace(sys.argv[1])
