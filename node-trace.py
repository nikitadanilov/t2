#!/usr/bin/env python3

import sys
from collections import defaultdict

def trace(fname):
    S = defaultdict(list)
    T = defaultdict(list)
    L = defaultdict(int)
    with open(fname, 'r') as f:
        for line in f:
            # 0         1         2         3         4         5         6
            # 0123456789012345678901234567890123456789012345678901234567890
            # N   2796330504163000             143931 0000910000000203 0 L
            if line[0] == 'N':
                time  = int(line[ 4:20])
                bolt  = int(line[21:39])
                addr  = int(line[40:56], 16)
                level = int(line[57:58])
                state =     line[59:60]
                T[addr].append(bolt)
                S[addr].append(state)
                L[addr] = max(L[addr], level)
    for addr in S:
        print('{:016x} {:1d}'.format(addr, L[addr]), end = ' ')
        for idx, state in enumerate(S[addr]):
            if idx > 0 and T[addr][idx - 1] != 0:
                print(int((T[addr][idx] - T[addr][idx - 1]) / 30) * '.', end = '')
            print(state, end = '')
        print('')

if __name__ == "__main__":
    trace(sys.argv[1])
