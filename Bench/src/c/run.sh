#!/bin/bash
CWD=$(dirname "$0")
gcc -O2 $CWD/main.c -o $CWD/c_bench
$CWD/c_bench
rm -f $CWD/c_bench