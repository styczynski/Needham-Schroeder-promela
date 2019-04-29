#!/bin/bash
#
# Script to check for issues with key exchange algorithm.
# MIT LICENSE
#
# Piotr Styczyński
#

cd ./src && spin -a -f "<> (processASuccess && processBSuccess)" broken_ca.pml
gcc -o pan pan.c > /dev/null 2> /dev/null
./pan
