#!/bin/bash

cd ./src && spin -a -f "<> (processASuccess && processBSuccess)" with_ca.pml
gcc -o pan pan.c > /dev/null 2> /dev/null
./pan
