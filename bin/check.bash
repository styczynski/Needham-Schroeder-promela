#!/bin/bash

spin -a -f "<> (processASuccess && processBSuccess)" smart_c.pml
gcc -o pan pan.c > /dev/null 2> /dev/null
./pan
