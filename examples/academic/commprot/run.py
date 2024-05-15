#!/usr/bin/env python3

import subprocess
import os

# Change working dir to the script path
os.chdir(os.path.dirname(os.path.abspath(__file__)))

# The generated state space is huge, well over 10^8 states. Explicit verification of the state
# space is therefore not possible. One can use highway search, using e.g. --todo-max=1000,
# searching with 10000 lanes through the state space for deadlocks. The total number of 
# states to be explored is limited to 100000 in this example. 
run = subprocess.run(['mcrl22lps', '-v', '-n', 'commprot.mcrl2', 'commprot.lps'], stdout=subprocess.PIPE, check=True)
run = subprocess.run(['lpsparunfold', '-sList(UDPsp)', '-sList(CFsp)', '-n5'], input=run.stdout, stdout=subprocess.PIPE, check=True)
run = subprocess.run(['lpsparunfold', 'UDPsp', '-', 'commprot.lps'], input=run.stderr, stdout=subprocess.PIPE, check=True)

subprocess.run(['lps2lts', '-D', '--strategy=highway', '--cached', '--todo-max=1000', '-l100000', '-v', 'commprot.lps'], check=True)

# Checking the properties below does not work on an ordinary computer, given 
# the size of the state space. 
subprocess.run(['lps2pbes', '-v', '-fnodeadlock.mcf', 'commprot.lps', 'commprot.nodeadlock.lps'], stdout=subprocess.PIPE, check=True)