#!/usr/bin/env python3

import subprocess
import os

# Change working dir to the script path
os.chdir(os.path.dirname(os.path.abspath(__file__)))

run = subprocess.run(['mcrl22lps', '-v', 'food_package.mcrl2'], stdout=subprocess.PIPE, check=True)
run = subprocess.run(['lpssuminst'], input=run.stdout, stdout=subprocess.PIPE, check=True)
run = subprocess.run(['lps2pbes', '-v', '-f', 'sustained_delivery.mcf'], input=run.stdout, stdout=subprocess.PIPE, check=True)
subprocess.run(['pbesconstelm', '-ve', '-', 'sustained_delivery.pbesconstelm.pbes'], input=run.stdout, stdout=subprocess.PIPE, check=True)

# We use -rjittyc is used below, which does work on linux and mac, and not on windows.
# Note that the generated bes is huge.
subprocess.run(['pbes2bool', '-v', '-zdepth-first', '-s3', 'sustained_delivery.pbesconstelm.pbes'], shell=True, check=True)