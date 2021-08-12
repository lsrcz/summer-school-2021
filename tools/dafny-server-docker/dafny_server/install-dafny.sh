#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


set -e
set -x

mkdir .dafny
cd .dafny

#git clone https://github.com/secure-foundations/dafny.git
# actually let's use official dafny:
git clone https://github.com/dafny-lang/dafny.git
cd dafny
make exe
cd ..

if [ `uname` == "Linux" ]; then
    wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip
    unzip z3-4.8.5-x64-ubuntu-16.04.zip
    cp -r z3-4.8.5-x64-ubuntu-16.04 dafny/Binaries/z3/
else
    echo UH OH SCRIPT BROKE
    exit -1
fi
