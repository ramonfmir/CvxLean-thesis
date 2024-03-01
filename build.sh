#!/bin/bash

# Build this project.

lake clean
lake update
lake exe cache get
lake build 

# Build the CvxLean dependency.

cd .lake/packages/CvxLean

lake exe cache get
lake run EggClean
lake build EggPreDCP
lake build CvxLean
lake build CvxLeanTest

cd ../../..

# Copy egg-pre-dcp.

cp -r .lake/packages/CvxLean/egg-pre-dcp .

# Re-build the code in this repository, with `pre_dcp` working.

rm -rf .lake/build 
lake build
