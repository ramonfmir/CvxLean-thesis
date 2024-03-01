#!/bin/bash

# Build this project.

lake update
lake exe cache get
lake build 

# Build the CvxLean dependency.

cd .lake/packages/CvxLean

lake update
lake exe cache get
lake run EggClean
lake build EggPreDCP
lake build CvxLean
lake build CvxLeanTest
