import Lake

open Lake DSL

package Thesis

require CvxLean from git "https://github.com/verified-optimization/CvxLean" @ "main"

@[default_target]
lean_lib Thesis
