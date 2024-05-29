import Lake

open Lake DSL

package Thesis

require CvxLean from git "https://github.com/verified-optimization/CvxLean" @ "32443811fe7184559f784c9aedce48a4bd2ff3ca"

@[default_target]
lean_lib Thesis
