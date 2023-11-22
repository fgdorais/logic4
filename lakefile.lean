import Lake
open Lake DSL

package logic

@[default_target]
lean_lib Logic

require std from git "https://github.com/leanprover/std4" @ "main"
