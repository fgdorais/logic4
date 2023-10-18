import Lake
open Lake DSL

package Logic

@[default_target]
lean_lib Logic

require std from git "https://github.com/fgdorais/std4" @ "nat-all"
