import Lake
open Lake DSL

package «cakeml» where

-- Pin as in candle-hol4-lean4-study (proving_nohol4/ts/lean): Batteries v4.28.0, rev 495c008c
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.28.0"

@[default_target]
lean_lib «CakeML» where
