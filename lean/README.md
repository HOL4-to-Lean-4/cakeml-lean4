# lean

One Lake project: package `cakeml`, Lean 4.28.0, Batteries v4.28.0 (rev `495c008c`, as in `candle-hol4-lean4-study/proving_nohol4/ts/lean`) as the
only dependency. One module per HOL4 theory, mirroring CakeML's directory tree: `CakeML/Semantics/Proofs/TypeSound.lean` is
`semantics/proofs/typeSoundScript.sml` (rule in `workflow/modules.py`). `CakeML.lean` imports every milestone module. The milestone-1 modules
are empty stubs until the translation is accepted.

    lake build        # builds the skeleton and Batteries (needs network for Batteries on the first build only)

Regenerate the skeleton after adding a milestone: `python3 workflow/mk_lean_skeleton.py`.
