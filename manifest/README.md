# manifest
Freeze pins, theory list, dependency order and batch plan.

`milestone1/statements.jsonl` is the HOL4 export of the 25 theories (`workflow/export/run_export.sh`): one JSON object per theorem, definition, axiom,
constant and type, with the type variables, the constants used, HOL4's printing, and the kernel term (`tys` table plus `["v"|"c"|"a"|"l", ...]`
nodes, see `workflow/export/export_theories.sml`). `export_counts.tsv` compares it with `theories.tsv`.
