# lean-LCS v0.1.1

This release migrates lean-LCS from Lean and Mathlib v4.34.0 to **v4.35.0-rc2**.
It is intended for submission to the **Palomar registry**.

The Palomar submission contains **52 theorems** in `Challenge.lean`, with matching
proofs in `Solution.lean`. These include De Wilde's closed graph and open mapping
theorems as the two results on webbed spaces. The submission metadata and compared
declarations are recorded in `formalization.yaml` and `comparator.json`.

The release also generalizes supporting graph, linear-relation and completion
results and improves declaration and module documentation, including explicit
real-convexity and Fréchet-space conventions.

The fresh local Comparator run passed for all 52 submitted theorems, with con-ron,
NanoDa and Lean's kernel accepting the solution. The library and solution contain
no `sorry` placeholders or project-specific axioms; the deliberate `sorry` holes
in the Challenge file are part of the submission format.

**Build:** `lake exe cache get && lake build`
