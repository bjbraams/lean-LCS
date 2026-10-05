# Credits

This file records material in lean-LCS that is imported from, copied from, adapted from, or
related to work outside the pinned Mathlib. Each such declaration also carries a note at its point
of use in the Lean source; those notes are authoritative for the details.

## Tau Ceti

[Tau Ceti](https://github.com/TauCetiProject/TauCeti) is a dependency of this project, pinned at
commit `a780c7ad6beb23f60a17351a492d177878020ad5` in [lakefile.toml](lakefile.toml). All Tau Ceti
results listed below are by the Tau Ceti contributors and are imported directly; no local copies
are retained.

| Tau Ceti module | Declarations used | Used in |
| --- | --- | --- |
| `TauCeti.Topology.Algebra.Group.FirstCountable` | `SeparatelyContinuousMul.toFirstCountableTopology`, `SeparatelyContinuousAdd.toFirstCountableTopology` (instances) | [TopologicalGroups/Basic](TopologicalGroups/Basic.lean), [WebbedSpaces/Baire](WebbedSpaces/Baire.lean) |
| `TauCeti.Topology.Algebra.Module.LocallyConvex` | `LocallyConvexSpace.toStronglyLocallyContractibleSpace` (instance, re-exported) | [LocallyConvexSpaces/Basic](LocallyConvexSpaces/Basic.lean) |
| `TauCeti.Topology.Algebra.ZeroSequenceOfUnits` | `TauCeti.HasZeroSequenceOfUnits` (class) | [MathlibExtras/Analysis/ZeroSequenceOfUnits](MathlibExtras/Analysis/ZeroSequenceOfUnits.lean), which registers nontrivially normed fields as instances |
| `TauCeti.Topology.Algebra.OpenMapping.Basic` | `TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero` (the Baire step of Henkel's open mapping theorem) | [TopologicalVectorSpaces/BaireMapping](TopologicalVectorSpaces/BaireMapping.lean) |

The following project statements overlap with Tau Ceti results but were obtained independently
and are retained, with a note at the declaration:

| Project declaration | Related Tau Ceti declaration |
| --- | --- |
| `exists_seq_mem_div_prod_mem_closure` ([TopologicalGroups/Series](TopologicalGroups/Series.lean)) | `TauCeti.exists_seq_mem_and_sub_sum_mem` (additive form for images under an additive map) |
| `ContinuousLinearMap.isClosed_graph` ([TopologicalVectorSpaces/Basic](TopologicalVectorSpaces/Basic.lean)) | `AddMonoidHomClass.isClosed_graph` (subgroup graph of a continuous additive homomorphism) |

Before contributing these results to Mathlib, their Tau Ceti prerequisites must be resolved.

## Open Mathlib pull requests

Some statements duplicate, adapt, or follow the proof organization of material in open Mathlib
pull requests. The notes beside the declarations say which, and when the local copy is to be
deleted.

| Pull request | Author | Files with notes |
| --- | --- | --- |
| #26339 (Banach–Dieudonné lemma, draft) | C. Hoskin | [KreinSmulian](LocallyConvexSpaces/KreinSmulian.lean) |
| #26345 (bipolar theorem) | C. Hoskin | [Bipolar](LocallyConvexSpaces/Bipolar.lean) |
| #34106 (quotient group seminorms, draft) | A. Dedecker | [QuotientSeminorm](TopologicalVectorSpaces/QuotientSeminorm.lean) |
| #40983 | K. H. Wilson | [NearlyOpen](TopologicalGroups/NearlyOpen.lean), [TopologicalVectorSpaces/Basic](TopologicalVectorSpaces/Basic.lean) |
| #41166 (generalized open mapping theorem, draft) | K. H. Wilson | [NearlyOpen](TopologicalGroups/NearlyOpen.lean), [OpenMapping](LocallyConvexSpaces/OpenMapping.lean), [ClosedGraph](LocallyConvexSpaces/ClosedGraph.lean), [BaireMapping](TopologicalVectorSpaces/BaireMapping.lean) |
| #43747 (dense submodules and annihilators) | yuanyi-350 | [Transpose](LocallyConvexSpaces/Transpose.lean) |
