/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.Quotient

/-!
# Quotients of bornological and ultrabornological spaces

For a locally convex space `E`, the quotient topology of `E ⧸ N` is the final locally convex
topology for the quotient map: it is locally convex and it is the finest topology for which the
quotient map is continuous. Since locally convex hulls of bornological and of ultrabornological
spaces are of the same kind, the quotients of these spaces are bornological, respectively
ultrabornological ([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7.(7), and Köthe I
§28.4.(2)).

## Main statements

* `Submodule.Quotient.eq_locallyConvexFinalTopology_mkQ`
* `Submodule.Quotient.instBornologicalSpace`, `Submodule.Quotient.instUltrabornologicalSpace`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7.(7)

## Tags

quotient, bornological space, ultrabornological space
-/

public section

open Set Filter

open scoped Topology

universe u v

namespace Submodule.Quotient

variable {𝕜 : Type v} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] (N : Submodule 𝕜 E)

/-- The quotient topology is the final locally convex topology for the quotient map. -/
theorem eq_locallyConvexFinalTopology_mkQ :
    (inferInstance : TopologicalSpace (E ⧸ N)) =
      locallyConvexFinalTopology fun _ : Unit ↦ N.mkQ := by
  let f := fun _ : Unit ↦ N.mkQ
  refine le_antisymm ?_ ((locallyConvexFinalTopology.le_iff f).mpr fun _ ↦ continuous_quot_mk)
  exact N.isQuotientMap_mkQ.eq_coinduced.le.trans
    (continuous_iff_coinduced_le.mp (locallyConvexFinalTopology.continuous_apply f ()))

/-- A quotient of a bornological locally convex space is bornological. -/
instance instBornologicalSpace [BornologicalSpace 𝕜 E] : BornologicalSpace 𝕜 (E ⧸ N) := by
  have h := locallyConvexFinalTopology.bornologicalSpace (𝕜 := 𝕜) fun _ : Unit ↦ N.mkQ
  rwa [← eq_locallyConvexFinalTopology_mkQ N] at h

/-- A quotient of an ultrabornological space is ultrabornological, Köthe II §35.7.(7). -/
instance instUltrabornologicalSpace [UltrabornologicalSpace 𝕜 E] :
    UltrabornologicalSpace 𝕜 (E ⧸ N) := by
  have h := locallyConvexFinalTopology.ultrabornologicalSpace (𝕜 := 𝕜) fun _ : Unit ↦ N.mkQ
  rwa [← eq_locallyConvexFinalTopology_mkQ N] at h

end Submodule.Quotient
