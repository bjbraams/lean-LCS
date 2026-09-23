/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Projection
public import WebbedSpaces.DeWilde.OpenMapping
public import WebbedSpaces.Product

/-!
# Algebraic complements that are topological complements

Let `E` be a Hausdorff ultrabornological space that is the algebraic direct sum of two subspaces
`H₁` and `H₂`. If both subspaces are webbed for the induced topology, then the projections onto
them are continuous, so that they are closed and topologically complementary
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5.(4)). If `E` itself is webbed, it
suffices that `H₁` and `H₂` are sequentially closed (§35.5.(5) a)).

The proof applies De Wilde's open mapping theorem to the continuous linear bijection
`(a, b) ↦ a + b` from the webbed space `H₁ × H₂` onto `E`.

## Main statements

* `Submodule.continuous_prodEquivOfIsCompl_symm_of_webbedSpace`
* `Submodule.continuous_projectionOnto_of_webbedSpace`
* `Submodule.continuous_projectionOnto_of_isSeqClosed`
* `Submodule.isClosed_of_isCompl_of_isSeqClosed`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5

## Tags

complemented subspace, open mapping theorem, De Wilde, webbed space
-/

public section

open Set Filter Function

open scoped Topology

universe u v

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type u} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [UltrabornologicalSpace 𝕜 E] [T2Space E]
  {H₁ H₂ : Submodule 𝕜 E}

namespace Submodule

/-- Let a Hausdorff ultrabornological space be the algebraic direct sum of two subspaces that
are webbed for the induced topology. Then the decomposition `x ↦ (x₁, x₂)` is continuous,
Köthe II §35.5.(4). -/
theorem continuous_prodEquivOfIsCompl_symm_of_webbedSpace [WebbedSpace H₁] [WebbedSpace H₂]
    (h : IsCompl H₁ H₂) : Continuous (H₁.prodEquivOfIsCompl H₂ h).symm := by
  have hlc (H : Submodule 𝕜 E) : LocallyConvexSpace ℝ H :=
    Topology.IsInducing.locallyConvexSpace (f := H.subtype.restrictScalars ℝ) .subtypeVal
  have := hlc H₁
  have := hlc H₂
  let e := H₁.prodEquivOfIsCompl H₂ h
  -- The map `(a, b) ↦ a + b` is a continuous linear bijection from a webbed space onto `E`.
  have hcont : Continuous e := by
    have he : (e : H₁ × H₂ → E) = fun x ↦ (x.1 : E) + (x.2 : E) :=
      funext fun x ↦ coe_prodEquivOfIsCompl' H₁ H₂ h x
    rw [he]
    fun_prop
  have hopen : IsOpenMap e :=
    (⟨e.toLinearMap, hcont⟩ : (H₁ × H₂) →L[𝕜] E).isOpenMap_of_webbedSpace_of_ultrabornologicalSpace
      e.surjective
  refine continuous_def.mpr fun U hU ↦ ?_
  rw [← LinearEquiv.image_eq_preimage_symm]
  exact hopen U hU

/-- Let a Hausdorff ultrabornological space be the algebraic direct sum of two subspaces that
are webbed for the induced topology. Then the projection onto the first subspace along the
second one is continuous, Köthe II §35.5.(4). -/
theorem continuous_projectionOnto_of_webbedSpace [WebbedSpace H₁] [WebbedSpace H₂]
    (h : IsCompl H₁ H₂) : Continuous (H₁.projectionOnto H₂ h) := by
  have hc := continuous_fst.comp (continuous_prodEquivOfIsCompl_symm_of_webbedSpace h)
  refine hc.congr fun x ↦ ?_
  rw [Function.comp_apply, prodEquivOfIsCompl_symm_apply]

/-- Let a Hausdorff space that is webbed and ultrabornological be the algebraic direct sum of two
sequentially closed subspaces. Then the projection onto the first subspace along the second one
is continuous, Köthe II §35.5.(5) a). -/
theorem continuous_projectionOnto_of_isSeqClosed [WebbedSpace E] (h : IsCompl H₁ H₂)
    (h₁ : IsSeqClosed (H₁ : Set E)) (h₂ : IsSeqClosed (H₂ : Set E)) :
    Continuous (H₁.projectionOnto H₂ h) := by
  have := WebbedSpace.of_isSeqClosed H₁ h₁
  have := WebbedSpace.of_isSeqClosed H₂ h₂
  exact continuous_projectionOnto_of_webbedSpace h

/-- Let a Hausdorff space that is webbed and ultrabornological be the algebraic direct sum of two
sequentially closed subspaces. Then the subspaces are closed, Köthe II §35.5.(5) a). -/
theorem isClosed_of_isCompl_of_isSeqClosed [WebbedSpace E] (h : IsCompl H₁ H₂)
    (h₁ : IsSeqClosed (H₁ : Set E)) (h₂ : IsSeqClosed (H₂ : Set E)) :
    IsClosed (H₂ : Set E) := by
  have hc := continuous_projectionOnto_of_isSeqClosed h h₁ h₂
  have hker : (H₂ : Set E) = H₁.projectionOnto H₂ h ⁻¹' {0} := by
    ext x
    rw [mem_preimage, mem_singleton_iff, projectionOnto_apply_eq_zero_iff, SetLike.mem_coe]
  rw [hker]
  exact isClosed_singleton.preimage hc

end Submodule
