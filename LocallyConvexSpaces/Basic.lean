/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TopologicalVectorSpaces.Basic

/-!
# Convex balanced neighbourhoods of zero

In Mathlib a real or complex locally convex space `E` is described by
`[Module ℝ E] [LocallyConvexSpace ℝ E]` together with a compatible `𝕜`-module structure; see for
instance `Mathlib/Analysis/LocallyConvex/Separation.lean`. The class `LocallyConvexSpace ℝ E`
provides convex neighbourhoods of zero, whereas arguments with seminorms and barrels need
neighbourhoods that are convex over `ℝ` and balanced over `𝕜`. This file provides them.

## Main statements

* `LocallyConvexSpace.of_real`, `PolynormableSpace.of_locallyConvexSpace_real`: a real or complex
  topological vector space that is locally convex over `ℝ` is locally convex over `𝕜` for the
  order `ComplexOrder`, and is polynormable over `𝕜`. This links the convention of this library
  (`LocallyConvexSpace ℝ E`) to statements of Mathlib about `PolynormableSpace 𝕜 E`.
* `nhds_zero_hasBasis_convex_balanced`: in a locally convex space the neighbourhoods of zero
  that are convex over `ℝ` and balanced over `𝕜` form a basis of neighbourhoods of zero.

* `SeparatingDual.of_locallyConvexSpace_real`: continuous functionals separate points in a
  Hausdorff real or complex locally convex space.

## Implementation notes

`Mathlib/Analysis/LocallyConvex/AbsConvex.lean` has `nhds_hasBasis_absConvex`, which concerns
`AbsConvex 𝕜` under the hypothesis `LocallyConvexSpace 𝕜 E`; for `𝕜 = ℂ` that refers to the
order on `ℂ`. The statement here keeps convexity over `ℝ`, as in `gaugeSeminorm`.

## Tags

locally convex, balanced core, absolutely convex
-/

public section

open Set Filter

open scoped Topology Pointwise

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [SMulCommClass ℝ 𝕜 E]

variable (𝕜 E) in
/-- In a locally convex space the neighbourhoods of zero that are convex over `ℝ` and balanced
over `𝕜` form a basis of neighbourhoods of zero. -/
theorem nhds_zero_hasBasis_convex_balanced [TopologicalSpace E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E ↦ s ∈ 𝓝 (0 : E) ∧ Convex ℝ s ∧ Balanced 𝕜 s) id := by
  refine (LocallyConvexSpace.convex_basis_zero ℝ E).to_hasBasis (fun s hs ↦ ?_)
    fun s hs ↦ ⟨s, ⟨hs.1, hs.2.1⟩, Subset.rfl⟩
  exact ⟨balancedCore 𝕜 s,
    ⟨balancedCore_mem_nhds_zero hs.1, hs.2.balancedCore (mem_of_mem_nhds hs.1),
      balancedCore_balanced s⟩,
    balancedCore_subset s⟩

section RCLike

variable (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E]

open scoped ComplexOrder in
/-- A real or complex vector space that is locally convex over `ℝ` is locally convex over `𝕜`,
for the partial order `ComplexOrder` on `𝕜`. -/
theorem LocallyConvexSpace.of_real : LocallyConvexSpace 𝕜 E :=
  LocallyConvexSpace.ofBasisZero 𝕜 E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    fun _ hs ↦ convex_RCLike_iff_convex_real.mpr hs.2

/-- A real or complex topological vector space that is locally convex over `ℝ` is polynormable
over `𝕜`: its topology is defined by the continuous `𝕜`-seminorms. -/
theorem PolynormableSpace.of_locallyConvexSpace_real [ContinuousSMul 𝕜 E] :
    PolynormableSpace 𝕜 E := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have := LocallyConvexSpace.of_real 𝕜 E
  exact LocallyConvexSpace.toPolynormableSpace

/-- The continuous dual of a Hausdorff real or complex locally convex space separates points. -/
theorem SeparatingDual.of_locallyConvexSpace_real [ContinuousSMul 𝕜 E] [T1Space E] :
    SeparatingDual 𝕜 E := by
  constructor
  intro x hx
  obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
  exact ⟨f, fun h ↦ by simp [h] at hf⟩

end RCLike
