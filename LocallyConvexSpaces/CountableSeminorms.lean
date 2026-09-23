/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Basic
public import TopologicalVectorSpaces.CountableSeminorms
public import TopologicalVectorSpaces.Gauge

/-!
# First-countable locally convex spaces are countably seminormed

Mathlib shows that a topology defined by a countable family of seminorms is first countable
(`WithSeminorms.firstCountableTopology`). This file proves the converse for locally convex
spaces over `ℝ` or `ℂ`, using the more general result for polynormable spaces from
`TopologicalVectorSpaces.CountableSeminorms`. A sequence of continuous seminorm balls is chosen
inside a countable
zero-neighbourhood basis using Mathlib's `PolynormableSpace.hasBasis_zero_ball`. Together with
Mathlib's metrizability of first-countable uniform groups this gives the
usual equivalence between first-countable and countably seminormed locally convex spaces.
Such spaces are pseudometrizable, and metrizable if they are Hausdorff.

## Main statements

* `gaugeSeminorm_ball_mem_nhds` (imported from `TopologicalVectorSpaces.Gauge`): balls of the gauge
  seminorm of a convex balanced neighbourhood
  of zero are neighbourhoods of zero.
* `exists_continuous_seminorm_ball_subset`: every neighbourhood of zero contains the open unit
  ball of a continuous seminorm.
* `PolynormableSpace.exists_seminormFamily_nat_withSeminorms`: the imported polynormable core.
* `exists_seminormFamily_nat_withSeminorms`: a first-countable locally convex space has a
  sequence of seminorms that defines its topology.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], I §6.1, II §4
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §18.2

## Tags

metrizable, first countable, seminorm, Fréchet space
-/

public section

open Set Filter

open scoped Topology Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

omit [ContinuousSMul ℝ E] in
/-- In a locally convex space every neighbourhood of zero contains the open unit ball of a
continuous seminorm. -/
theorem exists_continuous_seminorm_ball_subset [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    {e : Set E} (he : e ∈ 𝓝 (0 : E)) :
    ∃ p : Seminorm 𝕜 E, Continuous p ∧ p.ball 0 1 ⊆ e := by
  have : PolynormableSpace 𝕜 E := PolynormableSpace.of_locallyConvexSpace_real 𝕜 E
  exact PolynormableSpace.exists_continuous_seminorm_ball_subset he

variable (𝕜 E) in
omit [ContinuousSMul ℝ E] in
/-- A first-countable locally convex space over `ℝ` or `ℂ` has a sequence of seminorms that
defines its topology. -/
theorem exists_seminormFamily_nat_withSeminorms [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    [FirstCountableTopology E] : ∃ p : SeminormFamily 𝕜 E ℕ, WithSeminorms p := by
  have : PolynormableSpace 𝕜 E := PolynormableSpace.of_locallyConvexSpace_real 𝕜 E
  exact PolynormableSpace.exists_seminormFamily_nat_withSeminorms 𝕜 E
