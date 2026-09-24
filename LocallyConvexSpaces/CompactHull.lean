/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.TotallyBounded
public import MathlibExtras.Analysis.ConvexCompact
public import MathlibExtras.Analysis.ConvexHull

/-!
# Compact `ℝ`-convex balanced hulls

In a quasi-complete locally convex space over `ℝ` or `ℂ` every compact set is contained in a compact
set that is `ℝ`-convex and balanced, namely the closure of the `ℝ`-convex hull of its balanced hull.

Mathlib provides the absolute-convex-hull API with scalar convexity. Here
`MathlibExtras.Analysis.ConvexHull` relates that API to real convexity, while balancedness remains
over `𝕜`. Compactness follows from Mathlib's quasi-completeness theorem for totally bounded sets.

## Main statements

* `IsCompact.exists_isCompact_convex_balanced_superset_of_quasiCompleteSpace`: the quasi-complete
  version.
* `IsCompact.exists_isCompact_convex_balanced_superset`: a compact subset of a complete locally
  convex space lies in a compact `ℝ`-convex balanced set that contains zero.

## Tags

compact, convex, balanced, absolutely convex hull
-/

public section

open Set Metric

open scoped Pointwise Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- In a quasi-complete locally convex space every compact set lies in a compact `ℝ`-convex
balanced set containing zero. -/
theorem IsCompact.exists_isCompact_convex_balanced_superset_of_quasiCompleteSpace
    [QuasiCompleteSpace 𝕜 E] {K : Set E} (hK : IsCompact K) :
    ∃ K' : Set E, K ⊆ K' ∧ IsCompact K' ∧ Convex ℝ K' ∧ Balanced 𝕜 K' ∧ (0 : E) ∈ K' := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  -- The balanced hull of `insert 0 K`, as the image of a compact set.
  let B : Set E := (fun p : 𝕜 × E ↦ p.1 • p.2) '' (closedBall (0 : 𝕜) 1 ×ˢ insert 0 K)
  have hBc : IsCompact B :=
    ((isCompact_closedBall (0 : 𝕜) 1).prod (hK.insert 0)).image (by fun_prop)
  have hBsub : insert 0 K ⊆ B := fun x hx ↦
    ⟨(1, x), ⟨by simp, hx⟩, one_smul 𝕜 x⟩
  have hBbal : Balanced 𝕜 B := by
    rintro a ha _ ⟨_, ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩, rfl⟩
    refine ⟨(a * c, x), ⟨?_, hx⟩, mul_smul a c x⟩
    rw [mem_closedBall_zero_iff] at hc ⊢
    rw [norm_mul]
    calc ‖a‖ * ‖c‖ ≤ 1 * 1 := mul_le_mul ha hc (norm_nonneg c) zero_le_one
      _ = 1 := one_mul 1
  have hHtb : TotallyBounded (convexHull ℝ B) := hBc.totallyBounded.convexHull
  refine ⟨closure (convexHull ℝ B), ?_,
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := 𝕜) hHtb,
    (convex_convexHull ℝ B).closure, hBbal.convexHull_real.closure, ?_⟩
  · exact ((subset_insert 0 K).trans hBsub).trans ((subset_convexHull ℝ B).trans subset_closure)
  · exact subset_closure (subset_convexHull ℝ B (hBsub (mem_insert 0 K)))

/-- In a complete locally convex space every compact set lies in a compact `ℝ`-convex balanced set
containing zero. -/
theorem IsCompact.exists_isCompact_convex_balanced_superset [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) :
    ∃ K' : Set E, K ⊆ K' ∧ IsCompact K' ∧ Convex ℝ K' ∧ Balanced 𝕜 K' ∧ (0 : E) ∈ K' :=
  hK.exists_isCompact_convex_balanced_superset_of_quasiCompleteSpace
