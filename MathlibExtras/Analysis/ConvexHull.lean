/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Real and scalar convex hulls

No ambient topology is needed.

## Main statements

* `convexHull_RCLike_eq_real`: convex hulls over an `RCLike` field and over the reals agree for
  a compatible real module structure.
* `Balanced.convexHull_real`: the real convex hull of a balanced set is balanced.
-/

public section

open Set

open scoped Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

open scoped ComplexOrder in
/-- Convex hulls over an RCLike field and over the reals agree for the compatible real module. -/
theorem convexHull_RCLike_eq_real (s : Set E) : convexHull 𝕜 s = convexHull ℝ s := by
  apply Subset.antisymm
  · exact convexHull_min (subset_convexHull ℝ s)
      (convex_RCLike_iff_convex_real.mpr (convex_convexHull ℝ s))
  · exact convexHull_min (subset_convexHull 𝕜 s)
      (convex_RCLike_iff_convex_real.mp (convex_convexHull 𝕜 s))

open scoped ComplexOrder in
/-- The real convex hull of a `𝕜`-balanced set is `𝕜`-balanced. -/
theorem Balanced.convexHull_real {s : Set E} (hs : Balanced 𝕜 s) :
    Balanced 𝕜 (convexHull ℝ s) := by
  rw [← convexHull_RCLike_eq_real (𝕜 := 𝕜)]
  exact hs.convexHull
