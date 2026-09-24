/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Basic
public import Mathlib.Analysis.LocallyConvex.Bounded
public import TopologicalVectorSpaces.PolarCalculus

/-!
# Bounded `ℝ`-convex hulls

The real convex hull of a bounded set in a real or complex locally convex space is bounded.
Balanced hulls preserve boundedness (`Bornology.IsVonNBounded.balancedHull`), so `ℝ`-convex
balanced hulls of bounded sets are bounded as well. The polar identities for closures, hulls
and scalar multiples are in `TopologicalVectorSpaces.PolarCalculus`.

## Main statements

* `Bornology.IsVonNBounded.convexHull`: the `ℝ`-convex hull of a bounded set is bounded.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], I §5.1
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

section Bounded

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- In a locally convex space the `ℝ`-convex hull of a bounded set is bounded. -/
theorem Bornology.IsVonNBounded.convexHull [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hs : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (convexHull ℝ s) := by
  intro V hV
  obtain ⟨W, ⟨hW, hWc, -⟩, hWV⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hV
  refine Absorbs.mono_left ?_ hWV
  refine Filter.Eventually.mono (hs hW) fun c hc ↦ convexHull_min hc ?_
  rw [← image_smul]
  exact hWc.is_linear_image ⟨smul_add c, fun a x ↦ smul_comm c a x⟩

end Bounded
