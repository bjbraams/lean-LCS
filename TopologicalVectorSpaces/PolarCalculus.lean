/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import MathlibExtras.Analysis.Polar
public import TopologicalVectorSpaces.Basic

/-!
# Polar identities in topological vector spaces

The polar in the continuous dual is unchanged by closure, balanced hull, or real convex
hull. For a nonzero scalar `c`, the polar of `c • s` equals `c⁻¹ • polar 𝕜 s`.
Balancedness and convexity of polars are imported from `MathlibExtras.Analysis.Polar`.

## Main statements

* `StrongDual.polar_closure`, `StrongDual.polar_balancedHull`.
* `StrongDual.polar_convexHull`, `StrongDual.polar_smul`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §1.3
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §1.2, II §6.3
-/

public section

open Set Filter

open scoped Topology Pointwise

namespace StrongDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- The polar of the closure of a set is the polar of the set. Mathlib has this for normed
spaces as `NormedSpace.polar_closure`. -/
theorem polar_closure (s : Set E) : polar 𝕜 (closure s) = polar 𝕜 s := by
  refine Subset.antisymm (fun φ hφ x hx ↦ hφ x (subset_closure hx)) fun φ hφ ↦ ?_
  have hcl : IsClosed {x : E | ‖φ x‖ ≤ 1} := isClosed_le φ.continuous.norm continuous_const
  exact fun x hx ↦ closure_minimal (fun y hy ↦ hφ y hy) hcl hx

/-- The polar of the balanced hull of a set is the polar of the set. -/
theorem polar_balancedHull (s : Set E) : polar 𝕜 (balancedHull 𝕜 s) = polar 𝕜 s := by
  refine Subset.antisymm (fun φ hφ x hx ↦ hφ x (subset_balancedHull 𝕜 hx)) fun φ hφ x hx ↦ ?_
  obtain ⟨c, hc, y, hy, rfl⟩ := mem_balancedHull_iff.mp hx
  change ‖φ (c • y)‖ ≤ 1
  rw [map_smul, norm_smul]
  calc ‖c‖ * ‖φ y‖ ≤ 1 * 1 := mul_le_mul hc (hφ y hy) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The polar of `c • s` is `c⁻¹ • polar s`, for a nonzero scalar `c`. -/
theorem polar_smul {c : 𝕜} (hc : c ≠ 0)
    (s : Set E) : polar 𝕜 (c • s) = c⁻¹ • polar 𝕜 s := by
  ext φ
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc), inv_inv]
  constructor
  · intro hφ x hx
    have h := hφ (c • x) (smul_mem_smul_set hx)
    change ‖c • φ x‖ ≤ 1
    rwa [← map_smul]
  · rintro hφ _ ⟨x, hx, rfl⟩
    have h := hφ x hx
    change ‖c • φ x‖ ≤ 1 at h
    rwa [← map_smul] at h

end StrongDual

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- The polar of the real convex hull of a set is the polar of the set. -/
theorem StrongDual.polar_convexHull (s : Set E) :
    StrongDual.polar 𝕜 (convexHull ℝ s) = StrongDual.polar 𝕜 s := by
  refine Subset.antisymm (fun φ hφ x hx ↦ hφ x (subset_convexHull ℝ s hx)) fun φ hφ ↦ ?_
  have hconv : Convex ℝ {x : E | ‖φ x‖ ≤ 1} := by
    have h : {x : E | ‖φ x‖ ≤ 1} = φ ⁻¹' Metric.closedBall (0 : 𝕜) 1 := by
      ext x
      simp
    rw [h]
    exact (convex_closedBall (0 : 𝕜) 1).is_linear_preimage
      (φ.toLinearMap.restrictScalars ℝ).isLinear
  exact fun x hx ↦ convexHull_min (fun y hy ↦ hφ y hy) hconv hx

end RCLike
