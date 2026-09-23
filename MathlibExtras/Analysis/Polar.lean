/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Basic

/-!
# Balanced and convex polars of linear pairings

Neither result requires a topology on the paired modules.

## Main statements

* `LinearMap.balanced_polar`: polars are balanced, over a normed commutative ring.
* `LinearMap.convex_polar`: polars are convex over the reals, for real or complex pairings.
-/

public section

open Set

/-- Polars are balanced. -/
theorem LinearMap.balanced_polar {𝕜 E F : Type*} [NormedCommRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) : Balanced 𝕜 (B.polar s) := by
  refine balanced_iff_smul_mem.mpr fun a ha y hy x hx ↦ ?_
  rw [map_smul, smul_eq_mul]
  apply (norm_mul_le _ _).trans
  calc ‖a‖ * ‖B x y‖ ≤ 1 * 1 := mul_le_mul ha (hy x hx) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

section Polar

variable {𝕜 E F : Type*} [RCLike 𝕜]

namespace LinearMap

section Polar

variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E)

/-- Polars are convex. -/
theorem convex_polar [Module ℝ F] [IsScalarTower ℝ 𝕜 F] : Convex ℝ (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact convex_iInter₂ fun x _ ↦
    (convex_closedBall (0 : 𝕜) 1).is_linear_preimage ((B x).restrictScalars ℝ).isLinear

end Polar

end LinearMap

end Polar
