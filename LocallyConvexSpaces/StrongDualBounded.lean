/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.PolarCalculus
public import LocallyConvexSpaces.PolarTopology

/-!
# Bounded subsets of the strong dual

The polar of a bornivorous subset of a topological vector space, in particular the polar of a
neighbourhood of zero, is bounded in the strong dual. Polars are closed in the strong dual.

## Main statements

* `StrongDual.isVonNBounded_polar_of_isBornivorous`
* `StrongDual.isVonNBounded_polar_of_mem_nhds`
* `StrongDual.isClosed_polar`

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.2

## Tags

strong dual, bounded set, polar, bornivorous
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- The polar of a bornivorous set is von Neumann bounded in the strong dual. -/
theorem StrongDual.isVonNBounded_polar_of_isBornivorous {U : Set E} (hU : IsBornivorous 𝕜 U) :
    IsVonNBounded 𝕜 (StrongDual.polar 𝕜 U) := by
  rw [StrongDual.hasBasis_nhds_zero_polar.isVonNBounded_iff]
  intro B hB
  -- `U` absorbs the bounded set `B`, so the polar of `B` absorbs the polar of `U`.
  obtain ⟨R, hR⟩ := absorbs_iff_norm.mp (hU B hB)
  refine absorbs_iff_norm.mpr ⟨max R 1, fun a ha ↦ ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    linarith [le_max_right R 1]
  have hBU : a⁻¹ • B ⊆ U := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨u, hu, hub⟩ := hR a ((le_max_left R 1).trans ha) hb
    have hub' : a • u = b := hub
    change a⁻¹ • b ∈ U
    rw [← hub', inv_smul_smul₀ ha0]
    exact hu
  have h : StrongDual.polar 𝕜 U ⊆ StrongDual.polar 𝕜 (a⁻¹ • B) :=
    LinearMap.polar_antitone _ hBU
  rwa [StrongDual.polar_smul (inv_ne_zero ha0), inv_inv] at h

/-- The polar of a neighbourhood of zero is von Neumann bounded in the strong dual. -/
theorem StrongDual.isVonNBounded_polar_of_mem_nhds {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsVonNBounded 𝕜 (StrongDual.polar 𝕜 U) :=
  StrongDual.isVonNBounded_polar_of_isBornivorous (isBornivorous_of_mem_nhds hU)

/-- The polar of a set is closed in the strong dual. -/
theorem StrongDual.isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) := by
  have h : StrongDual.polar 𝕜 s = ⋂ z ∈ s, {φ : StrongDual 𝕜 E | ‖φ z‖ ≤ 1} := by
    ext φ
    simp [StrongDual.mem_polar_iff]
  rw [h]
  exact isClosed_biInter fun z _ ↦
    isClosed_le (continuous_norm.comp (continuous_eval_const z))
      continuous_const
