/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Combination

/-!
# Finite convex combinations with bounded total weight

`Convex.sum_smul_mem_smul` bounds a finite positive combination by a scalar multiple of a
convex set. `Convex.sum_smul_mem` handles nonnegative weights of sum at most one when zero
belongs to the set. Scalars lie in an arbitrary linearly ordered field.
-/

public section

open Set

open scoped Pointwise

variable {R F : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup F] [Module R F] {K : Set F} {ι : Type*}

/-- A sum `∑ c i • x i` of points of a convex set with nonnegative coefficients lies in
`(∑ c i) • K`, if the sum of the coefficients is positive. -/
theorem Convex.sum_smul_mem_smul (hK : Convex R K) {t : Finset ι} {c : ι → R} {x : ι → F}
    (hc : ∀ i ∈ t, 0 ≤ c i) (hpos : 0 < ∑ i ∈ t, c i) (hx : ∀ i ∈ t, x i ∈ K) :
    ∑ i ∈ t, c i • x i ∈ (∑ i ∈ t, c i) • K := by
  refine ⟨∑ i ∈ t, (c i / ∑ j ∈ t, c j) • x i, hK.sum_mem
    (fun i hi ↦ div_nonneg (hc i hi) hpos.le) ?_ hx, ?_⟩
  · simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, mul_inv_cancel₀ hpos.ne']
  · simp only [Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_div_cancel₀ _ hpos.ne']

/-- A sum `∑ c i • x i` of points of a convex set that contains zero, with nonnegative
coefficients of sum at most one, lies in the set. -/
theorem Convex.sum_smul_mem (hK : Convex R K) (h0 : (0 : F) ∈ K) {t : Finset ι} {c : ι → R}
    {x : ι → F} (hc : ∀ i ∈ t, 0 ≤ c i) (hle : ∑ i ∈ t, c i ≤ 1) (hx : ∀ i ∈ t, x i ∈ K) :
    ∑ i ∈ t, c i • x i ∈ K := by
  rcases (Finset.sum_nonneg hc).eq_or_lt with h | h
  · have hzero : ∀ i ∈ t, c i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hc).mp h.symm
    rw [Finset.sum_eq_zero fun i hi ↦ by rw [hzero i hi, zero_smul]]
    exact h0
  · obtain ⟨y, hy, hyx⟩ := hK.sum_smul_mem_smul hc h hx
    rw [← hyx]
    exact hK.smul_mem_of_zero_mem h0 hy ⟨h.le, hle⟩
