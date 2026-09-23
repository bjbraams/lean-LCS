/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Seminorm bounds for finite sums and convergent sequences

`Seminorm.sum_smul_le_of_le` estimates arbitrary finite linear combinations using bounds
only on the selected terms. Continuous seminorms are bounded on null sequences. The
sequence-specialized wrappers and the ℓ¹ bound support the Fréchet-space application; the
ℓ¹ estimate is a direct specialization of Mathlib's `lp.sum_rpow_le_norm_rpow`.
-/

public section

open Set Filter

open scoped Topology lp

/-- A finite sum of scalar multiples is bounded by the sum of coefficient norms times a common
seminorm bound on the terms occurring in the sum. -/
theorem Seminorm.sum_smul_le_of_le {𝕜 E ι : Type*} [SeminormedRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] (p : Seminorm 𝕜 E) (t : Finset ι) (a : ι → 𝕜) (x : ι → E) {C : ℝ}
    (hC : ∀ n ∈ t, p (x n) ≤ C) : p (∑ n ∈ t, a n • x n) ≤ C * ∑ n ∈ t, ‖a n‖ := by
  refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) t
    fun n ↦ a n • x n).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn ↦ ?_
  rw [map_smul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC n hn) (norm_nonneg _)

section Estimates

variable {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- If `p (x n) ≤ C` for all `n` then `p (∑ n ∈ t, a n • x n) ≤ C * ∑ n ∈ t, ‖a n‖`. -/
theorem Seminorm.sum_smul_le (p : Seminorm 𝕜 E) (t : Finset ℕ) (a : ℕ → 𝕜) (x : ℕ → E) {C : ℝ}
    (hC : ∀ n, p (x n) ≤ C) : p (∑ n ∈ t, a n • x n) ≤ C * ∑ n ∈ t, ‖a n‖ :=
  p.sum_smul_le_of_le t a x fun n _ ↦ hC n

/-- A continuous seminorm is bounded on a sequence that tends to zero. -/
theorem Seminorm.exists_forall_le_of_tendsto_zero [TopologicalSpace E] {p : Seminorm 𝕜 E}
    (hp : Continuous p) {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, p (x n) ≤ C := by
  have h : Tendsto (fun n ↦ p (x n)) atTop (𝓝 (p 0)) := (hp.tendsto 0).comp hx
  obtain ⟨C, hC⟩ := h.bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun n ↦ (hC (mem_range_self n)).trans (le_max_left _ _)⟩

end Estimates

section Lp

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

/-- The norm of an element of `ℓ¹` dominates every finite partial sum of its coordinates. -/
theorem lp.sum_norm_le_norm_one (a : lp E 1) (t : Finset ι) : ∑ n ∈ t, ‖a n‖ ≤ ‖a‖ := by
  simpa using lp.sum_rpow_le_norm_rpow (p := 1) (by norm_num) a t

end Lp
