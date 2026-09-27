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
# Seminorm bounds for finite sums, convergent sequences and bounded families

## Main statements

* `Seminorm.sum_smul_le_of_le`: `p (∑ n ∈ t, a n • x n) ≤ C * ∑ n ∈ t, ‖a n‖` when
  `p (x n) ≤ C` for the terms that occur.
* `Seminorm.exists_forall_le_of_tendsto_zero`: a continuous seminorm is bounded on a null
  sequence.
* `Seminorm.exists_forall_le_of_isVonNBounded`: a continuous seminorm is bounded on a family with
  von Neumann bounded range.
* `lp.sum_norm_le_norm_one`: the norm of an element of `ℓ¹` dominates every finite sum of the
  norms of its coordinates; a specialization of Mathlib's `lp.sum_rpow_le_norm_rpow`.
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

/-- A continuous seminorm is bounded on a sequence that tends to zero. -/
theorem Seminorm.exists_forall_le_of_tendsto_zero [TopologicalSpace E] {p : Seminorm 𝕜 E}
    (hp : Continuous p) {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, p (x n) ≤ C := by
  have h : Tendsto (fun n ↦ p (x n)) atTop (𝓝 (p 0)) := (hp.tendsto 0).comp hx
  obtain ⟨C, hC⟩ := h.bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun n ↦ (hC (mem_range_self n)).trans (le_max_left _ _)⟩

end Estimates

/-- A continuous seminorm is bounded on a family with von Neumann bounded range. -/
theorem Seminorm.exists_forall_le_of_isVonNBounded {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {p : Seminorm 𝕜 E} (hp : Continuous p)
    {x : ι → E} (hx : Bornology.IsVonNBounded 𝕜 (range x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, p (x i) ≤ C := by
  obtain ⟨r, -, h⟩ := (hx (p.ball_mem_nhds hp one_pos)).exists_pos
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
  refine ⟨‖c‖, norm_nonneg _, fun i ↦ ?_⟩
  obtain ⟨y, hy, hyx⟩ := h c hc.le (mem_range_self i)
  rw [← hyx, map_smul_eq_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (p.mem_ball_zero.mp hy).le

section Lp

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

/-- The norm of an element of `ℓ¹` dominates every finite sum of the norms of its coordinates. -/
theorem lp.sum_norm_le_norm_one (a : lp E 1) (t : Finset ι) : ∑ n ∈ t, ‖a n‖ ≤ ‖a‖ := by
  simpa using lp.sum_rpow_le_norm_rpow (p := 1) (by norm_num) a t

end Lp
