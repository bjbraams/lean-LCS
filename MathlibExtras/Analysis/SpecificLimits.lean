/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A bound for geometric partial sums

## Main statements

* `sum_half_pow_succ_le_one`: the partial sums of `∑ (1 / 2) ^ (k + 1)` are at most one. The
  bound is used to choose radii in web constructions.
-/

public section

/-- The partial sums of the series `∑ (1 / 2) ^ (k + 1)` are at most one. These numbers bound
the radii of the series associated with a strand of a web. -/
theorem sum_half_pow_succ_le_one (n : ℕ) : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
  have h := sum_geometric_two_le n
  have h2 : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) =
      (1 / 2) * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [pow_succ]; ring
  rw [h2]
  linarith
