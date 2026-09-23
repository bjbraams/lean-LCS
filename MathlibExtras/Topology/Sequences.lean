/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Finite restrictions and extensions of sequences

These results use no vector-space structure.

## Main statements

* `PiNat.res_succ_eq_res_append`, `PiNat.res_comp`, `PiNat.exists_res_eq`: finite restrictions
  of sequences, stored with the newest entry at the head.
* `Set.exists_seq_forall_mem_forall_add_eq`: a prescribed tail extends to a sequence of points
  in nonempty sets.
-/

public section

open Set PiNat

section Res

/-- The restriction of a strand to its indices `1, 2, …`. -/
theorem PiNat.res_succ_eq_res_append {α : Type*} (σ : ℕ → α) (k : ℕ) :
    res σ (k + 1) = res (fun i ↦ σ (i + 1)) k ++ [σ 0] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [res_succ, ih, res_succ, List.cons_append]

/-- The restriction of a strand composed with a map. -/
theorem PiNat.res_comp {α β : Type*} (g : α → β) (σ : ℕ → α) (k : ℕ) :
    res (fun i ↦ g (σ i)) k = (res σ k).map g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [res_succ, res_succ, List.map_cons, ih]

/-- Every finite sequence, stored with the newest entry at the head, is the restriction of an
infinite sequence. -/
theorem PiNat.exists_res_eq {α : Type*} [Inhabited α] (l : List α) :
    ∃ σ : ℕ → α, res σ l.length = l := by
  classical
  induction l with
  | nil => exact ⟨fun _ ↦ default, rfl⟩
  | cons a l ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨Function.update σ l.length a, ?_⟩
    rw [List.length_cons, res_succ, Function.update_self]
    congr 1
    exact (res_eq_res.mpr fun i hi ↦ Function.update_of_ne (Nat.ne_of_lt hi) _ _).trans hσ

/-- Completing a tail to a sequence: for sets `S k` that are nonempty for `k < k₀` and points
`Y j ∈ S (k₀ + j)` there is a sequence `X` with `X k ∈ S k` for all `k` and `X (k₀ + j) = Y j`.
This reduces a condition on the tails of sequences along a strand of a web to a condition on
whole sequences. -/
theorem Set.exists_seq_forall_mem_forall_add_eq {α : Type*} {S : ℕ → Set α} {k₀ : ℕ}
    (hne : ∀ k < k₀, (S k).Nonempty) {Y : ℕ → α} (hY : ∀ j, Y j ∈ S (k₀ + j)) :
    ∃ X : ℕ → α, (∀ k, X k ∈ S k) ∧ ∀ j, X (k₀ + j) = Y j := by
  refine ⟨fun k ↦ if h : k₀ ≤ k then Y (k - k₀) else (hne k (not_le.mp h)).some,
    fun k ↦ ?_, fun j ↦ ?_⟩
  · by_cases h : k₀ ≤ k
    · have h1 := hY (k - k₀)
      rw [Nat.add_sub_cancel' h] at h1
      simpa [h] using h1
    · simpa [h] using (hne k (not_le.mp h)).some_mem
  · simp

end Res
