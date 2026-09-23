/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import MathlibExtras.Topology.Sequences

/-!
# Non-meagre strands in a tree of sets

Finite restrictions of sequences use `PiNat.res`, with the newest entry at the head.

## Main statements

* `exists_forall_not_isMeagre_res`: a tree of sets with countably many successors at each vertex
  and a non-meagre root has a strand of non-meagre sets.
-/

public section

open Set PiNat

/-- Let `T` be a family of sets indexed by finite sequences of natural numbers, with `T l`
contained in the union of the `T (n :: l)`. If `T []` is not meagre then there is a strand `σ`
such that no `T (res σ k)` is meagre. -/
theorem exists_forall_not_isMeagre_res {E : Type*} [TopologicalSpace E] {T : List ℕ → Set E}
    (h0 : ¬IsMeagre (T [])) (hT : ∀ l, T l ⊆ ⋃ n, T (n :: l)) :
    ∃ σ : ℕ → ℕ, ∀ k, ¬IsMeagre (T (res σ k)) := by
  have step (l : List ℕ) (hl : ¬IsMeagre (T l)) : ∃ n, ¬IsMeagre (T (n :: l)) := by
    by_contra hcon
    push Not at hcon
    exact hl ((isMeagre_iUnion hcon).mono (hT l))
  let L : ∀ k : ℕ, {l : List ℕ // ¬IsMeagre (T l)} := fun k ↦
    Nat.rec (motive := fun _ ↦ {l : List ℕ // ¬IsMeagre (T l)}) ⟨[], h0⟩
      (fun _ l ↦ ⟨Classical.choose (step l.1 l.2) :: l.1,
        Classical.choose_spec (step l.1 l.2)⟩) k
  let σ : ℕ → ℕ := fun k ↦ Classical.choose (step (L k).1 (L k).2)
  have hL (k : ℕ) : (L (k + 1)).1 = σ k :: (L k).1 := rfl
  have hres (k : ℕ) : res σ k = (L k).1 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [res_succ, ih, hL]
  exact ⟨σ, fun k ↦ (hres k) ▸ (L k).2⟩
