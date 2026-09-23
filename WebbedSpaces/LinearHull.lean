/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.BanachDisk
public import WebbedSpaces.Hereditary

/-!
# The linear hull of a set of a strict web is strictly webbed

Let `C` be a strict web on a topological vector space `E` and let `l₀` be a nonempty finite
sequence of indices with `C l₀` nonempty. Then the linear hull `L` of `C l₀`, with the topology
induced by `E`, is strictly webbed ([G. Köthe, *Topological Vector Spaces II*][kothe1979],
§35.4.(10)). The web on `L` has the sets `(m + 1) • C (l ++ l₀)`: the first index `m` selects a
multiple and the remaining indices continue the strand of `C` that starts with `l₀`.

## Main statements

* `IsStrictWeb.strictlyWebbedSpace_span`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(10)

## Tags

web, strictly webbed space, linear hull
-/

public section

open Set Filter PiNat

open scoped Topology Pointwise

/-- A strand that starts with the entries of `σ₀` below `p` and continues with `τ`. -/
private def concatStrand (σ₀ τ : ℕ → ℕ) (p : ℕ) : ℕ → ℕ :=
  fun i ↦ if i < p then σ₀ i else τ (i - p)

/-- The restrictions of a concatenated strand beyond the first `p` entries. -/
private theorem res_concatStrand (σ₀ τ : ℕ → ℕ) (p k : ℕ) :
    res (concatStrand σ₀ τ p) (p + k) = res τ k ++ res σ₀ p := by
  induction k with
  | zero =>
    rw [res_zero, List.nil_append, Nat.add_zero]
    exact res_eq_res.mpr fun i hi ↦ by simp [concatStrand, hi]
  | succ k ih =>
    have h : res (concatStrand σ₀ τ p) (p + (k + 1)) =
        concatStrand σ₀ τ p (p + k) :: res (concatStrand σ₀ τ p) (p + k) := rfl
    rw [h, ih, res_succ, List.cons_append]
    congr 1
    simp [concatStrand]

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- The web on the linear hull of `C l₀`: the first index `m` selects the multiple
`(m + 1) • C l₀` and the remaining indices `l` select `(m + 1) • C (l ++ l₀)`. -/
private def hullWebOf (C : List ℕ → Set E) (l₀ : List ℕ) (l : List ℕ) :
    Set ↥(Submodule.span 𝕜 (C l₀)) :=
  match l.reverse with
  | [] => univ
  | m :: l' => (↑) ⁻¹' (((m : ℝ) + 1) • C (l'.reverse ++ l₀))

omit [IsScalarTower ℝ 𝕜 E] in
/-- The sets of the web on the linear hull, for a nonempty list of indices. -/
private theorem hullWebOf_append_singleton (C : List ℕ → Set E) (l₀ l : List ℕ) (m : ℕ) :
    hullWebOf (𝕜 := 𝕜) C l₀ (l ++ [m]) = (↑) ⁻¹' (((m : ℝ) + 1) • C (l ++ l₀)) := by
  simp [hullWebOf]

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

omit [IsTopologicalAddGroup E] in
/-- **The linear hull of a set of a strict web is strictly webbed** for the induced topology,
Köthe II §35.4.(10). -/
theorem IsStrictWeb.strictlyWebbedSpace_span {C : List ℕ → Set E} (hC : IsStrictWeb 𝕜 C)
    {l₀ : List ℕ} (hl₀ : l₀ ≠ []) (hne : (C l₀).Nonempty) :
    StrictlyWebbedSpace 𝕜 ↥(Submodule.span 𝕜 (C l₀)) := by
  obtain ⟨e₀, he₀⟩ := hne
  have h0 (l : List ℕ) (hl : (C l).Nonempty) : (0 : E) ∈ C l := (hC.balanced l).zero_mem hl
  -- The sets `C (l ++ l₀)` lie in `C l₀`.
  have hsub (l : List ℕ) : C (l ++ l₀) ⊆ C l₀ := by
    induction l with
    | nil => exact Subset.rfl
    | cons n l ih => exact (hC.toIsWeb.cons_subset n (l ++ l₀)).trans ih
  have hpos (m : ℕ) : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine ⟨hullWebOf (𝕜 := 𝕜) C l₀, ?_⟩
  refine
    { nil := rfl
      iUnion_cons := fun l ↦ ?_
      convex := fun l ↦ ?_
      balanced := fun l ↦ ?_
      exists_radius := fun σ ↦ ?_ }
  · rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · -- Every point of the span lies in a multiple of `C l₀`.
      refine eq_univ_of_forall fun x ↦ ?_
      obtain ⟨r, hr, d, hd, hxd⟩ := DiskSpace.exists_smul_eq_of_mem_span 𝕜 (C l₀) x.2
      rw [diskHull_eq_self (hC.convex l₀) (hC.balanced l₀) ⟨e₀, he₀⟩] at hd
      obtain ⟨m, hm⟩ := exists_nat_ge r
      refine mem_iUnion.mpr ⟨m, ?_⟩
      have h := hullWebOf_append_singleton (𝕜 := 𝕜) C l₀ [] m
      rw [List.nil_append, List.nil_append] at h
      rw [h, mem_preimage, hxd]
      refine ⟨(r / ((m : ℝ) + 1)) • d, (hC.convex l₀).smul_mem_of_zero_mem
        (h0 l₀ ⟨e₀, he₀⟩) hd ⟨div_nonneg hr (hpos m).le, ?_⟩, ?_⟩
      · rw [div_le_one (hpos m)]
        linarith
      · change ((m : ℝ) + 1) • (r / ((m : ℝ) + 1)) • d = r • d
        rw [smul_smul, mul_div_cancel₀ _ (hpos m).ne']
    · simp only [List.concat_eq_append]
      have h (n : ℕ) : hullWebOf (𝕜 := 𝕜) C l₀ (n :: (L ++ [b])) =
          (↑) ⁻¹' (((b : ℝ) + 1) • C (n :: (L ++ l₀))) := by
        rw [← List.cons_append, hullWebOf_append_singleton, List.cons_append]
      simp_rw [h]
      rw [hullWebOf_append_singleton, ← preimage_iUnion, ← smul_set_iUnion,
        hC.toIsWeb.iUnion_cons]
  · rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact convex_univ
    · rw [List.concat_eq_append, hullWebOf_append_singleton]
      exact ((hC.convex _).smul _).is_linear_preimage
        ((Submodule.span 𝕜 (C l₀)).subtype.restrictScalars ℝ).isLinear
  · rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact balanced_univ
    · rw [List.concat_eq_append, hullWebOf_append_singleton]
      have hb : Balanced 𝕜 (((b : ℝ) + 1) • C (L ++ l₀)) := by
        rintro a ha _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨a • y, (hC.balanced _) a ha (smul_mem_smul_set hy), smul_comm _ a y⟩
      exact hb.preimage (Submodule.span 𝕜 (C l₀)).subtype
  · -- The strand of `C` that starts with `l₀` and continues with the tail of `σ`.
    obtain ⟨σ₀, hσ₀⟩ := exists_res_eq l₀
    set p := l₀.length with hp
    have hp1 : 1 ≤ p := List.length_pos_iff.mpr hl₀
    let τ : ℕ → ℕ := fun i ↦ σ (i + 1)
    let τ' := concatStrand σ₀ τ p
    have hτ' (k : ℕ) : res τ' (p + k) = res τ k ++ l₀ := by
      rw [res_concatStrand, hσ₀]
    obtain ⟨ρ, hρ, hstrict⟩ := hC.exists_radius τ'
    let m := σ 0
    have hD (k : ℕ) : hullWebOf (𝕜 := 𝕜) C l₀ (res σ (k + 1)) =
        (↑) ⁻¹' (((m : ℝ) + 1) • C (res τ k ++ l₀)) := by
      rw [res_succ_eq_res_append, hullWebOf_append_singleton]
    refine ⟨fun k ↦ ρ (p - 1 + k), fun k ↦ hρ _, fun x c hx hc k₀ ↦ ?_⟩
    -- Write `x k = (m + 1) • y k` with `y k` in the strand of `C`.
    have hy (k : ℕ) : ∃ y ∈ C (res τ' (p - 1 + k + 1)), ((m : ℝ) + 1) • y = (x k : E) := by
      have h := hx k
      rw [hD, mem_preimage] at h
      obtain ⟨y, hy, hyx⟩ := h
      refine ⟨y, ?_, hyx⟩
      rw [show p - 1 + k + 1 = p + k by omega, hτ']
      exact hy
    choose y hyC hyx using hy
    -- Sequences along the whole strand, with fillers from `C l₀` and zero coefficients below
    -- index `p - 1`.
    have hfill (i : ℕ) (hi : i < p - 1) : (C (res τ' (i + 1))).Nonempty := by
      have h1 : e₀ ∈ C (res τ' (p + 0)) := by
        rw [hτ', res_zero, List.nil_append]
        exact he₀
      exact ⟨e₀, hC.toIsWeb.res_antitone τ' (by omega) h1⟩
    obtain ⟨X, hX, hXy⟩ := Set.exists_seq_forall_mem_forall_add_eq
      (S := fun i ↦ C (res τ' (i + 1))) hfill hyC
    obtain ⟨c', hc', hc'c⟩ := Set.exists_seq_forall_mem_forall_add_eq
      (S := fun i ↦ Icc (0 : ℝ) (ρ i)) (k₀ := p - 1) (fun i _ ↦ ⟨0, le_rfl, (hρ i).le⟩)
      (Y := c) fun j ↦ hc j
    obtain ⟨s, hsC, hs⟩ := hstrict X c' hX (fun i ↦ mem_Icc.mp (hc' i)) (p - 1 + k₀)
    have hterm (j : ℕ) : c' (p - 1 + k₀ + j) • X (p - 1 + k₀ + j) = c (k₀ + j) • y (k₀ + j) := by
      rw [add_assoc, hXy, hc'c]
    have hsC' : s ∈ C (res τ k₀ ++ l₀) := by
      rw [show p - 1 + k₀ + 1 = p + k₀ by omega, hτ'] at hsC
      exact hsC
    -- The limit `(m + 1) • s` lies in the span.
    have hmem : ((m : ℝ) + 1) • s ∈ Submodule.span 𝕜 (C l₀) :=
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (hsub _ hsC'))
    refine ⟨⟨((m : ℝ) + 1) • s, hmem⟩, ?_, ?_⟩
    · rw [hD, mem_preimage]
      exact smul_mem_smul_set hsC'
    · rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
      refine (hs.const_smul ((m : ℝ) + 1)).congr fun N ↦ ?_
      rw [Function.comp_apply, Submodule.coe_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hterm, smul_comm, hyx, Submodule.coe_smul_of_tower]
