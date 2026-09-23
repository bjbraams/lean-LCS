/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TopologicalVectorSpaces.Quotient

/-!
# Quotient seminorms

`Seminorm.quotient p N` takes the infimum of `p` on each coset of `N`. Open balls are images
of the original seminorm balls, and a continuous seminorm induces a continuous quotient
seminorm. No local convexity or closedness of `N` is needed.
The quotient seminorm is the largest seminorm whose pullback is bounded by `p`.
This universal property gives monotonicity, descent of seminorms vanishing on `N`,
and bounds for the linear maps induced on the quotient.
-/

public section

open Set Filter

open scoped Topology NNReal

namespace Seminorm

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E)
  (N : Submodule 𝕜 E)

/-- The set of values of `p` on a coset is nonempty. -/
theorem quotient_fiber_nonempty (q : E ⧸ N) : (p '' {x | N.mkQ x = q}).Nonempty := by
  obtain ⟨x, hx⟩ := N.mkQ_surjective q
  exact ⟨p x, x, hx, rfl⟩

/-- The set of values of `p` on a coset is bounded below. -/
theorem quotient_fiber_bddBelow (q : E ⧸ N) : BddBelow (p '' {x | N.mkQ x = q}) :=
  ⟨0, by
    rintro _ ⟨x, -, rfl⟩
    exact apply_nonneg p x⟩

/-- The **quotient seminorm** on `E ⧸ N`: the infimum of `p` over a coset. -/
@[expose]
noncomputable def quotient : Seminorm 𝕜 (E ⧸ N) :=
  Seminorm.ofSMulLE (fun q ↦ sInf (p '' {x | N.mkQ x = q}))
    (le_antisymm (csInf_le (quotient_fiber_bddBelow p N 0) ⟨0, map_zero _, map_zero p⟩)
      (le_csInf (quotient_fiber_nonempty p N 0) (by
        rintro _ ⟨x, -, rfl⟩
        exact apply_nonneg p x)))
    (fun q₁ q₂ ↦ by
      refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := exists_lt_of_csInf_lt (quotient_fiber_nonempty p N q₁)
        (lt_add_of_pos_right _ (half_pos hε))
      obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ := exists_lt_of_csInf_lt (quotient_fiber_nonempty p N q₂)
        (lt_add_of_pos_right _ (half_pos hε))
      have hxy : N.mkQ (x + y) = q₁ + q₂ := by rw [map_add, hx, hy]
      calc sInf (p '' {z | N.mkQ z = q₁ + q₂}) ≤ p (x + y) :=
            csInf_le (quotient_fiber_bddBelow p N _) ⟨x + y, hxy, rfl⟩
        _ ≤ p x + p y := map_add_le_add p x y
        _ < _ := by linarith)
    (fun a q ↦ by
      have hle (x : E) (hx : N.mkQ x = q) : sInf (p '' {z | N.mkQ z = a • q}) ≤ ‖a‖ * p x := by
        have h1 : N.mkQ (a • x) = a • q := by rw [map_smul, hx]
        exact (csInf_le (quotient_fiber_bddBelow p N _) ⟨a • x, h1, rfl⟩).trans_eq
          (map_smul_eq_mul p a x)
      rcases eq_or_lt_of_le (norm_nonneg a) with h0 | hpos
      · obtain ⟨x, hx⟩ := N.mkQ_surjective q
        have := hle x hx
        rwa [← h0, zero_mul] at this ⊢
      · rw [← div_le_iff₀' hpos]
        refine le_csInf (quotient_fiber_nonempty p N q) ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [div_le_iff₀' hpos]
        exact hle x hx)

/-- The quotient seminorm of the class of `x` is at most `p x`. -/
theorem quotient_mk_le (x : E) : p.quotient N (N.mkQ x) ≤ p x :=
  csInf_le (quotient_fiber_bddBelow p N _) ⟨x, rfl, rfl⟩

/-- A seminorm on the quotient is bounded by the quotient seminorm exactly when its
pullback is bounded by the original seminorm. -/
theorem le_quotient_iff (q : Seminorm 𝕜 (E ⧸ N)) :
    q ≤ p.quotient N ↔ q.comp N.mkQ ≤ p := by
  constructor
  · intro h x
    exact (h (N.mkQ x)).trans (p.quotient_mk_le N x)
  · intro h z
    apply le_csInf (p.quotient_fiber_nonempty N z)
    rintro _ ⟨x, hx, rfl⟩
    change N.mkQ x = z at hx
    simpa only [Seminorm.comp_apply, hx] using h x

/-- Taking quotient seminorms preserves pointwise inequalities. -/
theorem quotient_mono {p q : Seminorm 𝕜 E} (h : p ≤ q) : p.quotient N ≤ q.quotient N :=
  (q.le_quotient_iff N _).mpr fun x ↦ (p.quotient_mk_le N x).trans (h x)

/-- Pulling a seminorm back from the quotient and then taking its quotient recovers it. -/
@[simp] theorem comp_mkQ_quotient (q : Seminorm 𝕜 (E ⧸ N)) :
    (q.comp N.mkQ).quotient N = q := by
  apply le_antisymm
  · intro z
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    exact (q.comp N.mkQ).quotient_mk_le N x
  · exact ((q.comp N.mkQ).le_quotient_iff N q).mpr le_rfl

/-- If a seminorm vanishes on the submodule, its quotient has the same value on every
representative. -/
theorem quotient_mk_eq (h : ∀ x ∈ N, p x = 0) (x : E) :
    p.quotient N (N.mkQ x) = p x := by
  apply le_antisymm (p.quotient_mk_le N x)
  apply le_csInf (p.quotient_fiber_nonempty N _)
  rintro _ ⟨y, hy, rfl⟩
  have hxy : x - y ∈ N := (Submodule.Quotient.eq N).mp hy.symm
  calc p x = p ((x - y) + y) := by rw [sub_add_cancel]
    _ ≤ p (x - y) + p y := map_add_le_add p _ _
    _ = p y := by rw [h _ hxy, zero_add]

/-- A seminorm vanishing on the submodule is the pullback of its quotient seminorm. -/
theorem quotient_comp_mkQ (h : ∀ x ∈ N, p x = 0) :
    (p.quotient N).comp N.mkQ = p := by
  ext x
  exact p.quotient_mk_eq N h x

/-- The linear map induced on a quotient satisfies a seminorm bound exactly when the
original linear map does. -/
theorem comp_liftQ_le_quotient_iff {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (hf : N ≤ LinearMap.ker f) :
    q.comp (N.liftQ f hf) ≤ p.quotient N ↔ q.comp f ≤ p := by
  rw [p.le_quotient_iff]
  rfl

/-- If the quotient seminorm of `q` is less than `r`, then `q` has a representative `x` with
`p x < r`. -/
theorem exists_lt_of_quotient_lt {q : E ⧸ N} {r : ℝ} (h : p.quotient N q < r) :
    ∃ x, N.mkQ x = q ∧ p x < r := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := exists_lt_of_csInf_lt (quotient_fiber_nonempty p N q) h
  exact ⟨x, hx, hx'⟩

/-- Taking quotient seminorms commutes with nonnegative scalar multiplication. -/
@[simp] theorem quotient_smul (C : ℝ≥0) : (C • p).quotient N = C • p.quotient N := by
  apply le_antisymm
  · intro z
    by_cases hC : C = 0
    · obtain ⟨x, rfl⟩ := N.mkQ_surjective z
      simpa [hC] using (C • p).quotient_mk_le N x
    have hCpos : 0 < (C : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)
    change (C • p).quotient N z ≤ C * p.quotient N z
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨x, hx, hpx⟩ := p.exists_lt_of_quotient_lt N
      (lt_add_of_pos_right (p.quotient N z) (div_pos hε hCpos))
    calc (C • p).quotient N z ≤ C * p x := hx ▸ (C • p).quotient_mk_le N x
      _ < C * (p.quotient N z + ε / C) := mul_lt_mul_of_pos_left hpx hCpos
      _ = C * p.quotient N z + ε := by rw [mul_add, mul_div_cancel₀ _ hCpos.ne']
  · apply ((C • p).le_quotient_iff N _).mpr
    intro x
    exact mul_le_mul_of_nonneg_left (p.quotient_mk_le N x) C.coe_nonneg

/-- The linear map induced on a quotient preserves any nonnegative seminorm bound. -/
theorem comp_liftQ_le_smul_quotient_iff {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (hf : N ≤ LinearMap.ker f) (C : ℝ≥0) :
    q.comp (N.liftQ f hf) ≤ C • p.quotient N ↔ q.comp f ≤ C • p := by
  rw [← quotient_smul, comp_liftQ_le_quotient_iff]

/-- The image of an open `p`-ball under the quotient map is the open ball of the quotient
seminorm. -/
theorem image_mkQ_ball (r : ℝ) : N.mkQ '' p.ball 0 r = (p.quotient N).ball 0 r := by
  ext q
  simp only [mem_image, Seminorm.mem_ball_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (quotient_mk_le p N x).trans_lt hx
  · intro h
    obtain ⟨x, hx, hx'⟩ := exists_lt_of_quotient_lt p N h
    exact ⟨x, hx', hx⟩

/-- The quotient seminorm of a continuous seminorm is continuous. -/
theorem continuous_quotient [TopologicalSpace E] [IsTopologicalAddGroup E]
    (hp : Continuous p) : Continuous (p.quotient N) := by
  refine Seminorm.continuous_of_forall fun r hr ↦ ?_
  rw [← image_mkQ_ball]
  have hball : p.ball 0 r ∈ 𝓝 (0 : E) := by
    have h := (isOpen_lt hp continuous_const : IsOpen {x | p x < r}).mem_nhds
      (show (0 : E) ∈ {x | p x < r} by simpa using hr)
    exact mem_of_superset h fun x hx ↦ by simpa [Seminorm.mem_ball_zero] using hx
  exact (Submodule.Quotient.nhds_zero_hasBasis_image N (𝓝 (0 : E)).basis_sets).mem_of_mem hball

end Seminorm
