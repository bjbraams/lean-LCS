/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Bipolar
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Mackey's theorem: weakly bounded sets are bounded

In a locally convex space over `ℝ` or `ℂ` a set on which every continuous linear functional is
bounded is bounded for the given topology. Consequently all locally convex topologies with the
same dual have the same bounded sets.

The usual proof applies the uniform boundedness principle in the Banach space spanned by the
polar of a neighbourhood of zero. The proof here avoids that auxiliary space. The polar `U°` of a
neighbourhood `U` of zero is weak-\* compact (Alaoglu–Bourbaki), hence a Baire space, and it is
the union of the weak-\* closed sets `{φ | ∀ x ∈ A, ‖φ x‖ ≤ n}`. One of them has an interior
point `φ₀` relative to `U°`. By the tube lemma there is `t ∈ (0, 1]` such that
`(1 - t) φ₀ + t ψ` lies in that interior for all `ψ ∈ U°` simultaneously, which bounds `A`
uniformly on `U°`. If `U` is closed, `ℝ`-convex and balanced, the bipolar theorem turns this into
the statement that `U` absorbs `A`.

## Main statements

* `StrongDual.exists_forall_polar_norm_le`: a set that is bounded under every continuous linear
  functional is uniformly bounded under the polar of any neighbourhood of zero. This holds in
  any topological vector space.
* `Bornology.isVonNBounded_of_forall_strongDual`: **Mackey's theorem**.
* `Bornology.isVonNBounded_iff_forall_strongDual`: a set in a locally convex space is bounded if
  and only if every continuous linear functional is bounded on it.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §3.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §5.3, IV §1.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §20.11

## Tags

Mackey, weakly bounded, bounded set, uniform boundedness
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- In a topological vector space, a set `A` on which every continuous linear functional is
bounded is uniformly bounded under the functionals in the polar of a neighbourhood of zero. -/
theorem StrongDual.exists_forall_polar_norm_le {U : Set E} (hU : U ∈ 𝓝 (0 : E)) {A : Set E}
    (h : ∀ φ : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ A, ‖φ x‖ ≤ C) :
    ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ StrongDual.polar 𝕜 U, ∀ x ∈ A, ‖ψ x‖ ≤ R := by
  -- The polar `K` of `U` is weak-* compact, hence a Baire space.
  let K : Set (WeakDual 𝕜 E) := WeakDual.polar 𝕜 U
  have hK : IsCompact K := WeakDual.isCompact_polar_of_mem_nhds hU
  have hKc : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKne : Nonempty K := ⟨⟨0, fun x _ ↦ by simp⟩⟩
  -- The closed sets `F n` cover `K`, so one of them has an interior point `φ₀`.
  let F : ℕ → Set K := fun n ↦ {φ | ∀ x ∈ A, ‖(φ : WeakDual 𝕜 E) x‖ ≤ n}
  have hFc (n : ℕ) : IsClosed (F n) := by
    have hF : F n = ⋂ x ∈ A, {φ : K | ‖(φ : WeakDual 𝕜 E) x‖ ≤ n} := by
      ext φ
      simp [F]
    rw [hF]
    exact isClosed_biInter fun x _ ↦ isClosed_le
      ((WeakDual.eval_continuous x).comp continuous_subtype_val).norm continuous_const
  have hFu : ⋃ n, F n = univ := eq_univ_of_forall fun φ ↦ by
    obtain ⟨C, hC⟩ := h (WeakDual.toStrongDual (φ : WeakDual 𝕜 E))
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact mem_iUnion.mpr ⟨n, fun x hx ↦ (hC x hx).trans hn⟩
  obtain ⟨n, φ₀, hφ₀⟩ := nonempty_interior_of_iUnion_of_closed hFc hFu
  obtain ⟨S, hSF, hSo, hφ₀S⟩ := mem_interior.mp hφ₀
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hSo
  -- By the tube lemma, `(1 - t) φ₀ + t ψ ∈ O` for some `t ∈ (0, 1]` and all `ψ ∈ K`.
  let G : ℝ × WeakDual 𝕜 E → WeakDual 𝕜 E := fun p ↦
    ((1 - p.1 : ℝ) : 𝕜) • (φ₀ : WeakDual 𝕜 E) + ((p.1 : ℝ) : 𝕜) • p.2
  have hG : Continuous G := by
    refine WeakDual.continuous_of_continuous_eval fun y ↦ ?_
    change Continuous fun p : ℝ × WeakDual 𝕜 E ↦
      ((1 - p.1 : ℝ) : 𝕜) * (φ₀ : WeakDual 𝕜 E) y + ((p.1 : ℝ) : 𝕜) * p.2 y
    have h2 : Continuous fun p : ℝ × WeakDual 𝕜 E ↦ p.2 y :=
      (WeakDual.eval_continuous y).comp continuous_snd
    fun_prop
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ G ⁻¹' O := by
    rintro ⟨t, ψ⟩ ⟨ht, -⟩
    have ht0 : t = 0 := ht
    have hG0 : G (t, ψ) = (φ₀ : WeakDual 𝕜 E) := by
      simp [G, ht0]
    rw [mem_preimage, hG0]
    exact hφ₀S
  obtain ⟨T, W, hTo, -, h0T, hKW, hTW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hO.preimage hG) hsub
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.mp hTo 0 (h0T rfl)
  let t : ℝ := min (ε / 2) 1
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htT : t ∈ T := hεT (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg ht0.le]
    exact (min_le_left _ _).trans_lt (half_lt_self hε))
  have hφ₀F : ∀ x ∈ A, ‖(φ₀ : WeakDual 𝕜 E) x‖ ≤ n := interior_subset hφ₀
  refine ⟨2 * n / t + 1, by positivity, fun ψ hψ x hx ↦ ?_⟩
  -- The functional `χ = (1 - t) φ₀ + t ψ` lies in `O ∩ K`, hence in `F n`.
  let χ : WeakDual 𝕜 E := G (t, StrongDual.toWeakDual ψ)
  have hχ (y : E) : χ y = ((1 - t : ℝ) : 𝕜) * (φ₀ : WeakDual 𝕜 E) y + ((t : ℝ) : 𝕜) * ψ y := rfl
  have hχO : χ ∈ O := hTW (⟨htT, hKW hψ⟩ : (t, StrongDual.toWeakDual ψ) ∈ T ×ˢ W)
  have hnorm1 : ‖((1 - t : ℝ) : 𝕜)‖ = 1 - t := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
  have hnormt : ‖((t : ℝ) : 𝕜)‖ = t := by rw [RCLike.norm_ofReal, abs_of_pos ht0]
  have hχK : χ ∈ K := fun u hu ↦ by
    change ‖χ u‖ ≤ 1
    rw [hχ]
    calc ‖((1 - t : ℝ) : 𝕜) * (φ₀ : WeakDual 𝕜 E) u + ((t : ℝ) : 𝕜) * ψ u‖
        ≤ (1 - t) * ‖(φ₀ : WeakDual 𝕜 E) u‖ + t * ‖ψ u‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, hnorm1, hnormt]
      _ ≤ (1 - t) * 1 + t * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (φ₀.2 u hu) (by linarith))
            (mul_le_mul_of_nonneg_left (hψ u hu) ht0.le)
      _ = 1 := by ring
  have hχn : ‖χ x‖ ≤ n := hSF (show (⟨χ, hχK⟩ : K) ∈ Subtype.val ⁻¹' O from hχO) x hx
  -- Solve for `ψ x`.
  have hψx : ((t : ℝ) : 𝕜) * ψ x = χ x - ((1 - t : ℝ) : 𝕜) * (φ₀ : WeakDual 𝕜 E) x := by
    rw [hχ]
    ring
  have h1 : t * ‖ψ x‖ ≤ 2 * n := by
    calc t * ‖ψ x‖ = ‖((t : ℝ) : 𝕜) * ψ x‖ := by rw [norm_mul, hnormt]
      _ = ‖χ x - ((1 - t : ℝ) : 𝕜) * (φ₀ : WeakDual 𝕜 E) x‖ := by rw [hψx]
      _ ≤ ‖χ x‖ + (1 - t) * ‖(φ₀ : WeakDual 𝕜 E) x‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, hnorm1]
      _ ≤ n + 1 * n :=
          add_le_add hχn (mul_le_mul (by linarith) (hφ₀F x hx) (norm_nonneg _) zero_le_one)
      _ = 2 * n := by ring
  calc ‖ψ x‖ = t * ‖ψ x‖ / t := by field_simp
    _ ≤ 2 * n / t := by gcongr
    _ ≤ 2 * n / t + 1 := by linarith

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- **Mackey's theorem**: in a locally convex space, a set on which every continuous linear
functional is bounded is von Neumann bounded. -/
theorem Bornology.isVonNBounded_of_forall_strongDual {A : Set E}
    (h : ∀ φ : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ A, ‖φ x‖ ≤ C) : IsVonNBounded 𝕜 A := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  intro V hV
  -- A closed, convex, balanced neighbourhood `U` of zero inside `V`.
  obtain ⟨V₁, hV₁, hV₁cl, hV₁V⟩ := exists_mem_nhds_isClosed_subset hV
  obtain ⟨W₀, ⟨hW₀, hW₀c, hW₀b⟩, hW₀V⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hV₁
  have hUV : closure W₀ ⊆ V := (closure_minimal hW₀V hV₁cl).trans hV₁V
  have hU : closure W₀ ∈ 𝓝 (0 : E) := mem_of_superset hW₀ subset_closure
  have hbip : (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 (closure W₀)) = closure W₀ :=
    StrongDual.bipolar_eq_self hW₀c.closure hW₀b.closure isClosed_closure
      ⟨0, mem_of_mem_nhds hU⟩
  refine Absorbs.mono_left ?_ hUV
  obtain ⟨R, hR0, hR⟩ := StrongDual.exists_forall_polar_norm_le hU h
  refine absorbs_iff_norm.mpr ⟨R, fun c hc x hx ↦ ?_⟩
  have hcpos : 0 < ‖c‖ := hR0.trans_le hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  rw [mem_smul_set_iff_inv_smul_mem₀ hc0, ← hbip]
  intro φ hφ
  change ‖φ (c⁻¹ • x)‖ ≤ 1
  rw [map_smul, norm_smul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
  exact (hR φ hφ x hx).trans hc

/-- A subset of a locally convex space is von Neumann bounded if and only if every continuous
linear functional is bounded on it. -/
theorem Bornology.isVonNBounded_iff_forall_strongDual {A : Set E} :
    IsVonNBounded 𝕜 A ↔ ∀ φ : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ A, ‖φ x‖ ≤ C := by
  refine ⟨fun hA φ ↦ ?_, Bornology.isVonNBounded_of_forall_strongDual⟩
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := 𝕜)).mp (hA.image φ)
  exact ⟨C, fun x hx ↦ hC _ ⟨x, hx, rfl⟩⟩
