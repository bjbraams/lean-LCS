/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.UltrabornologicalBanachDisk
public import LocallyConvexSpaces.CountableSeminorms
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import MathlibExtras.Analysis.SeminormEstimates

/-!
# Fréchet spaces are ultrabornological

A complete, first-countable, Hausdorff locally convex space `E` over `ℝ` or `ℂ` is
ultrabornological: its topology is the final locally convex topology for a family of linear
maps from Banach spaces, which gives the seminorm condition of `UltrabornologicalSpace` through
`UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace`.

The Banach spaces used are copies of `ℓ¹(ℕ, 𝕜)`. For every sequence `x` in `E` that tends to zero
the map `a ↦ ∑' n, a n • x n` is a continuous linear map `ℓ¹(ℕ, 𝕜) → E` (`lp.tsumSMulCLM x hx`). If
`U` is a `ℝ`-convex balanced set whose preimage under each of these maps is a neighbourhood of zero,
then `U` absorbs every sequence tending to zero, and in a first-countable space such a set is a
neighbourhood of zero (`mem_nhds_zero_of_forall_absorbs_range`). This avoids the normed spaces `E_B`
spanned by Banach disks, through which the statement is usually proved.

## Main definitions

* `lp.tsumSMulCLM x hx`: for a sequence `x` tending to zero in a complete Hausdorff locally convex
  space, the continuous linear map `ℓ¹(ℕ, 𝕜) →L[𝕜] E`, `a ↦ ∑' n, a n • x n`.

## Main statements

* `lp.summable_smul_of_tendsto_zero`: the series `∑ a n • x n` converges for `a ∈ ℓ¹` and `x → 0`.
* `lp.tsumSMulCLM_single`: the value of `lp.tsumSMulCLM` on a coordinate sequence.
* `UltrabornologicalSpace.of_completeSpace_firstCountableTopology`: Fréchet spaces are
  ultrabornological.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §8
* [L. Narici and E. Beckenstein, *Topological Vector Spaces*][narici2010], Chapter 13

## Tags

Fréchet space, ultrabornological space, inductive limit of Banach spaces
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise lp

universe u v


section Series

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E]

/-- In a complete locally convex space the series `∑ a n • x n` converges for `a ∈ ℓ¹` and a
sequence `x` that tends to zero. -/
theorem lp.summable_smul_of_tendsto_zero (a : ℓ¹(ℕ, 𝕜)) {x : ℕ → E}
    (hx : Tendsto x atTop (𝓝 0)) : Summable fun n ↦ a n • x n := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨p, hp, hpe⟩ := exists_continuous_seminorm_ball_subset (𝕜 := 𝕜) he
  obtain ⟨C, hC0, hC⟩ := p.exists_forall_le_of_tendsto_zero hp hx
  have hsum : Summable fun n ↦ ‖a n‖ := by simpa using a.2.summable
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum (1 / (C + 1)) (by positivity)
  refine ⟨s, fun t ht ↦ hpe ?_⟩
  rw [Seminorm.mem_ball_zero]
  have h1 : ∑ n ∈ t, ‖a n‖ < 1 / (C + 1) := by
    have := hs t ht
    rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at this
  calc p (∑ n ∈ t, a n • x n) ≤ C * ∑ n ∈ t, ‖a n‖ := p.sum_smul_le_of_le t _ x fun n _ ↦ hC n
    _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1.le hC0
    _ < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith

variable [T2Space E]

/-- For a sequence `x` tending to zero in a complete Hausdorff locally convex space, the
continuous linear map `ℓ¹(ℕ, 𝕜) → E` that sends `a` to `∑' n, a n • x n`. -/
@[expose]
noncomputable def lp.tsumSMulCLM (x : ℕ → E) (hx : Tendsto x atTop (𝓝 0)) : ℓ¹(ℕ, 𝕜) →L[𝕜] E where
  toFun a := ∑' n, a n • x n
  map_add' a b := by
    rw [← (lp.summable_smul_of_tendsto_zero a hx).tsum_add (lp.summable_smul_of_tendsto_zero b hx)]
    refine tsum_congr fun n ↦ ?_
    rw [lp.coeFn_add, Pi.add_apply, add_smul]
  map_smul' c a := by
    rw [RingHom.id_apply, ← (lp.summable_smul_of_tendsto_zero a hx).tsum_const_smul c]
    refine tsum_congr fun n ↦ ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
  cont := by
    -- It suffices to bound every continuous seminorm of the sum by a multiple of the norm.
    let T : ℓ¹(ℕ, 𝕜) →ₗ[𝕜] E :=
      { toFun := fun a ↦ ∑' n, a n • x n
        map_add' := fun a b ↦ by
          rw [← (lp.summable_smul_of_tendsto_zero a hx).tsum_add
            (lp.summable_smul_of_tendsto_zero b hx)]
          refine tsum_congr fun n ↦ ?_
          rw [lp.coeFn_add, Pi.add_apply, add_smul]
        map_smul' := fun c a ↦ by
          rw [RingHom.id_apply, ← (lp.summable_smul_of_tendsto_zero a hx).tsum_const_smul c]
          refine tsum_congr fun n ↦ ?_
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul] }
    have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
    change Continuous T
    refine continuous_of_continuousAt_zero T ?_
    rw [ContinuousAt, map_zero]
    intro e he
    obtain ⟨p, hp, hpe⟩ := exists_continuous_seminorm_ball_subset (𝕜 := 𝕜) he
    obtain ⟨C, hC0, hC⟩ := p.exists_forall_le_of_tendsto_zero hp hx
    have hball : Metric.ball (0 : ℓ¹(ℕ, 𝕜)) (1 / (C + 1)) ∈ 𝓝 (0 : ℓ¹(ℕ, 𝕜)) :=
      Metric.ball_mem_nhds 0 (by positivity)
    refine mem_map.mpr (mem_of_superset hball fun a ha ↦ hpe ?_)
    rw [Metric.mem_ball, dist_zero_right] at ha
    rw [Seminorm.mem_ball_zero]
    -- Pass to the limit in the estimate for partial sums.
    have hlim : Tendsto (fun t : Finset ℕ ↦ p (∑ n ∈ t, a n • x n)) atTop (𝓝 (p (T a))) :=
      (hp.tendsto _).comp (lp.summable_smul_of_tendsto_zero a hx).hasSum
    have hle : p (T a) ≤ C * ‖a‖ :=
      le_of_tendsto hlim (Eventually.of_forall fun t ↦
        (p.sum_smul_le_of_le t _ x fun n _ ↦ hC n).trans
          (mul_le_mul_of_nonneg_left (lp.sum_norm_le_norm_one a t) hC0))
    calc p (T a) ≤ C * ‖a‖ := hle
      _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left ha.le hC0
      _ < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith

/-- The defining formula of `lp.tsumSMulCLM`. -/
theorem lp.tsumSMulCLM_apply (x : ℕ → E) (hx : Tendsto x atTop (𝓝 0)) (a : ℓ¹(ℕ, 𝕜)) :
    lp.tsumSMulCLM x hx a = ∑' n, a n • x n :=
  rfl

/-- The value of `lp.tsumSMulCLM` on a coordinate sequence. -/
theorem lp.tsumSMulCLM_single (x : ℕ → E) (hx : Tendsto x atTop (𝓝 0)) (n : ℕ) (c : 𝕜) :
    lp.tsumSMulCLM x hx (lp.single 1 n c) = c • x n := by
  rw [lp.tsumSMulCLM_apply, tsum_eq_single n]
  · rw [lp.single_apply_self]
  · intro m hm
    rw [lp.single_apply_ne _ _ _ hm, zero_smul]

end Series

section Frechet

variable {𝕜 : Type v} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E] [FirstCountableTopology E] [T2Space E]

/-- A complete, first-countable, Hausdorff locally convex space (a Fréchet space) is
ultrabornological: its topology is the final locally convex topology for the maps
`lp.tsumSMulCLM x hx : ℓ¹(ℕ, 𝕜) → E`, where `x` ranges over the sequences in `E` that tend to
zero. -/
instance (priority := 100) UltrabornologicalSpace.of_completeSpace_firstCountableTopology :
    UltrabornologicalSpace 𝕜 E := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let ι : Type u := {x : ℕ → E // Tendsto x atTop (𝓝 0)}
  let f : ∀ _ : ι, ℓ¹(ℕ, 𝕜) →ₗ[𝕜] E := fun x ↦ (lp.tsumSMulCLM x.1 x.2).toLinearMap
  refine UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace f ?_
  refine le_antisymm ?_ ?_
  · -- Every neighbourhood of zero for the final topology is one for the given topology.
    have h1 := locallyConvexFinalTopology.isTopologicalAddGroup f
    have h2 := locallyConvexFinalTopology.continuousSMul f
    have h3 := locallyConvexFinalTopology.locallyConvexSpace f
    rw [le_iff_nhds]
    intro y
    rw [← map_add_left_nhds_zero y, ← @map_add_left_nhds_zero E (locallyConvexFinalTopology f) _
      h1 y]
    refine Filter.map_mono fun U hU ↦ ?_
    obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ :=
      (@nhds_zero_hasBasis_convex_balanced 𝕜 E _ _ _ _ _ (locallyConvexFinalTopology f) h2
        h3).mem_iff.mp hU
    refine mem_of_superset ?_ hWU
    -- `W` absorbs every sequence tending to zero.
    refine mem_nhds_zero_of_forall_absorbs_range (𝕜 := 𝕜) fun x hx ↦ ?_
    have hcont := locallyConvexFinalTopology.continuous_apply f ⟨x, hx⟩
    obtain ⟨O, hOW, hO, h0O⟩ := (@mem_nhds_iff E (locallyConvexFinalTopology f) 0 W).mp hW
    have hOpen : IsOpen (f ⟨x, hx⟩ ⁻¹' O) :=
      @Continuous.isOpen_preimage _ E _ (locallyConvexFinalTopology f) _ hcont O hO
    have h0 : (0 : ℓ¹(ℕ, 𝕜)) ∈ f ⟨x, hx⟩ ⁻¹' O := by
      rw [mem_preimage, map_zero]
      exact h0O
    have hpre : f ⟨x, hx⟩ ⁻¹' W ∈ 𝓝 (0 : ℓ¹(ℕ, 𝕜)) :=
      mem_of_superset (hOpen.mem_nhds h0) (preimage_mono hOW)
    obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hpre
    have hmem (n : ℕ) : ((δ / 2 : ℝ) : 𝕜) • x n ∈ W := by
      have hball : lp.single 1 n ((δ / 2 : ℝ) : 𝕜) ∈ Metric.ball (0 : ℓ¹(ℕ, 𝕜)) δ := by
        rw [Metric.mem_ball, dist_zero_right, lp.norm_single one_pos,
          RCLike.norm_ofReal, abs_of_pos (half_pos hδ)]
        exact half_lt_self hδ
      have h := hδW hball
      change lp.tsumSMulCLM x hx (lp.single 1 n ((δ / 2 : ℝ) : 𝕜)) ∈ W at h
      rwa [lp.tsumSMulCLM_single] at h
    have hne : ((δ / 2 : ℝ) : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero]
      exact (half_pos hδ).ne'
    refine absorbs_iff_norm.mpr ⟨(δ / 2)⁻¹, fun c hc ↦ ?_⟩
    rintro _ ⟨n, rfl⟩
    have hcpos : 0 < ‖c‖ := (inv_pos.mpr (half_pos hδ)).trans_le hc
    have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
    rw [mem_smul_set_iff_inv_smul_mem₀ hc0]
    have hsm : c⁻¹ • x n = (c⁻¹ * (((δ / 2 : ℝ) : 𝕜))⁻¹) • (((δ / 2 : ℝ) : 𝕜) • x n) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rw [hsm]
    refine balanced_iff_smul_mem.mp hWb ?_ (hmem n)
    rw [norm_mul, norm_inv, norm_inv, RCLike.norm_ofReal, abs_of_pos (half_pos hδ)]
    calc ‖c‖⁻¹ * (δ / 2)⁻¹ ≤ ((δ / 2)⁻¹)⁻¹ * (δ / 2)⁻¹ := by
          gcongr
      _ = 1 := by
          rw [inv_inv]
          exact mul_inv_cancel₀ (half_pos hδ).ne'
  · exact (locallyConvexFinalTopology.le_iff f).mpr fun x ↦ (lp.tsumSMulCLM x.1 x.2).continuous

end Frechet
