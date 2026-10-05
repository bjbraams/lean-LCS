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

For every family `x : ι → E` with von Neumann bounded range the map `a ↦ ∑' i, a i • x i` is a
continuous linear map `ℓ¹(ι, 𝕜) → E` (`lp.tsumSMulCLM x hx`), the synthesis operator of `x`.
The Banach spaces used here are copies of `ℓ¹(ℕ, 𝕜)`, one for each sequence `x` in `E` that tends
to zero. If `U` is a `ℝ`-convex balanced set whose preimage under each of these maps is a
neighbourhood of zero, then `U` absorbs every sequence tending to zero, and in a first-countable
space such a set is a neighbourhood of zero (`mem_nhds_zero_of_forall_absorbs_range`). This avoids
the normed spaces `E_B` spanned by Banach disks, through which the statement is usually proved.

## Main definitions

* `lp.tsumSMulCLM x hx`: for a family `x : ι → E` with von Neumann bounded range in a complete
  Hausdorff locally convex space, the continuous linear map `ℓ¹(ι, 𝕜) →L[𝕜] E`,
  `a ↦ ∑' i, a i • x i`.

## Main statements

* `lp.summable_smul_of_isVonNBounded`: the series `∑ a i • x i` converges for `a ∈ ℓ¹(ι, 𝕜)`
  and a family `x` with bounded range.
* `lp.summable_smul_of_tendsto_zero`: the special case of a sequence `x` tending to zero.
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

variable {𝕜 E ι : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E]

/-- In a complete locally convex space the series `∑ a i • x i` converges for `a ∈ ℓ¹(ι, 𝕜)` and
a family `x` with von Neumann bounded range. -/
theorem lp.summable_smul_of_isVonNBounded (a : ℓ¹(ι, 𝕜)) {x : ι → E}
    (hx : IsVonNBounded 𝕜 (range x)) : Summable fun i ↦ a i • x i := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨p, hp, hpe⟩ := exists_continuous_seminorm_ball_subset (𝕜 := 𝕜) he
  obtain ⟨C, hC0, hC⟩ := p.exists_forall_le_of_isVonNBounded hp hx
  have hsum : Summable fun i ↦ ‖a i‖ := by simpa using a.2.summable
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum (1 / (C + 1)) (by positivity)
  refine ⟨s, fun t ht ↦ hpe ?_⟩
  rw [Seminorm.mem_ball_zero]
  have h1 : ∑ i ∈ t, ‖a i‖ < 1 / (C + 1) := by
    have := hs t ht
    rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at this
  calc p (∑ i ∈ t, a i • x i) ≤ C * ∑ i ∈ t, ‖a i‖ := p.sum_smul_le_of_le t _ x fun i _ ↦ hC i
    _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1.le hC0
    _ < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith

/-- In a complete locally convex space the series `∑ a n • x n` converges for `a ∈ ℓ¹` and a
sequence `x` that tends to zero. -/
theorem lp.summable_smul_of_tendsto_zero (a : ℓ¹(ℕ, 𝕜)) {x : ℕ → E}
    (hx : Tendsto x atTop (𝓝 0)) : Summable fun n ↦ a n • x n :=
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  lp.summable_smul_of_isVonNBounded a (hx.isVonNBounded_range 𝕜)

variable [T2Space E]

/-- **The synthesis operator of a bounded family.** For a family `x` with von Neumann bounded
range in a complete Hausdorff locally convex space, the continuous linear map
`ℓ¹(ι, 𝕜) → E` that sends `a` to `∑' i, a i • x i`. Every continuous seminorm `p` satisfies
`p (∑' i, a i • x i) ≤ C * ‖a‖` for a bound `C` of `p` on the family. -/
@[expose]
noncomputable def lp.tsumSMulCLM (x : ι → E) (hx : IsVonNBounded 𝕜 (range x)) :
    ℓ¹(ι, 𝕜) →L[𝕜] E :=
  let T : ℓ¹(ι, 𝕜) →ₗ[𝕜] E :=
    { toFun := fun a ↦ ∑' i, a i • x i
      map_add' := fun a b ↦ by
        rw [← (lp.summable_smul_of_isVonNBounded a hx).tsum_add
          (lp.summable_smul_of_isVonNBounded b hx)]
        refine tsum_congr fun i ↦ ?_
        rw [lp.coeFn_add, Pi.add_apply, add_smul]
      map_smul' := fun c a ↦ by
        rw [RingHom.id_apply, ← (lp.summable_smul_of_isVonNBounded a hx).tsum_const_smul c]
        refine tsum_congr fun i ↦ ?_
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul] }
  { T with
    cont := by
      -- It suffices to bound every continuous seminorm of the sum by a multiple of the norm.
      have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
      change Continuous T
      refine continuous_of_continuousAt_zero T ?_
      rw [ContinuousAt, map_zero]
      intro e he
      obtain ⟨p, hp, hpe⟩ := exists_continuous_seminorm_ball_subset (𝕜 := 𝕜) he
      obtain ⟨C, hC0, hC⟩ := p.exists_forall_le_of_isVonNBounded hp hx
      have hball : Metric.ball (0 : ℓ¹(ι, 𝕜)) (1 / (C + 1)) ∈ 𝓝 (0 : ℓ¹(ι, 𝕜)) :=
        Metric.ball_mem_nhds 0 (by positivity)
      refine mem_map.mpr (mem_of_superset hball fun a ha ↦ hpe ?_)
      rw [Metric.mem_ball, dist_zero_right] at ha
      rw [Seminorm.mem_ball_zero]
      -- Pass to the limit in the estimate for partial sums.
      have hlim : Tendsto (fun t : Finset ι ↦ p (∑ i ∈ t, a i • x i)) atTop (𝓝 (p (T a))) :=
        (hp.tendsto _).comp (lp.summable_smul_of_isVonNBounded a hx).hasSum
      have hle : p (T a) ≤ C * ‖a‖ :=
        le_of_tendsto hlim (Eventually.of_forall fun t ↦
          (p.sum_smul_le_of_le t _ x fun i _ ↦ hC i).trans
            (mul_le_mul_of_nonneg_left (lp.sum_norm_le_norm_one a t) hC0))
      calc p (T a) ≤ C * ‖a‖ := hle
        _ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left ha.le hC0
        _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]
          linarith }

/-- The defining formula of `lp.tsumSMulCLM`. -/
theorem lp.tsumSMulCLM_apply (x : ι → E) (hx : IsVonNBounded 𝕜 (range x)) (a : ℓ¹(ι, 𝕜)) :
    lp.tsumSMulCLM x hx a = ∑' i, a i • x i :=
  rfl

/-- The value of `lp.tsumSMulCLM` on a coordinate sequence. -/
theorem lp.tsumSMulCLM_single [DecidableEq ι] (x : ι → E) (hx : IsVonNBounded 𝕜 (range x))
    (i : ι) (c : 𝕜) : lp.tsumSMulCLM x hx (lp.single 1 i c) = c • x i := by
  rw [lp.tsumSMulCLM_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, zero_smul]

end Series

section Frechet

variable {𝕜 : Type v} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E] [FirstCountableTopology E] [T2Space E]

/-- A complete, first-countable, Hausdorff locally convex space (a Fréchet space) is
ultrabornological: its topology is the final locally convex topology for the maps
`lp.tsumSMulCLM x _ : ℓ¹(ℕ, 𝕜) → E`, where `x` ranges over the sequences in `E` that tend to
zero. -/
instance (priority := 100) UltrabornologicalSpace.of_completeSpace_firstCountableTopology :
    UltrabornologicalSpace 𝕜 E := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let ι : Type u := {x : ℕ → E // Tendsto x atTop (𝓝 0)}
  let f : ∀ _ : ι, ℓ¹(ℕ, 𝕜) →ₗ[𝕜] E := fun x ↦
    (lp.tsumSMulCLM x.1 (x.2.isVonNBounded_range 𝕜)).toLinearMap
  refine UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace f ?_
  refine le_antisymm ?_ ?_
  · -- Every neighbourhood of zero for the final topology is one for the given topology.
    have h1 := locallyConvexFinalTopology.isTopologicalAddGroup f
    rw [le_iff_nhds]
    intro y
    rw [← map_add_left_nhds_zero y, ← @map_add_left_nhds_zero E (locallyConvexFinalTopology f) _
      h1 y]
    refine Filter.map_mono fun U hU ↦ ?_
    -- `U` absorbs every sequence `x` tending to zero: its preimage under `f x` absorbs the
    -- closed unit ball of `ℓ¹`, whose image contains the range of `x`.
    refine mem_nhds_zero_of_forall_absorbs_range (𝕜 := 𝕜) fun x hx ↦ ?_
    have hpre : f ⟨x, hx⟩ ⁻¹' U ∈ 𝓝 (0 : ℓ¹(ℕ, 𝕜)) :=
      locallyConvexFinalTopology.preimage_mem_nhds_zero f ⟨x, hx⟩ hU
    refine ((((NormedSpace.isVonNBounded_closedBall 𝕜 ℓ¹(ℕ, 𝕜) 1) hpre).image_linearMap
      (f ⟨x, hx⟩)).mono_left (image_preimage_subset _ _)).mono_right ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨lp.single 1 n 1, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, lp.norm_single one_pos, norm_one]
    · change lp.tsumSMulCLM x (hx.isVonNBounded_range 𝕜) (lp.single 1 n 1) = x n
      rw [lp.tsumSMulCLM_single, one_smul]
  · exact (locallyConvexFinalTopology.le_iff f).mpr fun x ↦
    (lp.tsumSMulCLM x.1 (x.2.isVonNBounded_range 𝕜)).continuous

end Frechet
