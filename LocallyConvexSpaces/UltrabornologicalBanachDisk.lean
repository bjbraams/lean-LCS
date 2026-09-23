/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.BanachDisk
public import LocallyConvexSpaces.Bornological
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ultrabornological spaces and Banach disks

A Hausdorff locally convex space is ultrabornological if and only if it is the locally convex hull
of the
Banach spaces `E_B`, where `B` runs through the Banach disks of `E`
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7.(1)). Consequently a linear map
from an ultrabornological space into a locally convex space is continuous as soon as it is
bounded on every Banach disk (§35.7.(5) a) for linear functionals).

The main step is that the image of the closed unit ball of a Banach space under a continuous
linear map is a Banach disk. The completeness of the space spanned by the image is purely
algebraic: it holds for every linear map from a Banach space into a vector space.

## Main definitions

* `banachDisks 𝕜 E`: the set of Banach disks of `E`.

## Main statements

* `DiskSpace.completeSpace_image_closedBall`, `IsBanachDisk.image_closedBall`.
* `UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks`,
  `UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_banachDisks`,
  `ultrabornologicalSpace_iff_eq_locallyConvexFinalTopology_banachDisks`: Köthe II §35.7.(1).
* `LinearMap.continuous_of_forall_isVonNBounded_image_banachDisk`: Köthe II §35.7.(5) a).
* `DiskSpace.absorbs_of_preimage_incl_mem_nhds`,
  `DiskSpace.continuous_comp_incl_of_isVonNBounded_image`: two lemmas on the spaces `E_S`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7

## Tags

ultrabornological space, Banach disk
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

universe u v

section Image

variable {𝕜 : Type*} [RCLike 𝕜] {E X : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
  [IsScalarTower ℝ 𝕜 X] (f : X →ₗ[𝕜] E)

/-- The image of the closed unit ball under a linear map is convex. -/
theorem LinearMap.convex_image_closedBall : Convex ℝ (f '' Metric.closedBall (0 : X) 1) :=
  (convex_closedBall (0 : X) 1).is_linear_image (f.restrictScalars ℝ).isLinear

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- The image of the closed unit ball under a linear map is balanced. -/
theorem LinearMap.balanced_image_closedBall : Balanced 𝕜 (f '' Metric.closedBall (0 : X) 1) :=
  (balanced_closedBall_zero (𝕜 := 𝕜) (E := X) (r := 1)).image f

/-- The disk hull of the image of the closed unit ball is that image. -/
theorem LinearMap.diskHull_image_closedBall :
    diskHull 𝕜 (f '' Metric.closedBall (0 : X) 1) = f '' Metric.closedBall (0 : X) 1 :=
  diskHull_eq_self f.convex_image_closedBall f.balanced_image_closedBall
    ⟨0, 0, Metric.mem_closedBall_self zero_le_one, map_zero f⟩

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] in
/-- The range of a linear map on a normed space lies in the span of the image of the closed
unit ball. -/
theorem LinearMap.apply_mem_span_image_closedBall (x : X) :
    f x ∈ Submodule.span 𝕜 (f '' Metric.closedBall (0 : X) 1) := by
  have hr : (0 : ℝ) < ‖x‖ + 1 := by positivity
  have hmem : ((‖x‖ + 1 : ℝ) : 𝕜)⁻¹ • x ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hr,
      inv_mul_le_iff₀ hr]
    linarith
  have hne : ((‖x‖ + 1 : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hr.ne'
  have h : f x = ((‖x‖ + 1 : ℝ) : 𝕜) • f (((‖x‖ + 1 : ℝ) : 𝕜)⁻¹ • x) := by
    rw [← map_smul, smul_inv_smul₀ hne]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩)

namespace DiskSpace

/-- A point of the space spanned by the image of the closed unit ball under `f` whose norm is
less than `r` is the image of a point of norm at most `r`. -/
theorem exists_norm_le_map_eq_incl {d : DiskSpace 𝕜 (f '' Metric.closedBall (0 : X) 1)} {r : ℝ}
    (hr : 0 < r) (hd : ‖d‖ < r) : ∃ x : X, ‖x‖ ≤ r ∧ f x = incl 𝕜 _ d := by
  have h := incl_mem_smul_diskHull hr hd
  rw [f.diskHull_image_closedBall] at h
  obtain ⟨_, ⟨w, hw, rfl⟩, hwd⟩ := h
  have hwd' : r • f w = incl 𝕜 _ d := hwd
  refine ⟨r • w, ?_, by rw [LinearMap.map_smul_of_tower, hwd']⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hw)

/-- A point of the space spanned by the image of the closed unit ball under `f` that is the
image of a point of norm at most `r` has norm at most `r`. -/
theorem norm_le_of_incl_eq_map {z : DiskSpace 𝕜 (f '' Metric.closedBall (0 : X) 1)} {x : X}
    {r : ℝ} (hr : 0 < r) (hx : ‖x‖ ≤ r) (hzx : incl 𝕜 _ z = f x) : ‖z‖ ≤ r := by
  refine norm_le_of_incl_mem_smul_diskHull hr.le ?_
  rw [f.diskHull_image_closedBall, hzx]
  refine ⟨f (r⁻¹ • x), ⟨r⁻¹ • x, ?_, rfl⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
      inv_mul_le_iff₀ hr, mul_one]
    exact hx
  · change r • f (r⁻¹ • x) = f x
    rw [← LinearMap.map_smul_of_tower, smul_inv_smul₀ hr.ne']

/-- The space spanned by the image of the closed unit ball of a Banach space under a linear map
is complete for the gauge of that image. -/
theorem completeSpace_image_closedBall [CompleteSpace X] :
    CompleteSpace (DiskSpace 𝕜 (f '' Metric.closedBall (0 : X) 1)) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n ↦ (1 / 2 : ℝ) ^ n)
    (fun n ↦ by positivity) fun u hu ↦ ?_
  -- Lift the increments of `u` to `X` with control of the norm.
  have hd (n : ℕ) : ‖u (n + 1) - u n‖ < (1 / 2 : ℝ) ^ n := by
    have h := hu n (n + 1) n (Nat.le_succ n) le_rfl
    rwa [dist_eq_norm] at h
  choose x hxn hxf using fun n ↦ exists_norm_le_map_eq_incl f (by positivity) (hd n)
  let S : ℕ → X := fun n ↦ ∑ k ∈ Finset.range n, x k
  have hS (n : ℕ) : dist (S n) (S (n + 1)) ≤ 2 / 2 / 2 ^ n := by
    have h1 : S (n + 1) - S n = x n := by
      simp only [S]
      rw [Finset.sum_range_succ, add_sub_cancel_left]
    rw [dist_comm, dist_eq_norm, h1]
    refine (hxn n).trans (le_of_eq ?_)
    rw [one_div, inv_pow]
    ring
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hS)
  have htail (n : ℕ) : ‖S n - s‖ ≤ 2 / 2 ^ n := by
    rw [← dist_eq_norm]
    exact dist_le_of_le_geometric_two_of_tendsto hS hs n
  -- The limit is the point of `E_B` over `u 0 + f s`.
  have h0 : incl 𝕜 _ (u 0) ∈ Submodule.span 𝕜 (f '' Metric.closedBall (0 : X) 1) := (u 0).2
  obtain ⟨z, hz⟩ := exists_incl_eq (𝕜 := 𝕜)
    (Submodule.add_mem _ h0 (f.apply_mem_span_image_closedBall s))
  have hun (n : ℕ) : incl 𝕜 _ (u n) = incl 𝕜 _ (u 0) + f (S n) := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have h1 : incl 𝕜 _ (u (n + 1)) = incl 𝕜 _ (u n) + incl 𝕜 _ (u (n + 1) - u n) := by
        rw [map_sub]
        abel
      have h2 : S (n + 1) = S n + x n := Finset.sum_range_succ _ _
      rw [h1, ih, ← hxf n, h2, map_add, add_assoc]
  have hbound (n : ℕ) : ‖u n - z‖ ≤ 2 / 2 ^ n := by
    refine norm_le_of_incl_eq_map f (by positivity) (htail n) ?_
    rw [map_sub, map_sub, hun, hz]
    abel
  refine ⟨z, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

end DiskSpace

/-- The image of the closed unit ball of a Banach space under a continuous linear map is a
Banach disk. -/
theorem IsBanachDisk.image_closedBall [CompleteSpace X] [TopologicalSpace E]
    (hf : Continuous f) :
    IsBanachDisk 𝕜 (f '' Metric.closedBall (0 : X) 1) :=
  ⟨f.convex_image_closedBall, f.balanced_image_closedBall,
    (NormedSpace.isVonNBounded_closedBall 𝕜 X 1).image (⟨f, hf⟩ : X →L[𝕜] E),
    DiskSpace.completeSpace_image_closedBall f⟩

end Image

section DiskSpace

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- If the preimage of `W` in the space `E_S` spanned by `S` is a neighbourhood of zero for the
gauge of `S`, then `W` absorbs `S`. -/
theorem DiskSpace.absorbs_of_preimage_incl_mem_nhds {S W : Set E}
    (h : DiskSpace.incl 𝕜 S ⁻¹' W ∈ 𝓝 (0 : DiskSpace 𝕜 S)) : Absorbs 𝕜 W S := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
  refine absorbs_iff_norm.mpr ⟨(δ / 2)⁻¹, fun a ha s hs ↦ ?_⟩
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    exact absurd ha (not_le.mpr (inv_pos.mpr hδ2))
  obtain ⟨s', hs'⟩ := DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span hs)
  have hnorm : ‖s'‖ ≤ 1 :=
    DiskSpace.norm_le_one_of_mem_unitDisk (by
      change DiskSpace.incl 𝕜 S s' ∈ diskHull 𝕜 S
      rw [hs']
      exact subset_diskHull S hs)
  have hlt : ‖a⁻¹ • s'‖ < δ := by
    rw [norm_smul, norm_inv]
    have h1 : ‖a‖⁻¹ ≤ δ / 2 := by
      rw [inv_le_comm₀ (norm_pos_iff.mpr ha0) hδ2]
      exact ha
    calc ‖a‖⁻¹ * ‖s'‖ ≤ δ / 2 * 1 := mul_le_mul h1 hnorm (norm_nonneg _) hδ2.le
      _ < δ := by linarith
  have hmem : DiskSpace.incl 𝕜 S (a⁻¹ • s') ∈ W := hball (by simpa [dist_eq_norm] using hlt)
  rw [map_smul, hs'] at hmem
  exact ⟨a⁻¹ • s, hmem, smul_inv_smul₀ ha0 s⟩

/-- A linear map that is bounded on a nonempty disk `S` is continuous on the space `E_S` spanned
by `S` with the gauge of `S`. -/
theorem DiskSpace.continuous_comp_incl_of_isVonNBounded_image {S : Set E} (hc : Convex ℝ S)
    (hb : Balanced 𝕜 S) (hne : S.Nonempty) {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] (A : E →ₗ[𝕜] F)
    (hA : IsVonNBounded 𝕜 (A '' S)) : Continuous (A ∘ₗ DiskSpace.incl 𝕜 S) := by
  have hhull : diskHull 𝕜 S = S := diskHull_eq_self hc hb hne
  refine LinearMap.continuous_of_forall_isVonNBounded_image _ fun T hT ↦ ?_
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((NormedSpace.isVonNBounded_iff 𝕜).mp hT)
  have hr : (0 : ℝ) < max C 0 + 1 := by positivity
  have hbdd : IsVonNBounded 𝕜 (((max C 0 + 1 : ℝ) : 𝕜) • (A '' S)) := hA.smul_set _
  refine hbdd.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  have hlt : ‖z‖ < max C 0 + 1 :=
    lt_of_le_of_lt ((hC z hz).trans (le_max_left C 0)) (lt_add_one _)
  have hmem := DiskSpace.incl_mem_smul_diskHull hr hlt
  rw [hhull] at hmem
  obtain ⟨b, hb', hbz⟩ := hmem
  have hbz' : (max C 0 + 1 : ℝ) • b = DiskSpace.incl 𝕜 S z := hbz
  refine ⟨A b, ⟨b, hb', rfl⟩, ?_⟩
  change ((max C 0 + 1 : ℝ) : 𝕜) • A b = A (DiskSpace.incl 𝕜 S z)
  rw [← hbz', ← RCLike.real_smul_eq_coe_smul (K := 𝕜), A.map_smul_of_tower]

end DiskSpace

section Hull

variable (𝕜 : Type v) (E : Type u) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- The Banach disks of a topological vector space. -/
@[expose]
def banachDisks : Set (Set E) :=
  {B | IsBanachDisk 𝕜 B}

variable {𝕜 E}

/-- **An ultrabornological space is the locally convex hull of the Banach spaces `E_B` spanned
by its Banach disks**, Köthe II §35.7.(1). -/
theorem UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks
    [UltrabornologicalSpace 𝕜 E] :
    (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1 := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  have : ContinuousSMul 𝕜 E := UltrabornologicalSpace.continuousSMul 𝕜 E
  have : LocallyConvexSpace ℝ E := UltrabornologicalSpace.locallyConvexSpace 𝕜 E
  let g := fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  refine le_antisymm (hf.le.trans ?_) ?_
  · -- Every `f i` factors through the Banach disk `f i '' closedBall 0 1`.
    have _i1 := locallyConvexFinalTopology.isTopologicalAddGroup g
    have _i2 := locallyConvexFinalTopology.continuousSMul g
    have _i3 := locallyConvexFinalTopology.locallyConvexSpace g
    refine (locallyConvexFinalTopology.le_iff (t := locallyConvexFinalTopology g) f).mpr
      fun i ↦ ?_
    have hfi : Continuous (f i) := by
      have h := locallyConvexFinalTopology.continuous_apply f i
      rwa [← hf] at h
    let B : banachDisks 𝕜 E :=
      ⟨f i '' Metric.closedBall (0 : X i) 1, IsBanachDisk.image_closedBall (f i) hfi⟩
    let φ : X i →ₗ[𝕜] DiskSpace 𝕜 B.1 :=
      LinearMap.codRestrict (Submodule.span 𝕜 B.1) (f i)
        (f i).apply_mem_span_image_closedBall
    have hφ : Continuous φ := by
      refine AddMonoidHomClass.continuous_of_bound φ 1 fun x ↦ ?_
      rw [one_mul]
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      exact DiskSpace.norm_le_of_incl_eq_map (f i) (by positivity)
        (le_add_of_nonneg_right hε.le) rfl
    exact @Continuous.comp (X i) (DiskSpace 𝕜 B.1) E _ _ (locallyConvexFinalTopology g) _ _
      (locallyConvexFinalTopology.continuous_apply g B) hφ
  · exact (locallyConvexFinalTopology.le_iff g).mpr fun B ↦
      DiskSpace.continuous_incl B.2.isVonNBounded

/-- A Hausdorff space that is the locally convex hull of the spaces `E_B` for a family of Banach
disks `B` is ultrabornological. -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_diskSpace [T1Space E]
    {𝔖 : Set (Set E)} (h𝔖 : ∀ B ∈ 𝔖, IsBanachDisk 𝕜 B)
    (h : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1) :
    UltrabornologicalSpace 𝕜 E := by
  have : IsTopologicalAddGroup E := by
    have h1 := locallyConvexFinalTopology.isTopologicalAddGroup
      fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1
    rwa [← h] at h1
  have : ContinuousSMul 𝕜 E := by
    have h1 := locallyConvexFinalTopology.continuousSMul fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1
    rwa [← h] at h1
  have : LocallyConvexSpace ℝ E := by
    have h1 := locallyConvexFinalTopology.locallyConvexSpace
      fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1
    rwa [← h] at h1
  have hX (B : 𝔖) : UltrabornologicalSpace 𝕜 (DiskSpace 𝕜 B.1) := by
    let _ := DiskSpace.normedAddCommGroup (𝕜 := 𝕜) (h𝔖 B.1 B.2).isVonNBounded
    have : CompleteSpace (DiskSpace 𝕜 B.1) := (h𝔖 B.1 B.2).completeSpace
    infer_instance
  have key := locallyConvexFinalTopology.ultrabornologicalSpace (𝕜 := 𝕜)
    fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1
  rwa [← h] at key

/-- **A Hausdorff space that is the locally convex hull of the Banach spaces spanned by its
Banach disks is ultrabornological**, Köthe II §35.7.(1). -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_banachDisks [T1Space E]
    (h : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1) :
    UltrabornologicalSpace 𝕜 E :=
  UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_diskSpace (fun _ hB ↦ hB) h

/-- A Hausdorff topological vector space is ultrabornological if and only if it is the locally
convex hull of the Banach spaces spanned by its Banach disks, Köthe II §35.7.(1). -/
theorem ultrabornologicalSpace_iff_eq_locallyConvexFinalTopology_banachDisks [T1Space E] :
    UltrabornologicalSpace 𝕜 E ↔ (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1 :=
  ⟨fun _ ↦ UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks,
    UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_banachDisks⟩

/-- **A linear map from an ultrabornological space into a locally convex space that is bounded
on every Banach disk is continuous**; for linear functionals this is Köthe II §35.7.(5) a). -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image_banachDisk
    [UltrabornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] (A : E →ₗ[𝕜] F)
    (hA : ∀ B : Set E, IsBanachDisk 𝕜 B → IsVonNBounded 𝕜 (A '' B)) : Continuous A := by
  have heq := UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks (𝕜 := 𝕜) (E := E)
  let g := fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  have h : @Continuous E F (locallyConvexFinalTopology g) _ A := by
    refine (locallyConvexFinalTopology.continuous_iff g A).mpr fun B ↦ ?_
    rcases B.1.eq_empty_or_nonempty with hB | hne
    · -- The space spanned by the empty set is trivial.
      have hzero (z : DiskSpace 𝕜 B.1) : DiskSpace.incl 𝕜 B.1 z = 0 := by
        have hz : DiskSpace.incl 𝕜 B.1 z ∈ Submodule.span 𝕜 B.1 := z.2
        have hs : Submodule.span 𝕜 B.1 = ⊥ := by rw [hB, Submodule.span_empty]
        rw [hs] at hz
        exact (Submodule.mem_bot 𝕜).mp hz
      have : Subsingleton (DiskSpace 𝕜 B.1) :=
        ⟨fun x y ↦ DiskSpace.incl_injective (by rw [hzero x, hzero y])⟩
      exact continuous_of_discreteTopology
    · exact DiskSpace.continuous_comp_incl_of_isVonNBounded_image B.2.convex B.2.balanced hne A
        (hA B.1 B.2)
  rwa [← heq] at h

end Hull
