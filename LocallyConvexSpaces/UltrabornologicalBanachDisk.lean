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

A locally convex space is ultrabornological if and only if every seminorm that is bounded on the
Banach disks is continuous, and if and only if it is the locally convex hull of the complete
seminormed spaces `E_B`, where `B` runs through the Banach disks of `E` ([G. Köthe, *Topological
Vector Spaces II*][kothe1979], §35.7.(1)). No separation is needed. Consequently a linear map from
an ultrabornological space into a locally convex space is continuous as soon as it is bounded on
every Banach disk (§35.7.(5) a) for linear functionals).

The main step is that the image of the closed unit ball of a complete seminormed space under a
continuous linear map is a Banach disk, and that the map factors through the space spanned by
that disk. The completeness of this space is purely algebraic: it holds for every linear map from
a complete seminormed space into a vector space.

## Main definitions

* `banachDisks 𝕜 E`: the set of Banach disks of `E`.

## Main statements

* `DiskSpace.completeSpace_image_closedBall`, `IsBanachDisk.image_closedBall`,
  `ContinuousLinearMap.isBanachDisk_image_closedBall`,
  `ContinuousLinearMap.exists_diskSpace_comp_eq`.
* `UltrabornologicalSpace.continuous_of_forall_bddAbove`,
  `UltrabornologicalSpace.of_forall_bddAbove`, `ultrabornologicalSpace_iff_forall_bddAbove`:
  seminorms bounded on the Banach disks.
* `UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace`: final locally
  convex topologies of complete seminormed spaces in arbitrary universes.
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
  [IsScalarTower ℝ 𝕜 E] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
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

section Factor

variable {𝕜 : Type*} [RCLike 𝕜] {E X : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] (f : X →L[𝕜] E)

/-- The image of the closed unit ball of a complete seminormed space under a continuous linear
map is a Banach disk. Unlike `IsBanachDisk.image_closedBall`, no real structure on `X` is
assumed. -/
theorem ContinuousLinearMap.isBanachDisk_image_closedBall :
    IsBanachDisk 𝕜 (f '' Metric.closedBall (0 : X) 1) :=
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  haveI : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
  IsBanachDisk.image_closedBall f.toLinearMap f.continuous

omit [CompleteSpace X] in
/-- A continuous linear map from a complete seminormed space into `E` factors through a
continuous linear map into the space `E_B` spanned by the Banach disk `B = f '' closedBall 0 1`,
of norm at most one. -/
theorem ContinuousLinearMap.exists_diskSpace_comp_eq :
    ∃ φ : X →L[𝕜] DiskSpace 𝕜 (f '' Metric.closedBall (0 : X) 1),
      (∀ x, DiskSpace.incl 𝕜 _ (φ x) = f x) ∧ ∀ x, ‖φ x‖ ≤ ‖x‖ := by
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
  let φ : X →ₗ[𝕜] DiskSpace 𝕜 (f '' Metric.closedBall (0 : X) 1) :=
    LinearMap.codRestrict (Submodule.span 𝕜 _) f.toLinearMap
      f.toLinearMap.apply_mem_span_image_closedBall
  have hφ (x : X) : ‖φ x‖ ≤ ‖x‖ := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    exact DiskSpace.norm_le_of_incl_eq_map f.toLinearMap (by positivity)
      (le_add_of_nonneg_right hε.le) rfl
  refine ⟨⟨φ, AddMonoidHomClass.continuous_of_bound φ 1 fun x ↦ ?_⟩, fun _ ↦ rfl, hφ⟩
  rw [one_mul]
  exact hφ x

end Factor

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
  have := PolynormableSpace.of_locallyConvexSpace_real 𝕜 F
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

/-- A seminorm on an ultrabornological space that is bounded on every Banach disk is
continuous. -/
theorem UltrabornologicalSpace.continuous_of_forall_bddAbove [UltrabornologicalSpace 𝕜 E]
    (p : Seminorm 𝕜 E) (h : ∀ B : Set E, IsBanachDisk 𝕜 B → BddAbove (p '' B)) :
    Continuous p :=
  UltrabornologicalSpace.continuous_of_forall_continuous_comp p fun X _ _ _ f ↦ by
    obtain ⟨C, hC⟩ := h _ f.isBanachDisk_image_closedBall
    exact (p.comp f.toLinearMap).continuous_of_bddAbove_closedBall
      ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC ⟨f x, ⟨x, hx, rfl⟩, rfl⟩⟩

omit [TopologicalSpace E] in
/-- A seminorm `p` whose composition with the inclusion of the space `E_B` spanned by a set
`B` is continuous is bounded on `B`. -/
theorem DiskSpace.bddAbove_image_of_continuous (p : Seminorm 𝕜 E) {B : Set E}
    (hp : Continuous fun y : DiskSpace 𝕜 B ↦ p (DiskSpace.incl 𝕜 B y)) : BddAbove (p '' B) := by
  obtain ⟨C, hC⟩ := (p.comp (DiskSpace.incl 𝕜 B)).bddAbove_image_closedBall_of_continuous hp
  refine ⟨C, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨y, hy⟩ := DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span hb)
  have hy1 : ‖y‖ ≤ 1 := DiskSpace.norm_le_of_incl_mem_smul_diskHull zero_le_one
    (by rw [one_smul, hy]; exact subset_diskHull B hb)
  rw [← hy]
  exact hC ⟨y, mem_closedBall_zero_iff.mpr hy1, rfl⟩

/-- A real or complex locally convex space in which every seminorm that is bounded on the
Banach disks is continuous is ultrabornological. No separation is needed. -/
theorem UltrabornologicalSpace.of_forall_bddAbove [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E]
    (h : ∀ p : Seminorm 𝕜 E, (∀ B : Set E, IsBanachDisk 𝕜 B → BddAbove (p '' B)) →
      Continuous p) :
    UltrabornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ h p fun B hB ↦ by
    have : CompleteSpace (DiskSpace 𝕜 B) := hB.completeSpace
    exact DiskSpace.bddAbove_image_of_continuous p
      (hp (DiskSpace 𝕜 B) ⟨DiskSpace.incl 𝕜 B, DiskSpace.continuous_incl hB.isVonNBounded⟩)⟩

/-- **A real or complex locally convex space is ultrabornological if and only if every seminorm
that is bounded on the Banach disks is continuous**; compare Köthe II §35.7.(1). -/
theorem ultrabornologicalSpace_iff_forall_bddAbove [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    UltrabornologicalSpace 𝕜 E ↔ ∀ p : Seminorm 𝕜 E,
      (∀ B : Set E, IsBanachDisk 𝕜 B → BddAbove (p '' B)) → Continuous p :=
  ⟨fun _ ↦ UltrabornologicalSpace.continuous_of_forall_bddAbove,
    UltrabornologicalSpace.of_forall_bddAbove⟩

/-- A space whose topology is the final locally convex topology for a family of linear maps
from complete seminormed spaces, in arbitrary universes, is ultrabornological. The maps are
tested through the spaces `E_B` of the Banach disks `B = f i '' closedBall 0 1`. -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace {ι : Type*}
    {X : ι → Type*} [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    [∀ i, CompleteSpace (X i)] (f : ∀ i, X i →ₗ[𝕜] E)
    (h : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology f) :
    UltrabornologicalSpace 𝕜 E := by
  have : IsTopologicalAddGroup E := by
    have h1 := locallyConvexFinalTopology.isTopologicalAddGroup f
    rwa [← h] at h1
  have : ContinuousSMul 𝕜 E := by
    have h1 := locallyConvexFinalTopology.continuousSMul f
    rwa [← h] at h1
  have : LocallyConvexSpace ℝ E := by
    have h1 := locallyConvexFinalTopology.locallyConvexSpace f
    rwa [← h] at h1
  have hfi (i : ι) : Continuous (f i) := by
    have h1 := locallyConvexFinalTopology.continuous_apply f i
    rwa [← h] at h1
  refine UltrabornologicalSpace.of_forall_bddAbove fun p hp ↦ ?_
  have key := locallyConvexFinalTopology.continuous_seminorm f p fun i ↦ by
    obtain ⟨C, hC⟩ := hp _ (ContinuousLinearMap.isBanachDisk_image_closedBall ⟨f i, hfi i⟩)
    exact (p.comp (f i)).continuous_of_bddAbove_closedBall
      ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC ⟨f i x, ⟨x, hx, rfl⟩, rfl⟩⟩
  rwa [← h] at key

/-- **An ultrabornological locally convex space is the locally convex hull of the Banach spaces
`E_B` spanned by its Banach disks**, Köthe II §35.7.(1). No separation is needed. -/
theorem UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [UltrabornologicalSpace 𝕜 E] :
    (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1 := by
  let g := fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  refine le_antisymm ?_ ((locallyConvexFinalTopology.le_iff g).mpr fun B ↦
    DiskSpace.continuous_incl B.2.isVonNBounded)
  -- A convex balanced neighbourhood of zero for the hull topology is a neighbourhood of zero.
  refine TopologicalSpace.le_of_nhds_zero_le inferInstance
    (locallyConvexFinalTopology.isTopologicalAddGroup g) fun U hU ↦ ?_
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ :=
    (@nhds_zero_hasBasis_convex_balanced 𝕜 E _ _ _ _ _ (locallyConvexFinalTopology g)
      (locallyConvexFinalTopology.continuousSMul g)
      (locallyConvexFinalTopology.locallyConvexSpace g)).mem_iff.mp hU
  have habs : Absorbent 𝕜 W :=
    @absorbent_nhds_zero 𝕜 E _ _ _ W (locallyConvexFinalTopology g)
      (locallyConvexFinalTopology.continuousSMul g) hW
  refine mem_of_superset (UltrabornologicalSpace.mem_nhds_zero hWc hWb habs fun X _ _ _ f ↦ ?_)
    hWU
  -- A map from a complete seminormed space factors through the space of a Banach disk.
  obtain ⟨φ, hφ, -⟩ := f.exists_diskSpace_comp_eq
  have hpre := locallyConvexFinalTopology.preimage_mem_nhds_zero g
    ⟨_, f.isBanachDisk_image_closedBall⟩ hW
  have h1 := φ.continuous.continuousAt.preimage_mem_nhds (x := 0) (by rw [map_zero]; exact hpre)
  convert h1 using 1
  ext x
  simp only [mem_preimage, g, hφ]

/-- A space that is the locally convex hull of the spaces `E_B` for a family of Banach disks
`B` is ultrabornological. -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_diskSpace {𝔖 : Set (Set E)}
    (h𝔖 : ∀ B ∈ 𝔖, IsBanachDisk 𝕜 B)
    (h : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : 𝔖 ↦ DiskSpace.incl 𝕜 B.1) :
    UltrabornologicalSpace 𝕜 E := by
  have (B : 𝔖) : CompleteSpace (DiskSpace 𝕜 B.1) := (h𝔖 B.1 B.2).completeSpace
  exact UltrabornologicalSpace.of_eq_locallyConvexFinalTopology _ h

/-- **A space that is the locally convex hull of the Banach spaces spanned by its Banach disks
is ultrabornological**, Köthe II §35.7.(1). -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_banachDisks
    (h : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1) :
    UltrabornologicalSpace 𝕜 E :=
  UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_diskSpace (fun _ hB ↦ hB) h

/-- A locally convex space is ultrabornological if and only if it is the locally convex hull
of the Banach spaces spanned by its Banach disks, Köthe II §35.7.(1). -/
theorem ultrabornologicalSpace_iff_eq_locallyConvexFinalTopology_banachDisks
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    UltrabornologicalSpace 𝕜 E ↔ (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1 :=
  ⟨fun _ ↦ UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks,
    UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_banachDisks⟩

/-- **A linear map from an ultrabornological space into a locally convex space that is bounded
on every Banach disk is continuous**; for linear functionals this is Köthe II §35.7.(5) a). -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image_banachDisk [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [UltrabornologicalSpace 𝕜 E] {F : Type*}
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
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
