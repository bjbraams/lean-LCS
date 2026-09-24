/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.PolarCalculus
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Basic
public import MathlibExtras.Analysis.ConvexHull

/-!
# Banach disks and the normed spaces `E_B`

A *disk* in a vector space `E` is a convex balanced set `B`. It spans a subspace `E_B` of `E`,
on which the gauge of `B` is a seminorm; if `E` is a Hausdorff topological vector space and `B`
is bounded, the gauge is a norm and the inclusion `E_B → E` is continuous. The disk `B` is a
*Banach disk* if `E_B` is complete.

## Implementation

`DiskSpace 𝕜 B` is a type synonym of the span of `B`. It is defined for an arbitrary set `B`
and carries the gauge of the *disk hull* `diskHull 𝕜 B`, the convex balanced hull of
`insert 0 B`, which is `B` itself when `B` is a nonempty disk. In this way the instances
`SeminormedAddCommGroup` and `NormedSpace` need no hypotheses on `B`, nothing has to be bundled,
and hypotheses on `B` appear only in theorems. This keeps the algebraic span independent of
its ambient topology. The empty set is allowed: its disk hull is `{0}` and its span is zero.
Without separation the resulting complete space can be only seminormed; the usual Banach-space
interpretation applies when the bounded disk lies in a Hausdorff topological vector space.

## Main definitions

* `diskHull 𝕜 B`, `DiskSpace 𝕜 B`, `DiskSpace.incl`, `DiskSpace.unitDisk`.
* `DiskSpace.normedAddCommGroup`: the norm structure for a bounded set in a Hausdorff space;
  a definition, not an instance.
* `Bornology.IsBanachDisk 𝕜 B`.

## Main statements

* `DiskSpace.continuous_incl`: for bounded `B` in a locally convex space the inclusion of
  `DiskSpace 𝕜 B` is continuous.
* `DiskSpace.eq_zero_of_norm_eq_zero`: for bounded `B` in a Hausdorff space the gauge is a norm.
* `DiskSpace.completeSpace_of_isComplete`: if a bounded disk `B` is complete as a subset of a
  Hausdorff locally convex space, in particular if it is compact, then `DiskSpace 𝕜 B` is
  complete.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §1.5
* [L. Narici and E. Beckenstein, *Topological Vector Spaces*][narici2010], 13.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §20.11

## Tags

Banach disk, gauge, bounded set, normed space
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- The **disk hull** of a set `B`: the convex balanced hull of `insert 0 B`. It is `B` itself if
`B` is a nonempty convex balanced set. -/
@[expose]
def diskHull (B : Set E) : Set E :=
  convexHull ℝ (balancedHull 𝕜 (insert 0 B))

open scoped ComplexOrder in
/-- The disk hull is Mathlib's absolute convex hull after adjoining zero. -/
theorem diskHull_eq_absConvexHull (B : Set E) :
    diskHull 𝕜 B = absConvexHull 𝕜 (insert 0 B) := by
  rw [absConvexHull_eq_convexHull_balancedHull, convexHull_RCLike_eq_real]
  rfl

variable {𝕜}

omit [IsScalarTower ℝ 𝕜 E] in
/-- A set is contained in its disk hull. -/
theorem subset_diskHull (B : Set E) : B ⊆ diskHull 𝕜 B :=
  (subset_insert 0 B).trans ((subset_balancedHull 𝕜).trans (subset_convexHull ℝ _))

omit [IsScalarTower ℝ 𝕜 E] in
/-- The disk hull contains zero. -/
theorem zero_mem_diskHull (B : Set E) : (0 : E) ∈ diskHull 𝕜 B :=
  subset_convexHull ℝ _ (subset_balancedHull 𝕜 (mem_insert 0 B))

omit [IsScalarTower ℝ 𝕜 E] in
/-- The disk hull is convex. -/
theorem convex_diskHull (B : Set E) : Convex ℝ (diskHull 𝕜 B) :=
  convex_convexHull ℝ _

/-- The disk hull is balanced. -/
theorem balanced_diskHull (B : Set E) : Balanced 𝕜 (diskHull 𝕜 B) :=
  (balancedHull.balanced _).convexHull_real

omit [IsScalarTower ℝ 𝕜 E] in
/-- The disk hull of a nonempty convex balanced set is the set itself. -/
theorem diskHull_eq_self {B : Set E} (hc : Convex ℝ B) (hb : Balanced 𝕜 B) (hne : B.Nonempty) :
    diskHull 𝕜 B = B := by
  have h0 : insert (0 : E) B = B := insert_eq_of_mem (hb.zero_mem hne)
  refine Subset.antisymm ?_ (subset_diskHull B)
  rw [diskHull, h0]
  exact convexHull_min (hb.balancedHull_subset_of_subset Subset.rfl) hc

/-- The disk hull of a bounded subset of a locally convex space is bounded. -/
theorem Bornology.IsVonNBounded.diskHull [TopologicalSpace E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] {B : Set E} (hB : IsVonNBounded 𝕜 B) :
    IsVonNBounded 𝕜 (diskHull 𝕜 B) :=
  (hB.insert 0).balancedHull.convexHull

variable (𝕜)

/-- The space `E_B` spanned by a set `B`, as a type synonym of the span of `B`. It carries the
gauge of the disk hull of `B` as a seminorm, not the topology of a subspace of `E`. -/
@[expose]
def DiskSpace (B : Set E) : Type _ :=
  ↥(Submodule.span 𝕜 B)

namespace DiskSpace

variable (B : Set E)

/-- The group structure of `E_B` is that of the span of `B`. -/
instance : AddCommGroup (DiskSpace 𝕜 B) :=
  inferInstanceAs (AddCommGroup ↥(Submodule.span 𝕜 B))

/-- The module structure of `E_B` is that of the span of `B`. -/
instance : Module 𝕜 (DiskSpace 𝕜 B) :=
  inferInstanceAs (Module 𝕜 ↥(Submodule.span 𝕜 B))

/-- The real module structure of `E_B` is that of the span of `B`. -/
instance : Module ℝ (DiskSpace 𝕜 B) :=
  inferInstanceAs (Module ℝ ↥(Submodule.span 𝕜 B))

/-- The real and the `𝕜`-module structures of `E_B` are compatible. -/
instance : IsScalarTower ℝ 𝕜 (DiskSpace 𝕜 B) :=
  inferInstanceAs (IsScalarTower ℝ 𝕜 ↥(Submodule.span 𝕜 B))

/-- The inclusion of `E_B` into `E`, as a linear map. -/
@[expose]
def incl : DiskSpace 𝕜 B →ₗ[𝕜] E :=
  (Submodule.span 𝕜 B).subtype

variable {𝕜 B}

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- The inclusion of `E_B` into `E` is injective. -/
theorem incl_injective : Function.Injective (incl 𝕜 B) :=
  Subtype.val_injective

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- The points of the span of `B` as points of `E_B`. -/
theorem exists_incl_eq {x : E} (hx : x ∈ Submodule.span 𝕜 B) :
    ∃ y : DiskSpace 𝕜 B, incl 𝕜 B y = x :=
  ⟨⟨x, hx⟩, rfl⟩

variable (𝕜 B)

/-- The unit disk of `E_B`: the points of `E_B` that lie in the disk hull of `B`. -/
@[expose]
def unitDisk : Set (DiskSpace 𝕜 B) :=
  incl 𝕜 B ⁻¹' diskHull 𝕜 B

/-- The unit disk of `E_B` is convex. -/
theorem convex_unitDisk : Convex ℝ (unitDisk 𝕜 B) :=
  (convex_diskHull B).is_linear_preimage ((incl 𝕜 B).restrictScalars ℝ).isLinear

/-- The unit disk of `E_B` is balanced. -/
theorem balanced_unitDisk : Balanced 𝕜 (unitDisk 𝕜 B) :=
  (balanced_diskHull B).preimage (incl 𝕜 B)

omit [IsScalarTower ℝ 𝕜 E] in
/-- The unit disk of `E_B` contains zero. -/
theorem zero_mem_unitDisk : (0 : DiskSpace 𝕜 B) ∈ unitDisk 𝕜 B := by
  change incl 𝕜 B 0 ∈ diskHull 𝕜 B
  rw [map_zero]
  exact zero_mem_diskHull B

/-- Every point of the span of `B` is a nonnegative real multiple of a point of the disk hull of
`B`. -/
theorem exists_smul_eq_of_mem_span {x : E} (hx : x ∈ Submodule.span 𝕜 B) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ h ∈ diskHull 𝕜 B, x = r • h := by
  induction hx using Submodule.span_induction with
  | mem b hb => exact ⟨1, zero_le_one, b, subset_diskHull B hb, (one_smul ℝ b).symm⟩
  | zero => exact ⟨0, le_rfl, 0, zero_mem_diskHull B, (zero_smul ℝ (0 : E)).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, h, hh, rfl⟩ := hx
    obtain ⟨s, hs, k, hk, rfl⟩ := hy
    rcases (add_nonneg hr hs).eq_or_lt with h0 | hpos
    · have hr0 : r = 0 := by linarith
      have hs0 : s = 0 := by linarith
      exact ⟨0, le_rfl, 0, zero_mem_diskHull B, by simp [hr0, hs0]⟩
    · refine ⟨r + s, hpos.le, (r / (r + s)) • h + (s / (r + s)) • k,
        convex_diskHull B hh hk (div_nonneg hr hpos.le) (div_nonneg hs hpos.le)
          (by rw [← add_div, div_self hpos.ne']), ?_⟩
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne']
  | smul c x _ hx =>
    obtain ⟨r, hr, h, hh, rfl⟩ := hx
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, le_rfl, 0, zero_mem_diskHull B, by rw [zero_smul, zero_smul]⟩
    · -- `c = ‖c‖ * u` with `‖u‖ = 1`.
      have hnorm : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
      refine ⟨‖c‖ * r, mul_nonneg hnorm.le hr, ((‖c‖ : 𝕜)⁻¹ * c) • h,
        balanced_diskHull B _ ?_ (smul_mem_smul_set hh), ?_⟩
      · rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hnorm, inv_mul_cancel₀ hnorm.ne']
      · rw [smul_comm c r h, mul_smul, smul_comm (‖c‖) r, ← algebraMap_smul 𝕜 ‖c‖,
          RCLike.algebraMap_eq_ofReal, smul_smul, ← mul_assoc,
          mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr hnorm.ne'), one_mul]

/-- The unit disk of `E_B` is absorbent. -/
theorem absorbent_unitDisk : Absorbent 𝕜 (unitDisk 𝕜 B) := by
  intro x
  obtain ⟨r, hr, h, hh, hxh⟩ := exists_smul_eq_of_mem_span 𝕜 B x.2
  refine absorbs_iff_norm.mpr ⟨max r 1, fun a ha ↦ singleton_subset_iff.mpr ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    linarith [le_max_right r 1]
  refine ⟨a⁻¹ • x, ?_, by simp only; rw [smul_inv_smul₀ ha0]⟩
  change incl 𝕜 B (a⁻¹ • x) ∈ diskHull 𝕜 B
  have hx' : incl 𝕜 B x = r • h := hxh
  rw [map_smul, hx', ← algebraMap_smul 𝕜 r h, RCLike.algebraMap_eq_ofReal, smul_smul]
  refine balanced_diskHull B _ ?_ (smul_mem_smul_set hh)
  rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hr]
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  rw [inv_mul_le_iff₀ hapos, mul_one]
  exact (le_max_left r 1).trans ha

/-- The gauge of the unit disk, as a seminorm on `E_B`. -/
@[expose]
noncomputable def seminorm : Seminorm 𝕜 (DiskSpace 𝕜 B) :=
  gaugeSeminorm (balanced_unitDisk 𝕜 B) (convex_unitDisk 𝕜 B)
    (absorbent_unitDisk 𝕜 B).restrictScalars_real

/-- `E_B` is seminormed by the gauge of its unit disk. -/
noncomputable instance : SeminormedAddCommGroup (DiskSpace 𝕜 B) :=
  (seminorm 𝕜 B).toAddGroupSeminorm.toSeminormedAddCommGroup

variable {𝕜 B}

/-- The norm of `E_B` is the gauge of its unit disk. -/
theorem norm_def (x : DiskSpace 𝕜 B) : ‖x‖ = gauge (unitDisk 𝕜 B) x :=
  rfl

/-- `E_B` is a (semi)normed space over `𝕜`. -/
noncomputable instance : NormedSpace 𝕜 (DiskSpace 𝕜 B) where
  norm_smul_le c x := (map_smul_eq_mul (seminorm 𝕜 B) c x).le

/-- `E_B` is a (semi)normed space over `ℝ`. -/
noncomputable instance : NormedSpace ℝ (DiskSpace 𝕜 B) where
  norm_smul_le c x := by
    rw [← algebraMap_smul 𝕜 c x, RCLike.algebraMap_eq_ofReal, norm_smul, RCLike.norm_ofReal,
      Real.norm_eq_abs]

/-- A point of `E_B` of norm less than one lies in the unit disk. -/
theorem mem_unitDisk_of_norm_lt_one {x : DiskSpace 𝕜 B} (hx : ‖x‖ < 1) : x ∈ unitDisk 𝕜 B :=
  setOfPred_gauge_lt_one_subset_self (convex_unitDisk 𝕜 B) (zero_mem_unitDisk 𝕜 B)
    (absorbent_unitDisk 𝕜 B).restrictScalars_real hx

/-- The points of the unit disk have norm at most one. -/
theorem norm_le_one_of_mem_unitDisk {x : DiskSpace 𝕜 B} (hx : x ∈ unitDisk 𝕜 B) : ‖x‖ ≤ 1 :=
  gauge_le_one_of_mem hx

/-- The unit disk of `E_B` is a neighbourhood of zero. -/
theorem unitDisk_mem_nhds_zero : unitDisk 𝕜 B ∈ 𝓝 (0 : DiskSpace 𝕜 B) :=
  mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun _ hx ↦
    mem_unitDisk_of_norm_lt_one (by simpa using hx)

/-- A point of `E_B` of norm less than `r` has its image in `r • diskHull 𝕜 B`. -/
theorem incl_mem_smul_diskHull {x : DiskSpace 𝕜 B} {r : ℝ} (hr : 0 < r) (hx : ‖x‖ < r) :
    incl 𝕜 B x ∈ r • diskHull 𝕜 B := by
  have h1 : ‖r⁻¹ • x‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_lt_iff₀ hr, mul_one]
    exact hx
  have h2 : incl 𝕜 B (r⁻¹ • x) ∈ diskHull 𝕜 B := mem_unitDisk_of_norm_lt_one h1
  refine ⟨incl 𝕜 B (r⁻¹ • x), h2, ?_⟩
  change r • incl 𝕜 B (r⁻¹ • x) = incl 𝕜 B x
  rw [LinearMap.map_smul_of_tower, smul_inv_smul₀ hr.ne']

/-- A point of `E_B` whose image lies in `r • diskHull 𝕜 B` has norm at most `r`. -/
theorem norm_le_of_incl_mem_smul_diskHull {x : DiskSpace 𝕜 B} {r : ℝ} (hr : 0 ≤ r)
    (hx : incl 𝕜 B x ∈ r • diskHull 𝕜 B) : ‖x‖ ≤ r := by
  refine gauge_le_of_mem hr ?_
  obtain ⟨h, hh, hhx⟩ := hx
  rcases hr.eq_or_lt with rfl | hpos
  · have hx0 : incl 𝕜 B x = 0 := by rw [← hhx]; exact zero_smul ℝ h
    have : x = 0 := incl_injective (by rw [hx0, map_zero])
    rw [this]
    exact ⟨0, zero_mem_unitDisk 𝕜 B, smul_zero _⟩
  · refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hpos.ne' x⟩
    change incl 𝕜 B (r⁻¹ • x) ∈ diskHull 𝕜 B
    have hhx' : r • h = incl 𝕜 B x := hhx
    rw [LinearMap.map_smul_of_tower, ← hhx', inv_smul_smul₀ hpos.ne']
    exact hh

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

omit [IsTopologicalAddGroup E] in
/-- For a bounded set `B`, every neighbourhood of zero in `E` contains the image of a ball of
`E_B`. -/
theorem exists_pos_forall_norm_lt_incl_mem (hB : IsVonNBounded 𝕜 B) {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : DiskSpace 𝕜 B, ‖x‖ < δ → incl 𝕜 B x ∈ U := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨R, hR⟩ := absorbs_iff_norm.mp ((hB.diskHull.restrict_scalars ℝ) hU)
  have hpos : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  refine ⟨(max R 1)⁻¹, inv_pos.mpr hpos, fun x hx ↦ ?_⟩
  obtain ⟨h, hh, hhx⟩ := incl_mem_smul_diskHull (inv_pos.mpr hpos) hx
  have hnorm : R ≤ ‖max R 1‖ := by
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact le_max_left R 1
  obtain ⟨u, hu, huh⟩ := hR (max R 1) hnorm hh
  have huh' : max R 1 • u = h := huh
  have hhx' : (max R 1)⁻¹ • h = incl 𝕜 B x := hhx
  rw [← hhx', ← huh', inv_smul_smul₀ hpos.ne']
  exact hu

/-- For a bounded subset `B` of a locally convex space the inclusion of `E_B` is continuous. -/
theorem continuous_incl (hB : IsVonNBounded 𝕜 B) : Continuous (incl 𝕜 B) := by
  refine continuous_of_continuousAt_zero (incl 𝕜 B) fun U hU ↦ ?_
  rw [map_zero] at hU
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_norm_lt_incl_mem hB hU
  exact mem_map.mpr (mem_of_superset (Metric.ball_mem_nhds 0 hδ) fun x hx ↦
    h x (by simpa using hx))

omit [IsTopologicalAddGroup E] in
/-- For a bounded subset `B` of a Hausdorff locally convex space the gauge on `E_B` is a norm. -/
theorem eq_zero_of_norm_eq_zero [T2Space E] (hB : IsVonNBounded 𝕜 B) {x : DiskSpace 𝕜 B}
    (hx : ‖x‖ = 0) : x = 0 := by
  refine incl_injective ?_
  rw [map_zero]
  by_contra hne
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_norm_lt_incl_mem hB (compl_singleton_mem_nhds
    (Ne.symm hne))
  exact h x (hx ▸ hδ) rfl

/-- The normed group structure of `E_B` for a bounded subset `B` of a Hausdorff locally convex
space. This is a definition and not an instance, because it depends on the boundedness of
`B`. -/
noncomputable abbrev normedAddCommGroup [T2Space E] (hB : IsVonNBounded 𝕜 B) :
    NormedAddCommGroup (DiskSpace 𝕜 B) :=
  NormedAddCommGroup.ofSeparation fun _ hx ↦ eq_zero_of_norm_eq_zero hB hx

end Topology

section Complete

variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [T2Space E]

/-- If a bounded disk `B` is complete as a subset of a Hausdorff locally convex space, in
particular if it is compact, then the space `E_B` is complete. -/
theorem completeSpace_of_isComplete (hc : Convex ℝ B) (hb : Balanced 𝕜 B) (hne : B.Nonempty)
    (hB : IsVonNBounded 𝕜 B) (hcomplete : IsComplete B) : CompleteSpace (DiskSpace 𝕜 B) := by
  have hhull : diskHull 𝕜 B = B := diskHull_eq_self hc hb hne
  have hclosed : IsClosed B := hcomplete.isClosed
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  refine Metric.complete_of_cauchySeq_tendsto fun x hx ↦ ?_
  -- Rescale the sequence into the unit disk.
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ n, ‖x n‖ < M := by
    obtain ⟨C, hC⟩ := hx.norm_bddAbove
    exact ⟨max C 0 + 1, by positivity, fun n ↦
      lt_of_le_of_lt ((hC (mem_range_self n)).trans (le_max_left C 0)) (lt_add_one _)⟩
  let u : ℕ → DiskSpace 𝕜 B := fun n ↦ M⁻¹ • x n
  have hu : CauchySeq u := hx.map (uniformContinuous_const_smul M⁻¹)
  have huB (n : ℕ) : incl 𝕜 B (u n) ∈ B := by
    have h1 : ‖u n‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos), inv_mul_lt_iff₀ hMpos,
        mul_one]
      exact hM n
    have h2 : incl 𝕜 B (u n) ∈ diskHull 𝕜 B := mem_unitDisk_of_norm_lt_one h1
    rwa [hhull] at h2
  -- The images converge in the complete set `B`.
  have hcauchy : CauchySeq fun n ↦ incl 𝕜 B (u n) :=
    hu.map (⟨incl 𝕜 B, continuous_incl hB⟩ : DiskSpace 𝕜 B →L[𝕜] E).uniformContinuous
  obtain ⟨z, hzB, hz⟩ := cauchySeq_tendsto_of_isComplete hcomplete huB hcauchy
  obtain ⟨z', hz'⟩ := exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span hzB)
  -- The sequence `u` converges to `z'` in the gauge.
  have hlim : Tendsto u atTop (𝓝 z') := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hmem : incl 𝕜 B (u n - z') ∈ (ε / 2) • B := by
      have hcl : IsClosed ((ε / 2) • B) := hclosed.smul₀ (ε / 2)
      have hlim' : Tendsto (fun m ↦ incl 𝕜 B (u n) - incl 𝕜 B (u m)) atTop
          (𝓝 (incl 𝕜 B (u n - z'))) := by
        rw [map_sub, hz']
        exact tendsto_const_nhds.sub hz
      refine hcl.mem_of_tendsto hlim' (eventually_atTop.mpr ⟨N, fun m hm ↦ ?_⟩)
      have hnm : ‖u n - u m‖ < ε / 2 := by
        have := hN n hn m hm
        rwa [dist_eq_norm] at this
      have h := incl_mem_smul_diskHull (half_pos hε) hnm
      rwa [map_sub, hhull] at h
    have hle : ‖u n - z'‖ ≤ ε / 2 :=
      norm_le_of_incl_mem_smul_diskHull (half_pos hε).le (hhull.symm ▸ hmem)
    rw [dist_eq_norm]
    linarith
  refine ⟨M • z', ?_⟩
  have h := hlim.const_smul M
  refine h.congr fun n ↦ ?_
  change M • M⁻¹ • x n = x n
  rw [smul_inv_smul₀ hMpos.ne']

end Complete

end DiskSpace

/-- If `B` spans the whole space then the disk hull of `B` is absorbent. -/
theorem absorbent_diskHull_of_span_eq_top (B : Set E) (h : Submodule.span 𝕜 B = ⊤) :
    Absorbent 𝕜 (diskHull 𝕜 B) := by
  intro x
  obtain ⟨r, hr, d, hd, hxd⟩ :=
    DiskSpace.exists_smul_eq_of_mem_span 𝕜 B (h ▸ Submodule.mem_top : x ∈ _)
  refine absorbs_iff_norm.mpr ⟨max r 1, fun a ha ↦ singleton_subset_iff.mpr ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    linarith [le_max_right r 1]
  refine ⟨a⁻¹ • x, ?_, by simp only; rw [smul_inv_smul₀ ha0]⟩
  rw [hxd, ← algebraMap_smul 𝕜 r d, RCLike.algebraMap_eq_ofReal, smul_smul]
  refine balanced_diskHull B _ ?_ (smul_mem_smul_set hd)
  rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hr]
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  rw [inv_mul_le_iff₀ hapos, mul_one]
  exact (le_max_left r 1).trans ha

/-- A subset `B` of a topological vector space is a **Banach disk** if it is convex, balanced and
bounded, and `DiskSpace 𝕜 B` is complete for the gauge of `diskHull 𝕜 B`. For a nonempty disk
this is the gauge of `B` itself. The empty set is allowed. Without Hausdorffness of the ambient
space the resulting complete space is only seminormed in general. -/
structure Bornology.IsBanachDisk (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] (B : Set E) : Prop where
  /-- A Banach disk is convex. -/
  convex : Convex ℝ B
  /-- A Banach disk is balanced. -/
  balanced : Balanced 𝕜 B
  /-- A Banach disk is bounded. -/
  isVonNBounded : IsVonNBounded 𝕜 B
  /-- The space spanned by a Banach disk is complete. -/
  completeSpace : CompleteSpace (DiskSpace 𝕜 B)

/-- A nonempty bounded disk that is complete as a subset of a Hausdorff locally convex space, in
particular a compact disk, is a Banach disk. -/
theorem Bornology.IsBanachDisk.of_isComplete {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E] {B : Set E} (hc : Convex ℝ B)
    (hb : Balanced 𝕜 B) (hne : B.Nonempty) (hB : IsVonNBounded 𝕜 B) (hcomplete : IsComplete B) :
    IsBanachDisk 𝕜 B :=
  ⟨hc, hb, hB, DiskSpace.completeSpace_of_isComplete hc hb hne hB hcomplete⟩

section Polar

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- The polar of the disk hull of a set is the polar of the set. -/
theorem StrongDual.polar_diskHull (S : Set E) :
    StrongDual.polar 𝕜 (diskHull 𝕜 S) = StrongDual.polar 𝕜 S := by
  rw [diskHull, StrongDual.polar_convexHull, StrongDual.polar_balancedHull]
  refine Subset.antisymm (LinearMap.polar_antitone _ (subset_insert 0 S)) fun φ hφ x hx ↦ ?_
  rcases hx with rfl | hx
  · change ‖φ 0‖ ≤ 1
    rw [map_zero, norm_zero]
    exact zero_le_one
  · exact hφ x hx

end Polar
