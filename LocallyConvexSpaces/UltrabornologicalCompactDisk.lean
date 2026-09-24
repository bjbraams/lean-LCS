/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.CompactHull
public import LocallyConvexSpaces.PairingTopology
public import LocallyConvexSpaces.UltrabornologicalBanachDisk

/-!
# Ultrabornological spaces and compact disks

A Hausdorff locally convex space is ultrabornological if and only if it is the locally convex
hull of the Banach spaces `E_K`, where `K` runs through the compact disks of `E`
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7.(2)). Consequently a linear map
from an ultrabornological space into a locally convex space is continuous as soon as it is
bounded on every compact disk (§35.7.(5) b) for linear functionals).

The point is that a sequence that tends to zero in the Banach space `E_B` of a Banach disk `B`
lies in a compact disk of `E_B`, whose image in `E` is a compact disk. Hence a `ℝ`-convex balanced
set that absorbs the compact disks absorbs, in every `E_B`, the sequences that tend to zero, so
that its trace on `E_B` is a neighbourhood of zero.

## Main definitions

* `Bornology.compactDisks 𝕜 E`: the nonempty compact disks of `E`.

## Main statements

* `Bornology.IsBanachDisk.of_isCompact`: a nonempty compact disk of a Hausdorff locally convex
  space is a Banach disk.
* `Bornology.IsBanachDisk.exists_mem_compactDisks_of_tendsto_zero`
* `UltrabornologicalSpace.eq_locallyConvexFinalTopology_compactDisks`,
  `UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_compactDisks`: Köthe II §35.7.(2).
* `LinearMap.continuous_of_forall_isVonNBounded_image_compactDisk`: Köthe II §35.7.(5) b).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7

## Tags

ultrabornological space, Banach disk, compact disk
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

universe u v

variable (𝕜 : Type v) (E : Type u) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- The nonempty compact disks of a topological vector space. -/
@[expose]
def Bornology.compactDisks [TopologicalSpace E] : Set (Set E) :=
  {K | IsCompact K ∧ Convex ℝ K ∧ Balanced 𝕜 K ∧ K.Nonempty}

variable {𝕜 E}

/-- A nonempty compact disk of a Hausdorff locally convex space is a Banach disk. -/
theorem Bornology.IsBanachDisk.of_isCompact [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hK : IsCompact K)
    (hc : Convex ℝ K) (hb : Balanced 𝕜 K) (hne : K.Nonempty) : IsBanachDisk 𝕜 K :=
  IsBanachDisk.of_isComplete hc hb hne (hK.isVonNBounded 𝕜) hK.isComplete

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A sequence that tends to zero in the Banach space `E_B` of a Banach disk `B` lies in a
compact disk of `E`. -/
theorem Bornology.IsBanachDisk.exists_mem_compactDisks_of_tendsto_zero {B : Set E}
    (hB : IsBanachDisk 𝕜 B) {y : ℕ → DiskSpace 𝕜 B} (hy : Tendsto y atTop (𝓝 0)) :
    ∃ K ∈ compactDisks 𝕜 E, ∀ n, DiskSpace.incl 𝕜 B (y n) ∈ K := by
  have := hB.completeSpace
  obtain ⟨K', hyK', hK'c, hK'conv, hK'bal, hK'0⟩ :=
    (hy.isCompact_insert_range).exists_isCompact_convex_balanced_superset (𝕜 := 𝕜)
  refine ⟨DiskSpace.incl 𝕜 B '' K',
    ⟨hK'c.image (DiskSpace.continuous_incl hB.isVonNBounded),
      hK'conv.is_linear_image ((DiskSpace.incl 𝕜 B).restrictScalars ℝ).isLinear,
      hK'bal.image (DiskSpace.incl 𝕜 B), ⟨_, 0, hK'0, rfl⟩⟩,
    fun n ↦ ⟨y n, hyK' (mem_insert_of_mem _ (mem_range_self n)), rfl⟩⟩

/-- **An ultrabornological space is the locally convex hull of the spaces `E_K` spanned by its
compact disks**, Köthe II §35.7.(2). -/
theorem UltrabornologicalSpace.eq_locallyConvexFinalTopology_compactDisks
    [UltrabornologicalSpace 𝕜 E] :
    (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1 := by
  have heq := UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks (𝕜 := 𝕜) (E := E)
  let gB := fun B : banachDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  let gK := fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
  refine le_antisymm ?_ ((locallyConvexFinalTopology.le_iff gK).mpr fun K ↦
    DiskSpace.continuous_incl (K.2.1.isVonNBounded 𝕜))
  -- A convex balanced neighbourhood of zero for the hull topology absorbs the compact disks.
  refine IsTopologicalAddGroup.le_of_nhds_zero_le inferInstance
    (locallyConvexFinalTopology.isTopologicalAddGroup gK) fun U hU ↦ ?_
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ :=
    (@nhds_zero_hasBasis_convex_balanced 𝕜 E _ _ _ _ _ (locallyConvexFinalTopology gK)
      (locallyConvexFinalTopology.continuousSMul gK)
      (locallyConvexFinalTopology.locallyConvexSpace gK)).mem_iff.mp hU
  have habs : Absorbent 𝕜 W :=
    @absorbent_nhds_zero 𝕜 E _ _ _ W (locallyConvexFinalTopology gK)
      (locallyConvexFinalTopology.continuousSMul gK) hW
  have hW' := locallyConvexFinalTopology.mem_nhds_zero gB hWc hWb habs fun B ↦ ?_
  · rw [← heq] at hW'
    exact mem_of_superset hW' hWU
  -- In `E_B` the trace of `W` absorbs the sequences that tend to zero.
  refine mem_nhds_zero_of_forall_absorbs_range (𝕜 := 𝕜) fun y hy ↦ ?_
  obtain ⟨K, hK, hyK⟩ := B.2.exists_mem_compactDisks_of_tendsto_zero hy
  have hpre : DiskSpace.incl 𝕜 K ⁻¹' W ∈ 𝓝 (0 : DiskSpace 𝕜 K) :=
    locallyConvexFinalTopology.preimage_mem_nhds_zero gK ⟨K, hK⟩ hW
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (DiskSpace.absorbs_of_preimage_incl_mem_nhds hpre)
  refine absorbs_iff_norm.mpr ⟨max r 1, fun a ha ↦ ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    exact absurd ((le_max_right r 1).trans ha) (by norm_num)
  rintro _ ⟨n, rfl⟩
  obtain ⟨w, hw, hwa⟩ := hr a ((le_max_left r 1).trans ha) (hyK n)
  have hwa' : a • w = DiskSpace.incl 𝕜 B.1 (y n) := hwa
  refine ⟨a⁻¹ • y n, ?_, smul_inv_smul₀ ha0 _⟩
  change DiskSpace.incl 𝕜 B.1 (a⁻¹ • y n) ∈ W
  rw [map_smul, ← hwa', inv_smul_smul₀ ha0]
  exact hw

/-- **A linear map from an ultrabornological space into a locally convex space that is bounded
on every compact disk is continuous**; for linear functionals this is Köthe II §35.7.(5) b). -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image_compactDisk
    [UltrabornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] (A : E →ₗ[𝕜] F)
    (hA : ∀ K ∈ compactDisks 𝕜 E, IsVonNBounded 𝕜 (A '' K)) : Continuous A := by
  have heq := UltrabornologicalSpace.eq_locallyConvexFinalTopology_compactDisks (𝕜 := 𝕜) (E := E)
  let g := fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
  have h : @Continuous E F (locallyConvexFinalTopology g) _ A :=
    (locallyConvexFinalTopology.continuous_iff g A).mpr fun K ↦
      DiskSpace.continuous_comp_incl_of_isVonNBounded_image K.2.2.1 K.2.2.2.1 K.2.2.2.2 A
        (hA K.1 K.2)
  rwa [← heq] at h

end Topology

/-- **A Hausdorff space that is the locally convex hull of the Banach spaces spanned by its
compact disks is ultrabornological**, Köthe II §35.7.(2). -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_compactDisks [UniformSpace E]
    [IsUniformAddGroup E] [T2Space E]
    (h : (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1) :
    UltrabornologicalSpace 𝕜 E := by
  have : ContinuousSMul 𝕜 E := by
    have h1 := locallyConvexFinalTopology.continuousSMul
      fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
    rwa [← h] at h1
  have : LocallyConvexSpace ℝ E := by
    have h1 := locallyConvexFinalTopology.locallyConvexSpace
      fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
    rwa [← h] at h1
  exact UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_diskSpace
    (fun K hK ↦ IsBanachDisk.of_isCompact hK.1 hK.2.1 hK.2.2.1 hK.2.2.2) h
