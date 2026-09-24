/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.BanachDisk
public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.PairingTopology

/-!
# Quasi-complete bornological spaces are ultrabornological

A Hausdorff bornological locally convex space carries the final locally convex topology of the
normed spaces `E_B` spanned by its closed bounded disks `B`. If the space is quasi-complete,
these disks are complete, the spaces `E_B` are Banach spaces, and the space is therefore
ultrabornological.

## Main statements

* `BornologicalSpace.eq_locallyConvexFinalTopology_diskSpace`: the topology of a bornological
  locally convex space is the final locally convex topology of the spaces `E_B`, for the closed
  bounded disks `B`.
* `UltrabornologicalSpace.of_bornologicalSpace_of_quasiCompleteSpace`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §2, III §6 Exercise
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §8.4
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §28.3

## Tags

bornological space, ultrabornological space, Banach disk, quasi-complete
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

universe u v

variable (𝕜 : Type v) (E : Type u) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- The closed, bounded, nonempty disks of a topological vector space. -/
@[expose]
def Bornology.closedBoundedDisks [TopologicalSpace E] : Set (Set E) :=
  {B | IsClosed B ∧ Convex ℝ B ∧ Balanced 𝕜 B ∧ IsVonNBounded 𝕜 B ∧ B.Nonempty}

variable {𝕜 E}

/-- Every bounded subset of a locally convex space lies in a closed bounded disk. -/
theorem Bornology.exists_mem_closedBoundedDisks_of_isVonNBounded [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    {S : Set E} (hS : IsVonNBounded 𝕜 S) : ∃ B ∈ closedBoundedDisks 𝕜 E, S ⊆ B := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  refine ⟨closure (diskHull 𝕜 S), ⟨isClosed_closure, (convex_diskHull S).closure,
    (balanced_diskHull S).closure, hS.diskHull.closure, ⟨0, subset_closure (zero_mem_diskHull S)⟩⟩,
    (subset_diskHull S).trans subset_closure⟩

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [T2Space E]

/-- The topology of a Hausdorff bornological locally convex space is the final locally convex
topology of the normed spaces `E_B` spanned by its closed bounded disks `B`. -/
theorem BornologicalSpace.eq_locallyConvexFinalTopology_diskSpace [BornologicalSpace 𝕜 E] :
    (inferInstance : TopologicalSpace E) =
      locallyConvexFinalTopology fun B : closedBoundedDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1 := by
  let f := fun B : closedBoundedDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  refine le_antisymm ?_ ?_
  · -- Every neighbourhood of zero for the final topology is bornivorous.
    refine IsTopologicalAddGroup.le_of_nhds_zero_le inferInstance
      (locallyConvexFinalTopology.isTopologicalAddGroup f) fun U hU ↦ ?_
    obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ :=
      (@nhds_zero_hasBasis_convex_balanced 𝕜 E _ _ _ _ _ (locallyConvexFinalTopology f)
        (locallyConvexFinalTopology.continuousSMul f)
        (locallyConvexFinalTopology.locallyConvexSpace f)).mem_iff.mp hU
    refine mem_of_superset (BornologicalSpace.mem_nhds_zero W hWc hWb fun S hS ↦ ?_) hWU
    obtain ⟨B, hB, hSB⟩ := exists_mem_closedBoundedDisks_of_isVonNBounded hS
    -- The preimage of `W` in `E_B` contains a ball.
    have hpre : DiskSpace.incl 𝕜 B ⁻¹' W ∈ 𝓝 (0 : DiskSpace 𝕜 B) :=
      locallyConvexFinalTopology.preimage_mem_nhds_zero f ⟨B, hB⟩ hW
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hBhull : diskHull 𝕜 B = B := diskHull_eq_self hB.2.1 hB.2.2.1 hB.2.2.2.2
    refine absorbs_iff_norm.mpr ⟨(δ / 2)⁻¹, fun a ha s hs ↦ ?_⟩
    have hδ2 : 0 < δ / 2 := half_pos hδ
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [norm_zero] at ha
      exact absurd ha (not_le.mpr (inv_pos.mpr hδ2))
    obtain ⟨s', hs'⟩ := DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span (hSB hs))
    have hnorm : ‖s'‖ ≤ 1 :=
      DiskSpace.norm_le_one_of_mem_unitDisk (by
        change DiskSpace.incl 𝕜 B s' ∈ diskHull 𝕜 B
        rw [hs', hBhull]
        exact hSB hs)
    have hlt : ‖a⁻¹ • s'‖ < δ := by
      rw [norm_smul, norm_inv]
      have h1 : ‖a‖⁻¹ ≤ δ / 2 := by
        rw [inv_le_comm₀ (norm_pos_iff.mpr ha0) hδ2]
        exact ha
      calc ‖a‖⁻¹ * ‖s'‖ ≤ δ / 2 * 1 :=
            mul_le_mul h1 hnorm (norm_nonneg _) hδ2.le
        _ < δ := by linarith
    have hmem : DiskSpace.incl 𝕜 B (a⁻¹ • s') ∈ W :=
      hball (by simpa [dist_eq_norm] using hlt)
    rw [map_smul, hs'] at hmem
    exact ⟨a⁻¹ • s, hmem, smul_inv_smul₀ ha0 s⟩
  · exact (locallyConvexFinalTopology.le_iff f).mpr fun B ↦ DiskSpace.continuous_incl B.2.2.2.2.1

/-- **A quasi-complete Hausdorff bornological locally convex space is ultrabornological.** In
such a space the closed bounded disks are Banach disks. -/
theorem UltrabornologicalSpace.of_bornologicalSpace_of_quasiCompleteSpace
    {𝕜 : Type v} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] [T2Space E] [BornologicalSpace 𝕜 E] [QuasiCompleteSpace 𝕜 E] :
    UltrabornologicalSpace 𝕜 E := by
  have heq := BornologicalSpace.eq_locallyConvexFinalTopology_diskSpace (𝕜 := 𝕜) (E := E)
  -- Every `E_B` is a Banach space, hence ultrabornological.
  have hX (B : closedBoundedDisks 𝕜 E) : UltrabornologicalSpace 𝕜 (DiskSpace 𝕜 B.1) := by
    obtain ⟨hcl, hc, hb, hbdd, hne⟩ := B.2
    let _ := DiskSpace.normedAddCommGroup (𝕜 := 𝕜) hbdd
    have : CompleteSpace (DiskSpace 𝕜 B.1) :=
      DiskSpace.completeSpace_of_isComplete hc hb hne hbdd
        (QuasiCompleteSpace.quasiComplete hbdd hcl)
    infer_instance
  have key := locallyConvexFinalTopology.ultrabornologicalSpace (𝕜 := 𝕜)
    fun B : closedBoundedDisks 𝕜 E ↦ DiskSpace.incl 𝕜 B.1
  rwa [← heq] at key
