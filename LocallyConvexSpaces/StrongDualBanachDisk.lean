/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.BanachDisk
public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.StrongDualBounded
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Polars of neighbourhoods are Banach disks in the strong dual

Let `U` be a neighbourhood of zero in a topological vector space `E`. The polar `U°` is convex,
balanced and bounded in the strong dual, and the space that it spans is complete for the gauge
of `U°`. Hence `U°` is a Banach disk in the strong dual. The proof uses compactness of the
polar in the weak-* topology; no seminorm property of the gauge of the arbitrary set `U` is
assumed.

Completeness is a statement about the gauge of `U°` only, so it can be proved with the weak-*
topology as the ambient topology, in which `U°` is compact by the Alaoglu–Bourbaki theorem, and
then used for the strong topology.

## Main statements

* `StrongDual.completeSpace_diskSpace_polar`
* `StrongDual.isBanachDisk_polar_of_mem_nhds`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(13), and
  [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.4

## Tags

Banach disk, polar, strong dual, equicontinuous set
-/

public section

open Set Bornology

open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- The space spanned by the polar of a neighbourhood of zero, in the weak-* dual, is complete
for the gauge of the polar. -/
private theorem WeakDual.completeSpace_diskSpace_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    CompleteSpace (DiskSpace 𝕜 (WeakDual.polar 𝕜 U)) := by
  have hc : IsCompact (WeakDual.polar 𝕜 U) := WeakDual.isCompact_polar_of_mem_nhds hU
  let _ : UniformSpace (WeakDual 𝕜 E) := IsTopologicalAddGroup.rightUniformSpace (WeakDual 𝕜 E)
  have : IsUniformAddGroup (WeakDual 𝕜 E) := isUniformAddGroup_of_addCommGroup
  have : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  -- Convexity and balancedness are proved on the strong dual and restated.
  have hconv' : Convex ℝ (StrongDual.polar 𝕜 U) := LinearMap.convex_polar _ _
  have hbal' : Balanced 𝕜 (StrongDual.polar 𝕜 U) := LinearMap.balanced_polar _ _
  have hconv : Convex ℝ (WeakDual.polar 𝕜 U) := hconv'
  have hbal : Balanced 𝕜 (WeakDual.polar 𝕜 U) := hbal'
  exact DiskSpace.completeSpace_of_isComplete hconv hbal ⟨0, StrongDual.zero_mem_polar 𝕜 U⟩
    (hc.isVonNBounded 𝕜) hc.isComplete

/-- The space spanned by the polar of a neighbourhood of zero is complete for the gauge of the
polar. -/
theorem StrongDual.completeSpace_diskSpace_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    CompleteSpace (DiskSpace 𝕜 (StrongDual.polar 𝕜 U)) :=
  WeakDual.completeSpace_diskSpace_polar hU

/-- **The polar of a neighbourhood of zero is a Banach disk in the strong dual.** -/
theorem StrongDual.isBanachDisk_polar_of_mem_nhds {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsBanachDisk 𝕜 (StrongDual.polar 𝕜 U) :=
  ⟨LinearMap.convex_polar _ _, LinearMap.balanced_polar _ _,
    StrongDual.isVonNBounded_polar_of_mem_nhds hU, StrongDual.completeSpace_diskSpace_polar hU⟩
