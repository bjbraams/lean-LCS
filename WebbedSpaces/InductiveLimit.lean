/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.DirectSum
public import LocallyConvexSpaces.FinalTopology
public import Mathlib.LinearAlgebra.DFinsupp
public import TopologicalVectorSpaces.LinearMapFiniteSum
public import WebbedSpaces.Product

/-!
# Countable locally convex hulls of webbed spaces

A space that is spanned by countably many images of webbed spaces under sequentially continuous
linear maps is webbed, and similarly for strictly webbed spaces. In particular the final locally
convex topology of a countable spanning family of webbed spaces is webbed; this covers countable
inductive limits, LF spaces and countable locally convex direct sums, [G. Köthe, *Topological Vector
Spaces II*][kothe1979], §35.4.(8) and (9).

The proof combines the two constructions of webs: the product `∀ i, E i` is webbed
(`Pi.instWebbedSpace`), and the space spanned by the images is the union over the finite sets
`s` of indices of the images of the maps `x ↦ ∑ i ∈ s, f i (x i)` defined on the product
(`WebbedSpace.of_iUnion_range`).

## Main statements

* `WebbedSpace.of_iSup_range`, `StrictlyWebbedSpace.of_iSup_range`.
* `locallyConvexFinalTopology.webbedSpace`, `locallyConvexFinalTopology.strictlyWebbedSpace`.
* `DirectSum.webbedSpace_locallyConvexTopology`,
  `DirectSum.strictlyWebbedSpace_locallyConvexTopology`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(8), (9)

## Tags

web, webbed space, inductive limit, direct sum, LF space
-/

public section

open Set Filter Function

open scoped Topology DirectSum


section Webbed

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Countable ι] {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

section

variable [TopologicalSpace F] [ContinuousAdd F]

/-- A space that is spanned by countably many images of webbed spaces under sequentially
continuous linear maps is webbed, Köthe II §35.4.(9). -/
theorem WebbedSpace.of_iSup_range [∀ i, WebbedSpace (E i)] (f : ∀ i, E i →ₗ[ℝ] F)
    (hf : ∀ i, SeqContinuous (f i)) (hspan : ⨆ i, LinearMap.range (f i) = ⊤) :
    WebbedSpace F :=
  WebbedSpace.of_iUnion_range (ι := Finset ι) (E := fun _ ↦ ∀ i, E i)
    (fun s ↦ LinearMap.finsetSumProj f s)
    (fun s ↦ LinearMap.seqContinuous_finsetSumProj hf s)
    (LinearMap.iUnion_range_finsetSumProj hspan)

/-- A space that is spanned by countably many images of strictly webbed spaces under
sequentially continuous linear maps is strictly webbed, Köthe II §35.4.(9). -/
theorem StrictlyWebbedSpace.of_iSup_range [∀ i, StrictlyWebbedSpace 𝕜 (E i)]
    (f : ∀ i, E i →ₗ[𝕜] F) (hf : ∀ i, SeqContinuous (f i))
    (hspan : ⨆ i, LinearMap.range (f i) = ⊤) : StrictlyWebbedSpace 𝕜 F :=
  StrictlyWebbedSpace.of_iUnion_range (ι := Finset ι) (E := fun _ ↦ ∀ i, E i)
    (fun s ↦ LinearMap.finsetSumProj f s)
    (fun s ↦ LinearMap.seqContinuous_finsetSumProj hf s)
    (LinearMap.iUnion_range_finsetSumProj hspan)

end

/-- The final locally convex topology of a countable spanning family of webbed spaces is
webbed. In particular countable inductive limits of webbed spaces, such as LF spaces, are
webbed, Köthe II §35.4.(8), (9). -/
theorem locallyConvexFinalTopology.webbedSpace [∀ i, WebbedSpace (E i)]
    (f : ∀ i, E i →ₗ[𝕜] F) (hspan : ⨆ i, LinearMap.range (f i) = ⊤) :
    @WebbedSpace F _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  refine WebbedSpace.of_iSup_range (fun i ↦ (f i).restrictScalars ℝ)
    (fun i ↦ (locallyConvexFinalTopology.continuous_apply f i).seqContinuous) ?_
  -- The real span of the ranges is everything, because the span over `𝕜` is.
  refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
  have hy : y ∈ ⨆ i, LinearMap.range (f i) := hspan ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem i y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  | zero => exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => exact add_mem h₁ h₂

/-- The final locally convex topology of a countable spanning family of strictly webbed spaces
is strictly webbed. -/
theorem locallyConvexFinalTopology.strictlyWebbedSpace [∀ i, StrictlyWebbedSpace 𝕜 (E i)]
    (f : ∀ i, E i →ₗ[𝕜] F) (hspan : ⨆ i, LinearMap.range (f i) = ⊤) :
    @StrictlyWebbedSpace 𝕜 F _ _ _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  exact StrictlyWebbedSpace.of_iSup_range f
    (fun i ↦ (locallyConvexFinalTopology.continuous_apply f i).seqContinuous) hspan

end Webbed

namespace DirectSum

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Countable ι] [DecidableEq ι] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)]

/-- A countable locally convex direct sum of webbed spaces is webbed. -/
theorem webbedSpace_locallyConvexTopology [∀ i, WebbedSpace (E i)] :
    @WebbedSpace (⨁ i, E i) _ _ (locallyConvexTopology 𝕜 E) :=
  locallyConvexFinalTopology.webbedSpace (lof 𝕜 ι E) DFinsupp.iSup_range_lsingle

/-- A countable locally convex direct sum of strictly webbed spaces is strictly webbed. -/
theorem strictlyWebbedSpace_locallyConvexTopology [∀ i, StrictlyWebbedSpace 𝕜 (E i)] :
    @StrictlyWebbedSpace 𝕜 (⨁ i, E i) _ _ _ _ (locallyConvexTopology 𝕜 E) :=
  locallyConvexFinalTopology.strictlyWebbedSpace (lof 𝕜 ι E) DFinsupp.iSup_range_lsingle

end DirectSum
