/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.FinalTopology
public import Mathlib.LinearAlgebra.LinearPMap
public import TopologicalVectorSpaces.LinearMapGraph
public import WebbedSpaces.DeWilde.Relation

/-!
# De Wilde's open mapping theorem

A linear map with sequentially closed graph from a webbed locally convex space onto an
ultrabornological space is open. The same holds for a map onto a non-meagre subspace of a
first-countable topological vector space, which is then the whole space; and, if the graph is
closed, for a map onto a non-meagre subspace of any topological vector space and for a map onto
a locally convex hull of Baire spaces. The map may be defined on a subspace of the webbed
space only (`LinearPMap`). These are the statements of
[G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.3.(1)–(6).

All of them are obtained from De Wilde's theorem for linear relations in
`WebbedSpaces.DeWilde.Relation`, applied to the graph of the map. No quotient by the
kernel of the map is needed.

## Main statements

For a partially defined map `A : F →ₗ.[𝕜] E` on a webbed locally convex space `F`:

* `LinearPMap.isOpenMap_of_isSeqClosed_graph_of_firstCountable`,
  `LinearPMap.range_eq_top_of_isSeqClosed_graph_of_firstCountable`: §35.3.(4).
* `LinearPMap.isOpenMap_of_isClosed_graph`, `LinearPMap.range_eq_top_of_isClosed_graph`:
  §35.3.(2).
* `LinearPMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace`: §35.3.(6).

For a map `A : F →ₗ[𝕜] E` defined on all of `F`:

* `LinearMap.isOpenMap_of_isSeqClosed_graph_of_webbedSpace`: **De Wilde's open mapping
  theorem**, §35.3.(5), and its consequence `ContinuousLinearMap.isOpenMap_of_webbedSpace`,
  §35.3.(1).
* `LinearMap.isOpenMap_of_isSeqClosed_graph_of_firstCountable`,
  `LinearMap.isOpenMap_of_isClosed_graph_of_not_isMeagre`, and the versions
  `ContinuousLinearMap.isOpenMap_of_webbedSpace_of_firstCountable`,
  `ContinuousLinearMap.isOpenMap_of_webbedSpace_of_baireSpace` for continuous maps onto
  Hausdorff Baire spaces.
* `LinearMap.isOpenMap_of_isClosed_graph_of_locallyConvexFinalTopology`: a map onto a locally convex
  hull of Baire spaces, §35.3.(3).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.3

## Tags

open mapping theorem, De Wilde, webbed space, ultrabornological space
-/

public section

open Set Filter Function

open scoped Topology

universe u v


section OpenMapping

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

omit [WebbedSpace F] [LocallyConvexSpace ℝ F] [ContinuousSMul 𝕜 F] [IsTopologicalAddGroup F]
  [IsScalarTower ℝ 𝕜 F] [Module ℝ F] in
/-- A subspace that contains a neighbourhood of zero is the whole space. -/
private theorem eq_top_of_mem_nhds_zero {S : Submodule 𝕜 E} {U : Set E} (hU : U ∈ 𝓝 (0 : E))
    (hUS : U ⊆ S) : S = ⊤ := by
  have htop : S.restrictScalars ℝ = ⊤ :=
    (S.restrictScalars ℝ).eq_top_of_nonempty_interior'
      ⟨0, mem_interior_iff_mem_nhds.mpr (mem_of_superset hU hUS)⟩
  exact (Submodule.restrictScalars_eq_top_iff ℝ 𝕜 E).mp htop

/-- A partially defined linear map with sequentially closed graph from a webbed locally convex
space onto a non-meagre subspace of a first-countable topological vector space is open,
Köthe II §35.3.(4). -/
theorem LinearPMap.isOpenMap_of_isSeqClosed_graph_of_firstCountable [FirstCountableTopology E]
    (A : F →ₗ.[𝕜] E) (hA : IsSeqClosed (A.graph : Set (F × E)))
    (hne : ¬IsMeagre (Set.range A)) : IsOpenMap A :=
  A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_isSeqClosed hA (by rwa [A.snd_image_graph]) hV

/-- A partially defined linear map with sequentially closed graph from a webbed locally convex
space onto a non-meagre subspace of a first-countable topological vector space is surjective,
Köthe II §35.3.(4). -/
theorem LinearPMap.range_eq_top_of_isSeqClosed_graph_of_firstCountable
    [FirstCountableTopology E] (A : F →ₗ.[𝕜] E) (hA : IsSeqClosed (A.graph : Set (F × E)))
    (hne : ¬IsMeagre (Set.range A)) : LinearMap.range A.toFun = ⊤ := by
  have h := A.graph.image_mem_nhds_zero_of_isSeqClosed hA (by rwa [A.snd_image_graph])
    (univ_mem : (univ : Set F) ∈ 𝓝 (0 : F))
  rw [A.image_graph] at h
  exact eq_top_of_mem_nhds_zero h (image_subset_range _ _)

/-- A partially defined linear map with closed graph from a webbed locally convex space onto a
non-meagre subspace of a topological vector space is open, Köthe II §35.3.(2). -/
theorem LinearPMap.isOpenMap_of_isClosed_graph (A : F →ₗ.[𝕜] E)
    (hA : IsClosed (A.graph : Set (F × E))) (hne : ¬IsMeagre (Set.range A)) : IsOpenMap A :=
  A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_isClosed hA (by rwa [A.snd_image_graph]) hV

/-- A partially defined linear map with closed graph from a webbed locally convex space onto a
non-meagre subspace of a topological vector space is surjective, Köthe II §35.3.(2). -/
theorem LinearPMap.range_eq_top_of_isClosed_graph (A : F →ₗ.[𝕜] E)
    (hA : IsClosed (A.graph : Set (F × E))) (hne : ¬IsMeagre (Set.range A)) :
    LinearMap.range A.toFun = ⊤ := by
  have h := A.graph.image_mem_nhds_zero_of_isClosed hA (by rwa [A.snd_image_graph])
    (univ_mem : (univ : Set F) ∈ 𝓝 (0 : F))
  rw [A.image_graph] at h
  exact eq_top_of_mem_nhds_zero h (image_subset_range _ _)

/-- A linear map with sequentially closed graph from a webbed locally convex space onto a
non-meagre subspace of a first-countable topological vector space is open. -/
theorem LinearMap.isOpenMap_of_isSeqClosed_graph_of_firstCountable [FirstCountableTopology E]
    (A : F →ₗ[𝕜] E) (hA : IsSeqClosed (A.graph : Set (F × E))) (hne : ¬IsMeagre (Set.range A)) :
    IsOpenMap A :=
  A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_isSeqClosed hA (by rwa [A.snd_image_graph]) hV

/-- A linear map with closed graph from a webbed locally convex space onto a non-meagre subspace
of a topological vector space is open. -/
theorem LinearMap.isOpenMap_of_isClosed_graph_of_not_isMeagre (A : F →ₗ[𝕜] E)
    (hA : IsClosed (A.graph : Set (F × E))) (hne : ¬IsMeagre (Set.range A)) : IsOpenMap A :=
  A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_isClosed hA (by rwa [A.snd_image_graph]) hV

/-- A continuous linear map from a webbed locally convex space onto a Hausdorff first-countable
Baire topological vector space is open. -/
theorem ContinuousLinearMap.isOpenMap_of_webbedSpace_of_firstCountable [BaireSpace E]
    [FirstCountableTopology E] [T2Space E] (A : F →L[𝕜] E) (hsurj : Surjective A) :
    IsOpenMap A := by
  have : Nonempty E := ⟨0⟩
  refine A.toLinearMap.isOpenMap_of_isSeqClosed_graph_of_firstCountable
    A.isClosed_graph.isSeqClosed ?_
  have hr : Set.range A.toLinearMap = univ := hsurj.range_eq
  rw [hr]
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

/-- A continuous linear map from a webbed locally convex space onto a Hausdorff Baire
topological vector space is open. -/
theorem ContinuousLinearMap.isOpenMap_of_webbedSpace_of_baireSpace [BaireSpace E] [T2Space E]
    (A : F →L[𝕜] E) (hsurj : Surjective A) : IsOpenMap A := by
  have : Nonempty E := ⟨0⟩
  refine A.toLinearMap.isOpenMap_of_isClosed_graph_of_not_isMeagre A.isClosed_graph ?_
  have hr : Set.range A.toLinearMap = univ := hsurj.range_eq
  rw [hr]
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

end OpenMapping

section Hull

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {X : ι → Type*} {E F : Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)] [∀ i, Module ℝ (X i)]
  [∀ i, IsScalarTower ℝ 𝕜 (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, IsTopologicalAddGroup (X i)] [∀ i, ContinuousSMul 𝕜 (X i)] [∀ i, BaireSpace (X i)]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- A linear map from a webbed locally convex space onto a locally convex hull of Baire
topological vector spaces is open, if its graph is closed, Köthe II §35.3.(3). It suffices that
the pullbacks `{(x, e) | A x = f i e}` of the graph to the spaces `F × X i` are closed. -/
theorem LinearMap.isOpenMap_of_isClosed_graph_of_locallyConvexFinalTopology (f : ∀ i, X i →ₗ[𝕜] E)
    (A : F →ₗ[𝕜] E) (hsurj : Surjective A)
    (hA : ∀ i, IsClosed {q : F × X i | A q.1 = f i q.2}) :
    @IsOpenMap F E _ (locallyConvexFinalTopology f) A := by
  let _ : TopologicalSpace E := locallyConvexFinalTopology f
  have : IsTopologicalAddGroup E := locallyConvexFinalTopology.isTopologicalAddGroup f
  refine A.isOpenMap_of_forall_image_graph fun V hV ↦ ?_
  refine Submodule.image_mem_nhds_zero_of_locallyConvexFinalTopology f A.graph ?_
    (fun i V hV ↦ ?_) hV
  · rw [A.snd_image_graph, hsurj.range_eq]
  · have : ContinuousSMul ℝ (X i) := IsScalarTower.continuousSMul 𝕜
    have : Nonempty (X i) := ⟨0⟩
    have hset : ((A.graph.comap (LinearMap.prodMap LinearMap.id (f i)) :
        Submodule 𝕜 (F × X i)) : Set (F × X i)) = {q : F × X i | A q.1 = f i q.2} := by
      ext q
      exact (LinearMap.mem_graph_iff _ _).trans eq_comm
    refine Submodule.image_mem_nhds_zero_of_isClosed _ (hset ▸ hA i) ?_ hV
    have huniv : Prod.snd '' ((A.graph.comap (LinearMap.prodMap LinearMap.id (f i)) :
        Submodule 𝕜 (F × X i)) : Set (F × X i)) = univ := by
      refine eq_univ_of_forall fun e ↦ ?_
      obtain ⟨x, hx⟩ := hsurj (f i e)
      exact ⟨(x, e), hset ▸ hx, rfl⟩
    rw [huniv]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

end Hull

section Ultrabornological

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type u} {F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [UltrabornologicalSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- A partially defined linear map with sequentially closed graph from a webbed locally convex
space onto an ultrabornological space is open, Köthe II §35.3.(6). -/
theorem LinearPMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace (A : F →ₗ.[𝕜] E)
    (hA : IsSeqClosed (A.graph : Set (F × E))) (hsurj : Surjective A) : IsOpenMap A := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  exact A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_ultrabornologicalSpace hA
      (by rw [A.snd_image_graph, hsurj.range_eq]) hV

/-- **De Wilde's open mapping theorem**: a linear map with sequentially closed graph from a
webbed locally convex space onto an ultrabornological space is open, Köthe II §35.3.(5). -/
theorem LinearMap.isOpenMap_of_isSeqClosed_graph_of_webbedSpace (A : F →ₗ[𝕜] E)
    (hA : IsSeqClosed (A.graph : Set (F × E))) (hsurj : Surjective A) : IsOpenMap A := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  exact A.isOpenMap_of_forall_image_graph fun _ hV ↦
    A.graph.image_mem_nhds_zero_of_ultrabornologicalSpace hA
      (by rw [A.snd_image_graph, hsurj.range_eq]) hV

/-- A continuous linear map from a webbed locally convex space onto a Hausdorff ultrabornological
space is open, Köthe II §35.3.(1). -/
theorem ContinuousLinearMap.isOpenMap_of_webbedSpace [T2Space E] (A : F →L[𝕜] E)
    (hsurj : Surjective A) : IsOpenMap A :=
  A.toLinearMap.isOpenMap_of_isSeqClosed_graph_of_webbedSpace A.isClosed_graph.isSeqClosed hsurj

end Ultrabornological
