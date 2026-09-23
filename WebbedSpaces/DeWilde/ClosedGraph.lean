/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.FinalTopology
public import LocallyConvexSpaces.FrechetUltrabornological
public import Mathlib.LinearAlgebra.LinearPMap
public import TopologicalVectorSpaces.LinearMapGraph
public import WebbedSpaces.DeWilde.Relation
public import WebbedSpaces.Frechet

/-!
# De Wilde's closed graph theorem

A linear map with sequentially closed graph from an ultrabornological space to a webbed locally
convex space is continuous. The same holds for a first-countable Baire domain, and, if the
graph is closed, for an arbitrary Baire topological vector space and for a locally convex hull
of such spaces as domain. These are the statements of
[G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.2.(1)–(5).

All of them are obtained from De Wilde's theorem for linear relations in
`WebbedSpaces.DeWilde.Relation`, applied to the transposed graph
`{(A x, x)}` of the map `A`.

## Main statements

* `LinearMap.continuous_of_isSeqClosed_graph_of_baireSpace`: first-countable Baire domain,
  sequentially closed graph, §35.2.(1).
* `LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace`: **De Wilde's closed
  graph theorem**, §35.2.(2).
* `LinearMap.continuous_of_isSeqClosed_graph_of_strictlyWebbedSpace`: the same for a strictly
  webbed codomain, in particular for a Fréchet codomain.
* `LinearPMap.domain_eq_top_of_isClosed_graph`, `LinearPMap.continuous_of_isClosed_graph`: a
  partially defined map with closed graph and non-meagre domain, §35.2.(3).
* `LinearMap.continuous_of_isClosed_graph_of_baireSpace`: Baire domain, closed graph, §35.2.(4).
* `LinearMap.continuous_of_isClosed_graph_of_locallyConvexFinalTopology`: a locally convex hull
  of Baire spaces as domain, §35.2.(5).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.2
* [M. De Wilde, *Closed Graph Theorems and Webbed Spaces*][dewilde1978]

## Tags

closed graph theorem, De Wilde, webbed space, ultrabornological space
-/

public section

open Set Filter

open scoped Topology

universe u v


section ClosedGraph

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- The closed graph theorem for a first-countable Baire domain: a linear map with sequentially
closed graph from a first-countable Baire topological vector space into a webbed locally convex
space is continuous, Köthe II §35.2.(1). -/
theorem LinearMap.continuous_of_isSeqClosed_graph_of_baireSpace [BaireSpace E]
    [FirstCountableTopology E] (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) : Continuous A := by
  have : Nonempty E := ⟨0⟩
  refine A.continuous_of_forall_image_transposedGraph fun V hV ↦ ?_
  refine A.transposedGraph.image_mem_nhds_zero_of_isSeqClosed
    (LinearMap.isSeqClosed_transposedGraph hA) ?_ hV
  rw [A.snd_image_transposedGraph]
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

/-- The closed graph theorem for a Baire domain: a linear map with closed graph from a Baire
topological vector space into a webbed locally convex space is continuous,
Köthe II §35.2.(4). -/
theorem LinearMap.continuous_of_isClosed_graph_of_baireSpace [BaireSpace E] (A : E →ₗ[𝕜] F)
    (hA : IsClosed (A.graph : Set (E × F))) : Continuous A := by
  have : Nonempty E := ⟨0⟩
  refine A.continuous_of_forall_image_transposedGraph fun V hV ↦ ?_
  refine A.transposedGraph.image_mem_nhds_zero_of_isClosed
    (LinearMap.isClosed_transposedGraph hA) ?_ hV
  rw [A.snd_image_transposedGraph]
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

/-- A partially defined linear map into a webbed locally convex space, with closed graph and
with a domain that is not meagre, is defined everywhere, Köthe II §35.2.(3). -/
theorem LinearPMap.domain_eq_top_of_isClosed_graph (A : E →ₗ.[𝕜] F)
    (hA : IsClosed (A.graph : Set (E × F))) (hne : ¬IsMeagre (A.domain : Set E)) :
    A.domain = ⊤ := by
  have h := A.transposedGraph.image_mem_nhds_zero_of_isClosed (hA.preimage continuous_swap)
    (by rwa [A.snd_image_transposedGraph]) (univ_mem : (univ : Set F) ∈ 𝓝 (0 : F))
  rw [A.image_transposedGraph, preimage_univ, image_univ, Subtype.range_coe] at h
  -- A subspace that is a neighbourhood of zero is the whole space.
  have htop : A.domain.restrictScalars ℝ = ⊤ :=
    (A.domain.restrictScalars ℝ).eq_top_of_nonempty_interior'
      ⟨0, mem_interior_iff_mem_nhds.mpr h⟩
  exact (Submodule.restrictScalars_eq_top_iff ℝ 𝕜 E).mp htop

/-- A partially defined linear map into a webbed locally convex space, with closed graph and
with a domain that is not meagre, is continuous, Köthe II §35.2.(3). -/
theorem LinearPMap.continuous_of_isClosed_graph (A : E →ₗ.[𝕜] F)
    (hA : IsClosed (A.graph : Set (E × F))) (hne : ¬IsMeagre (A.domain : Set E)) :
    Continuous A := by
  refine continuous_of_continuousAt_zero A.toFun fun V hV ↦ ?_
  have h0 : A.toFun 0 = 0 := map_zero _
  rw [h0] at hV
  have h := A.transposedGraph.image_mem_nhds_zero_of_isClosed (hA.preimage continuous_swap)
    (by rwa [A.snd_image_transposedGraph]) hV
  rw [A.image_transposedGraph] at h
  have hc : ContinuousAt ((↑) : A.domain → E) 0 := continuous_subtype_val.continuousAt
  have h' := hc.preimage_mem_nhds (by simpa using h)
  rw [preimage_image_eq _ Subtype.coe_injective] at h'
  exact h'

end ClosedGraph

section Hull

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {X : ι → Type*} {E F : Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)] [∀ i, Module ℝ (X i)]
  [∀ i, IsScalarTower ℝ 𝕜 (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, IsTopologicalAddGroup (X i)] [∀ i, ContinuousSMul ℝ (X i)] [∀ i, BaireSpace (X i)]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- A linear map with closed graph from a locally convex hull of Baire topological vector spaces
into a webbed locally convex space is continuous, Köthe II §35.2.(5). It suffices that the
compositions with the maps that define the hull have closed graphs. -/
theorem LinearMap.continuous_of_isClosed_graph_of_locallyConvexFinalTopology
    (f : ∀ i, X i →ₗ[𝕜] E) (A : E →ₗ[𝕜] F)
    (hA : ∀ i, IsClosed ((A ∘ₗ f i).graph : Set (X i × F))) :
    @Continuous E F (locallyConvexFinalTopology f) _ A :=
  (locallyConvexFinalTopology.continuous_iff f A).mpr fun i ↦
    (A ∘ₗ f i).continuous_of_isClosed_graph_of_baireSpace (hA i)

end Hull

section Ultrabornological

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type u} {F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [UltrabornologicalSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F]

/-- **De Wilde's closed graph theorem**: a linear map with sequentially closed graph from an
ultrabornological space into a webbed locally convex space is continuous, Köthe II §35.2.(2).
Banach spaces, Fréchet spaces and LF spaces are ultrabornological. -/
theorem LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace [WebbedSpace F]
    (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F))) : Continuous A := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  exact A.continuous_of_forall_image_transposedGraph fun V hV ↦
    A.transposedGraph.image_mem_nhds_zero_of_ultrabornologicalSpace
      (LinearMap.isSeqClosed_transposedGraph hA) A.snd_image_transposedGraph hV

/-- De Wilde's closed graph theorem for a strictly webbed codomain. -/
theorem LinearMap.continuous_of_isSeqClosed_graph_of_strictlyWebbedSpace
    [StrictlyWebbedSpace 𝕜 F] (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F))) :
    Continuous A := by
  have : WebbedSpace F := StrictlyWebbedSpace.toWebbedSpace (𝕜 := 𝕜)
  exact A.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace hA

end Ultrabornological

/-- A linear map with sequentially closed graph from an ultrabornological space to a Fréchet
space is continuous: Fréchet spaces are strictly webbed
(`StrictlyWebbedSpace.of_completeSpace_firstCountable`). -/
example {𝕜 : Type v} [RCLike 𝕜] {E : Type u} {F : Type*}
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [UltrabornologicalSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [CompleteSpace F]
    [FirstCountableTopology F] (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F))) :
    Continuous A :=
  A.continuous_of_isSeqClosed_graph_of_strictlyWebbedSpace hA
