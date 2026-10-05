/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import MathlibExtras.Analysis.ZeroSequenceOfUnits
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Module.Basic
public import TauCeti.Topology.Algebra.OpenMapping.Basic
public import TopologicalGroups.NearlyOpen
public import TopologicalVectorSpaces.Basic

/-!
# Open mapping and closed graph theorems for Baire spaces

This file proves the open mapping and closed graph theorems of Banach–Schauder type for
topological vector spaces over a nontrivially normed field, without any local convexity.

* A surjective linear map with closed graph from a complete, first-countable topological vector
  space onto a Baire topological vector space is open. The codomain need not be Hausdorff,
  complete or first-countable.
* A linear map with closed graph from a Baire topological vector space into a complete,
  first-countable topological vector space is continuous.

Both proofs have the same two steps as those in `LocallyConvexSpaces.OpenMapping` and
`LocallyConvexSpaces.ClosedGraph`. The Baire category theorem replaces barrelledness in the first
step: the closure of the image of a neighbourhood of zero under a surjective linear map onto a
Baire space is a neighbourhood of zero. The successive approximation of
`TopologicalGroups.NearlyOpen` is the second step. For the closed graph theorem the first step is
applied to the first projection of the graph, which is a surjection onto the Baire domain.

## Imported results

The Baire step is `TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero` of
`TauCeti.Topology.Algebra.OpenMapping.Basic`, by the Tau Ceti contributors:
<https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Topology/Algebra/OpenMapping/Basic.lean>.
It is imported directly; no local copy is retained.

## Main statements

* `LinearMap.isOpenMap_of_isClosed_graph_of_baireSpace`: the open mapping theorem for a closed
  graph and a Baire codomain.
* `ContinuousLinearMap.isOpenMap_of_baireSpace`: the open mapping theorem for a continuous linear
  map onto a Hausdorff Baire space.
* `LinearMap.continuous_of_isClosed_graph_of_baireSpace_of_firstCountableTopology`: the closed
  graph theorem for a Baire domain and a complete first-countable codomain.

## Relation to other mapping theorems

Mathlib PR #41166 (K. H. Wilson, draft), file `Mathlib/Analysis/Normed/Operator/OpenMapping.lean`,
proves the open mapping theorem `ContinuousLinearMap.isOpenMap` and the closed graph theorem
`LinearMap.continuous_of_isClosed_graph` for complete first-countable topological vector spaces
over a nontrivially normed field. Since a complete first-countable topological vector space is a
Baire space, its open mapping theorem is the case of
`ContinuousLinearMap.isOpenMap_of_baireSpace` with a complete first-countable codomain, and its
closed graph theorem is the case of
`LinearMap.continuous_of_isClosed_graph_of_baireSpace_of_firstCountableTopology` with a complete
first-countable domain. The statements here were obtained independently. The webbed-space
counterpart `LinearMap.continuous_of_isClosed_graph_of_baireSpace` in
`WebbedSpaces.DeWilde.ClosedGraph` has a Baire domain and a webbed locally convex codomain.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], I §3
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §15.12

## Tags

open mapping theorem, closed graph theorem, Baire space, Banach–Schauder theorem
-/

public section

open Set Filter Function

open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]

section OpenMapping

variable [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] [CompleteSpace E] [FirstCountableTopology E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [BaireSpace F]

/-- The **open mapping theorem** for a Baire codomain: a surjective linear map with closed graph
from a complete, first-countable topological vector space onto a Baire topological vector space is
an open map. No local convexity is assumed, and the codomain need not be Hausdorff. -/
theorem LinearMap.isOpenMap_of_isClosed_graph_of_baireSpace (f : E →ₗ[𝕜] F)
    (hf : IsClosed (f.graph : Set (E × F))) (hsurj : Surjective f) : IsOpenMap f := by
  have hgraph : (f.toAddMonoidHom.graph : Set (E × F)) = (f.graph : Set (E × F)) := by
    ext p
    exact eq_comm
  exact f.toAddMonoidHom.isOpenMap_of_isClosed_graph_of_nearlyOpen (hgraph ▸ hf) fun U hU ↦
    TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero f hsurj
      (fun x ↦ (continuous_id.smul continuous_const).continuousAt) hU

variable [T2Space F]

/-- The **open mapping theorem** for a Baire codomain: a continuous linear map from a complete,
first-countable topological vector space onto a Hausdorff Baire topological vector space is an
open map. -/
theorem ContinuousLinearMap.isOpenMap_of_baireSpace (f : E →L[𝕜] F) (hsurj : Surjective f) :
    IsOpenMap f :=
  f.toLinearMap.isOpenMap_of_isClosed_graph_of_baireSpace f.isClosed_graph hsurj

/-- A continuous linear map from a complete, first-countable topological vector space onto a
Hausdorff Baire topological vector space is a quotient map. -/
theorem ContinuousLinearMap.isQuotientMap_of_baireSpace (f : E →L[𝕜] F) (hsurj : Surjective f) :
    Topology.IsQuotientMap f :=
  (f.isOpenMap_of_baireSpace hsurj).isQuotientMap f.continuous hsurj

end OpenMapping

section ClosedGraph

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [BaireSpace E]
  [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
  [CompleteSpace F] [FirstCountableTopology F]

/-- The **closed graph theorem** for a Baire domain: a linear map with closed graph from a Baire
topological vector space to a complete, first-countable topological vector space is continuous.
No local convexity is assumed. -/
theorem LinearMap.continuous_of_isClosed_graph_of_baireSpace_of_firstCountableTopology
    (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := by
  have hgraph : (g.toAddMonoidHom.graph : Set (E × F)) = (g.graph : Set (E × F)) := by
    ext p
    exact eq_comm
  refine g.toAddMonoidHom.continuous_of_isClosed_graph_of_nearlyContinuous (hgraph ▸ hg)
    fun V hV ↦ ?_
  -- Near continuity: the Baire step for the first projection of the graph onto `E`.
  let π : g.graph →ₗ[𝕜] E := (LinearMap.fst 𝕜 E F).comp g.graph.subtype
  have hπ : Surjective π := fun x ↦ ⟨⟨(x, g x), (LinearMap.mem_graph_iff _ _).mpr rfl⟩, rfl⟩
  have hU : {p : g.graph | (p : E × F).2 ∈ V} ∈ 𝓝 (0 : g.graph) :=
    (continuous_snd.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hV)
  refine mem_of_superset (TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero π hπ
    (fun x ↦ (continuous_id.smul continuous_const).continuousAt) hU) (closure_mono ?_)
  rintro _ ⟨⟨⟨x, y⟩, hxy⟩, hy, rfl⟩
  have hyx : y = g x := (LinearMap.mem_graph_iff _ _).mp hxy
  change g x ∈ V
  rw [← hyx]
  exact hy

end ClosedGraph
