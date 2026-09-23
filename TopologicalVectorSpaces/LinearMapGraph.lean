/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences
public import MathlibExtras.LinearAlgebra.LinearMapGraph

/-!
# Topological consequences of graph identities

No local convexity or completeness is needed. The algebraic graph identities are in
`MathlibExtras.LinearAlgebra.LinearMapGraph`.

## Main statements

* `LinearMap.isSeqClosed_transposedGraph`, `LinearMap.isClosed_transposedGraph`: closedness
  passes to the transposed graph.
* `LinearMap.continuous_of_forall_image_transposedGraph`: continuity in terms of images of
  neighbourhoods under the transposed graph.
* `LinearMap.isOpenMap_of_forall_image_graph`, `LinearPMap.isOpenMap_of_forall_image_graph`:
  openness in terms of images of neighbourhoods under the graph.
-/

public section

open Set Filter

open scoped Topology Pointwise

section TransposedGraph

variable {𝕜 : Type*} [Ring 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

variable [TopologicalSpace E] [TopologicalSpace F]

/-- The transposed graph is sequentially closed if the graph is. -/
theorem LinearMap.isSeqClosed_transposedGraph {A : E →ₗ[𝕜] F}
    (hA : IsSeqClosed (A.graph : Set (E × F))) :
    IsSeqClosed (A.transposedGraph : Set (F × E)) :=
  hA.preimage continuous_swap.seqContinuous

/-- The transposed graph is closed if the graph is. -/
theorem LinearMap.isClosed_transposedGraph {A : E →ₗ[𝕜] F}
    (hA : IsClosed (A.graph : Set (E × F))) : IsClosed (A.transposedGraph : Set (F × E)) :=
  hA.preimage continuous_swap

/-- A linear map is continuous if the preimages of neighbourhoods of zero are neighbourhoods of
zero, in terms of the transposed graph. -/
theorem LinearMap.continuous_of_forall_image_transposedGraph [IsTopologicalAddGroup E]
    [IsTopologicalAddGroup F] (A : E →ₗ[𝕜] F)
    (h : ∀ V ∈ 𝓝 (0 : F), SetRel.image (A.transposedGraph : Set (F × E)) V ∈ 𝓝 (0 : E)) :
    Continuous A := by
  refine continuous_of_continuousAt_zero A fun V hV ↦ ?_
  rw [map_zero] at hV
  have h' := h V hV
  rwa [A.image_transposedGraph] at h'

end TransposedGraph

section Graph

variable {𝕜 : Type*} [Ring 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

variable [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup E]

/-- A partially defined linear map is open if its graph maps neighbourhoods of zero to
neighbourhoods of zero. -/
theorem LinearPMap.isOpenMap_of_forall_image_graph [IsTopologicalAddGroup F] (A : F →ₗ.[𝕜] E)
    (h : ∀ V ∈ 𝓝 (0 : F), SetRel.image (A.graph : Set (F × E)) V ∈ 𝓝 (0 : E)) :
    IsOpenMap A := by
  refine (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := A.toFun)).mpr fun s hs ↦ ?_
  obtain ⟨V, hV, hVs⟩ := mem_nhds_subtype _ _ _ |>.mp (mem_map.mp hs)
  have h' := h V hV
  rw [A.image_graph] at h'
  exact mem_of_superset h' ((image_mono hVs).trans (image_preimage_subset _ s))

/-- A linear map is open if its graph maps neighbourhoods of zero to neighbourhoods of zero. -/
theorem LinearMap.isOpenMap_of_forall_image_graph [IsTopologicalAddGroup F] (A : F →ₗ[𝕜] E)
    (h : ∀ V ∈ 𝓝 (0 : F), SetRel.image (A.graph : Set (F × E)) V ∈ 𝓝 (0 : E)) :
    IsOpenMap A := by
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun s hs ↦ ?_
  have h' := h _ (mem_map.mp hs)
  rw [A.image_graph] at h'
  exact mem_of_superset h' (image_preimage_subset A s)

end Graph
