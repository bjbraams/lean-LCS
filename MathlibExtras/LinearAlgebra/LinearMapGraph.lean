/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Graphs and relational images of linear maps

The graph and the transposed graph of a total or partially defined linear map are linear
submodules. Total maps are treated over semirings on additive commutative monoids; partially
defined maps use rings and additive commutative groups, as required by `LinearPMap`.
Topological consequences are in `TopologicalVectorSpaces.LinearMapGraph`.

## Main definitions

* `LinearMap.transposedGraph`, `LinearPMap.transposedGraph`: the transposed graph `{(A x, x)}`.

## Main statements

* `LinearMap.image_transposedGraph`, `LinearPMap.image_transposedGraph`,
  `LinearMap.image_graph`, `LinearPMap.image_graph`: relational images under graphs.
* `LinearMap.snd_image_graph`, `LinearPMap.snd_image_graph`,
  `LinearMap.snd_image_transposedGraph`, `LinearPMap.snd_image_transposedGraph`: coordinate
  projections of graphs.
-/

public section

open Set

section PartialTransposedGraph

variable {𝕜 : Type*} [Ring 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The transposed graph `{(A x, x)}` of a partially defined linear map, as a linear subspace
of `F × E`. -/
@[expose]
def LinearPMap.transposedGraph (A : E →ₗ.[𝕜] F) : Submodule 𝕜 (F × E) :=
  A.graph.comap (LinearEquiv.prodComm 𝕜 F E : F × E →ₗ[𝕜] E × F)

/-- Membership of the transposed graph of a partially defined linear map. -/
theorem LinearPMap.mem_transposedGraph {A : E →ₗ.[𝕜] F} {q : F × E} :
    q ∈ A.transposedGraph ↔ ∃ x : A.domain, (x : E) = q.2 ∧ A x = q.1 :=
  A.mem_graph_iff

/-- The image of a set under the transposed graph is the image of its preimage. -/
theorem LinearPMap.image_transposedGraph (A : E →ₗ.[𝕜] F) (V : Set F) :
    SetRel.image (A.transposedGraph : Set (F × E)) V = ((↑) : A.domain → E) '' (A ⁻¹' V) := by
  ext y
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hxy, hxv⟩ := LinearPMap.mem_transposedGraph.mp h
    exact ⟨x, by rw [mem_preimage, hxv]; exact hv, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨A x, hx, LinearPMap.mem_transposedGraph.mpr ⟨x, rfl, rfl⟩⟩

/-- The projection of the transposed graph is the domain. -/
theorem LinearPMap.snd_image_transposedGraph (A : E →ₗ.[𝕜] F) :
    Prod.snd '' (A.transposedGraph : Set (F × E)) = (A.domain : Set E) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, hxy, -⟩ := LinearPMap.mem_transposedGraph.mp hq
    exact hxy ▸ x.2
  · intro hy
    exact ⟨(A ⟨y, hy⟩, y), LinearPMap.mem_transposedGraph.mpr ⟨⟨y, hy⟩, rfl, rfl⟩, rfl⟩

end PartialTransposedGraph

section TransposedGraph

variable {𝕜 : Type*} [Semiring 𝕜] {E F : Type*} [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- The transposed graph `{(A x, x)}` of a linear map, as a submodule of `F × E`. -/
@[expose]
def LinearMap.transposedGraph (A : E →ₗ[𝕜] F) : Submodule 𝕜 (F × E) :=
  A.graph.comap (LinearEquiv.prodComm 𝕜 F E : F × E →ₗ[𝕜] E × F)

/-- Membership of the transposed graph of a linear map. -/
theorem LinearMap.mem_transposedGraph {A : E →ₗ[𝕜] F} {q : F × E} :
    q ∈ A.transposedGraph ↔ q.1 = A q.2 :=
  LinearMap.mem_graph_iff _ _

/-- The image of a set under the transposed graph is its preimage. -/
theorem LinearMap.image_transposedGraph (A : E →ₗ[𝕜] F) (V : Set F) :
    SetRel.image (A.transposedGraph : Set (F × E)) V = A ⁻¹' V := by
  ext y
  constructor
  · rintro ⟨v, hv, h⟩
    rw [mem_preimage, ← LinearMap.mem_transposedGraph.mp h]
    exact hv
  · intro hy
    exact ⟨A y, hy, LinearMap.mem_transposedGraph.mpr rfl⟩

/-- The projection of the transposed graph of a linear map is the whole space. -/
theorem LinearMap.snd_image_transposedGraph (A : E →ₗ[𝕜] F) :
    Prod.snd '' (A.transposedGraph : Set (F × E)) = univ :=
  eq_univ_of_forall fun y ↦ ⟨(A y, y), LinearMap.mem_transposedGraph.mpr rfl, rfl⟩

end TransposedGraph

section PartialGraph

variable {𝕜 : Type*} [Ring 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The image of a set under the graph of a partially defined linear map. -/
theorem LinearPMap.image_graph (A : F →ₗ.[𝕜] E) (V : Set F) :
    SetRel.image (A.graph : Set (F × E)) V = A '' (((↑) : A.domain → F) ⁻¹' V) := by
  ext y
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hxv, hxy⟩ := A.mem_graph_iff.mp h
    exact ⟨x, by rw [mem_preimage, hxv]; exact hv, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, A.mem_graph x⟩

/-- The projection of the graph of a partially defined linear map is its range. -/
theorem LinearPMap.snd_image_graph (A : F →ₗ.[𝕜] E) :
    Prod.snd '' (A.graph : Set (F × E)) = Set.range A := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, -, hxy⟩ := A.mem_graph_iff.mp hq
    exact ⟨x, hxy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨((x : F), A x), A.mem_graph x, rfl⟩

end PartialGraph

section Graph

variable {𝕜 : Type*} [Semiring 𝕜] {E F : Type*} [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- The image of a set under the graph of a linear map. -/
theorem LinearMap.image_graph (A : F →ₗ[𝕜] E) (V : Set F) :
    SetRel.image (A.graph : Set (F × E)) V = A '' V := by
  ext y
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, ((LinearMap.mem_graph_iff _ _).mp h).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (LinearMap.mem_graph_iff _ _).mpr rfl⟩

/-- The projection of the graph of a linear map is its range. -/
theorem LinearMap.snd_image_graph (A : F →ₗ[𝕜] E) :
    Prod.snd '' (A.graph : Set (F × E)) = Set.range A := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, ((LinearMap.mem_graph_iff _ _).mp hq).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, A x), (LinearMap.mem_graph_iff _ _).mpr rfl, rfl⟩

end Graph
