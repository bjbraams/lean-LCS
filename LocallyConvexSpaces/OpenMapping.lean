/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TopologicalGroups.NearlyOpen

/-!
# The open mapping theorem for a barrelled codomain

A continuous linear map from a Fréchet space onto a barrelled Hausdorff space is open. Here a
Fréchet space is a complete, first-countable, locally convex topological vector space. More
generally, a surjective linear map with closed graph from a Fréchet space onto a barrelled space
is open.

The proof has two steps. Barrelledness of the codomain makes every surjective linear map *nearly
open* (`LinearMap.closure_image_mem_nhds_of_barrelledSpace` in `LocallyConvexSpaces.Barrel`): the
closure of the image of a convex balanced neighbourhood of zero is a barrel, hence a neighbourhood
of zero. Completeness and first countability of the domain together with closedness of the graph
then upgrade near openness to openness (`AddMonoidHom.isOpenMap_of_isClosed_graph_of_nearlyOpen` in
`TopologicalGroups.NearlyOpen`).

## Main statements

* `LinearMap.isOpenMap_of_isClosed_graph_of_barrelledSpace`: a surjective linear map with closed
  graph from a Fréchet space onto a barrelled space is open.
* `ContinuousLinearMap.isOpenMap_of_barrelledSpace`: the **open mapping theorem**: a continuous
  linear map from a Fréchet space onto a barrelled Hausdorff space is open.
* `ContinuousLinearMap.isQuotientMap_of_barrelledSpace`: such a map is a quotient map.
* `LinearEquiv.continuous_symm_of_barrelledSpace`: a continuous linear bijection from a Fréchet
  space onto a barrelled Hausdorff space has a continuous inverse.

## Relation to other open mapping theorems

`ContinuousLinearMap.isOpenMap` in `Mathlib/Analysis/Normed/Operator/Banach.lean` is the open
mapping theorem for Banach spaces. Mathlib PR #41166 (K. H. Wilson, draft), file
`Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, generalizes it to complete first-countable
topological vector spaces over a nontrivially normed field, without local convexity, for both
the domain and the codomain. The theorem in this file has a different hypothesis on the
codomain: barrelled instead of complete and first countable. A complete first-countable
topological vector space is a Baire space and therefore barrelled
(`BaireSpace.instBarrelledSpace`), so for a locally convex domain over `ℝ` or `ℂ` the theorem of
this file contains that of the PR; see the `example` at the end of the file.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §2 and IV §8
* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §34

## Tags

open mapping theorem, barrelled space, Fréchet space
-/

public section

open Set Filter Function

open scoped Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [CompleteSpace E] [FirstCountableTopology E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [BarrelledSpace 𝕜 F]

/-- A surjective linear map with closed graph from a complete, first-countable, locally convex
space onto a barrelled space is an open map. -/
theorem LinearMap.isOpenMap_of_isClosed_graph_of_barrelledSpace (f : E →ₗ[𝕜] F)
    (hf : IsClosed (f.graph : Set (E × F))) (hsurj : Surjective f) : IsOpenMap f := by
  have hgraph : (f.toAddMonoidHom.graph : Set (E × F)) = (f.graph : Set (E × F)) := by
    ext p
    exact eq_comm
  refine f.toAddMonoidHom.isOpenMap_of_isClosed_graph_of_nearlyOpen (hgraph ▸ hf) fun U hU ↦ ?_
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hU
  exact mem_of_superset (LinearMap.closure_image_mem_nhds_of_barrelledSpace hsurj hWc hWb hW)
    (closure_mono (image_mono hWU))

variable [T2Space F]

/-- The **open mapping theorem** for a barrelled codomain: a continuous linear map from a
complete, first-countable, locally convex space onto a barrelled Hausdorff space is an open
map. -/
theorem ContinuousLinearMap.isOpenMap_of_barrelledSpace (f : E →L[𝕜] F) (hsurj : Surjective f) :
    IsOpenMap f :=
  f.toLinearMap.isOpenMap_of_isClosed_graph_of_barrelledSpace
    (isClosed_eq continuous_snd (f.continuous.comp continuous_fst)) hsurj

/-- A continuous linear map from a complete, first-countable, locally convex space onto a
barrelled Hausdorff space is a quotient map. -/
theorem ContinuousLinearMap.isQuotientMap_of_barrelledSpace (f : E →L[𝕜] F)
    (hsurj : Surjective f) : Topology.IsQuotientMap f :=
  (f.isOpenMap_of_barrelledSpace hsurj).isQuotientMap f.continuous hsurj

/-- A continuous linear bijection from a complete, first-countable, locally convex space onto a
barrelled Hausdorff space has a continuous inverse. -/
theorem LinearEquiv.continuous_symm_of_barrelledSpace (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  exact ContinuousLinearMap.isOpenMap_of_barrelledSpace ⟨e.toLinearMap, h⟩ e.surjective s hs

/-- The open mapping theorem of this file applies when the codomain is a complete
first-countable topological vector space, because such a space is a Baire space and hence
barrelled. For these spaces the statement is contained in `ContinuousLinearMap.isOpenMap` of
Mathlib PR #41166 (K. H. Wilson), file `Mathlib/Analysis/Normed/Operator/OpenMapping.lean`,
which does not assume local convexity of the domain. -/
example {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [CompleteSpace F] [FirstCountableTopology F] [T2Space F] (f : E →L[𝕜] F)
    (hsurj : Surjective f) : IsOpenMap f :=
  haveI : (uniformity F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  f.isOpenMap_of_barrelledSpace hsurj
