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
# The closed graph theorem for a barrelled domain

A linear map with closed graph from a barrelled space to a complete, first-countable locally
convex topological vector space is continuous. No Hausdorff assumption is needed for this
statement; in particular it applies to every Fréchet codomain.

The proof has two steps. Barrelledness of the domain makes every linear map *nearly continuous*
(`LinearMap.closure_preimage_mem_nhds_of_barrelledSpace` in `LocallyConvexSpaces.Barrel`): the
closure of the preimage of a convex balanced neighbourhood of zero is a barrel, hence a
neighbourhood of zero. Completeness and first countability of the codomain together with closedness
of the graph then upgrade near continuity to continuity
(`AddMonoidHom.continuous_of_isClosed_graph_of_nearlyContinuous` in `TopologicalGroups.NearlyOpen`).

## Main statements

* `LinearMap.continuous_of_isClosed_graph_of_barrelledSpace`: the closed graph theorem.
* `LinearMap.continuous_of_forall_continuous_comp_of_barrelledSpace`: a linear map `g` from a
  barrelled space to a Fréchet space is continuous as soon as `φ i ∘ g` is continuous for a family
  `φ` of continuous linear functionals that separates the points of the codomain.

## Relation to other closed graph theorems

`LinearMap.continuous_of_isClosed_graph` in `Mathlib/Analysis/Normed/Operator/Banach.lean` is
the closed graph theorem for Banach spaces. Mathlib PR #41166 (K. H. Wilson, draft), file
`Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, generalizes it to complete first-countable
topological vector spaces over a nontrivially normed field, without local convexity, for both
the domain and the codomain. The theorem in this file has a different hypothesis on the domain:
barrelled instead of complete and first countable. A complete first-countable topological vector
space is a Baire space and therefore barrelled (`BaireSpace.instBarrelledSpace`), so for a
locally convex codomain over `ℝ` or `ℂ` the theorem of this file contains that of the PR; see
the `example` at the end of the file.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §2 and IV §8
* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §34

## Tags

closed graph theorem, barrelled space, Fréchet space
-/

public section

open Set Filter Function

open scoped Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [BarrelledSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F]
  [CompleteSpace F] [FirstCountableTopology F]

/-- The **closed graph theorem** for a barrelled domain: a linear map with closed graph from a
barrelled space to a complete, first-countable, locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_barrelledSpace (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := by
  have hgraph : (g.toAddMonoidHom.graph : Set (E × F)) = (g.graph : Set (E × F)) := by
    ext p
    exact eq_comm
  refine g.toAddMonoidHom.continuous_of_isClosed_graph_of_nearlyContinuous (hgraph ▸ hg)
    fun V hV ↦ ?_
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWV⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  exact mem_of_superset (g.closure_preimage_mem_nhds_of_barrelledSpace hWc hWb hW)
    (closure_mono (preimage_mono hWV))

/-- A linear map `g` from a barrelled space to a complete, first-countable, locally convex space
is continuous if `φ i ∘ g` is continuous for every member of a family `φ` of continuous linear
functionals that separates the points of the codomain. -/
theorem LinearMap.continuous_of_forall_continuous_comp_of_barrelledSpace (g : E →ₗ[𝕜] F) {ι : Type*}
    (φ : ι → F →L[𝕜] 𝕜) (hφ : ∀ y : F, (∀ i, φ i y = 0) → y = 0)
    (h : ∀ i, Continuous (φ i ∘ g)) : Continuous g := by
  refine g.continuous_of_isClosed_graph_of_barrelledSpace ?_
  have hgraph : (g.graph : Set (E × F)) = ⋂ i, {p : E × F | φ i p.2 = φ i (g p.1)} := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_iInter, mem_ofPred_eq]
    refine ⟨fun hp i ↦ by rw [hp], fun hp ↦ sub_eq_zero.mp (hφ _ fun i ↦ ?_)⟩
    rw [map_sub, hp i, sub_self]
  rw [hgraph]
  exact isClosed_iInter fun i ↦
    isClosed_eq ((φ i).continuous.comp continuous_snd) ((h i).comp continuous_fst)

/-- The closed graph theorem of this file applies when the domain is a complete first-countable
topological vector space, because such a space is a Baire space and hence barrelled. For these
spaces the statement is contained in `LinearMap.continuous_of_isClosed_graph` of Mathlib PR
#41166 (K. H. Wilson), file `Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, which does not
assume local convexity of the codomain. -/
example {E : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [CompleteSpace E] [FirstCountableTopology E] (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g :=
  haveI : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  g.continuous_of_isClosed_graph_of_barrelledSpace hg
