/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.FinalTopology
public import Mathlib.Algebra.DirectSum.Module

/-!
# Locally convex direct sums

The *locally convex direct sum* of a family `E i` of locally convex spaces is the algebraic
direct sum `⨁ i, E i` with the final locally convex topology for the canonical injections
`DirectSum.lof`. It is the coproduct in the category of locally convex spaces.

## Main definitions

* `DirectSum.locallyConvexTopology 𝕜 E`: the locally convex direct sum topology on `⨁ i, E i`.
  It is a term rather than an instance, like `locallyConvexFinalTopology`.

## Main statements

* `DirectSum.continuous_lof`, `DirectSum.continuous_component`: the canonical injections and
  the coordinate projections are continuous.
* `DirectSum.isEmbedding_lof`: every summand is topologically embedded in the direct sum.
* `DirectSum.continuous_iff_forall_comp_lof`: the universal property.
* `DirectSum.t2Space_locallyConvexTopology`: a direct sum of Hausdorff spaces is Hausdorff.

Barrelledness, bornologicity and ultrabornologicity of locally convex direct sums are instances
of `locallyConvexFinalTopology.barrelledSpace`, `.bornologicalSpace` and
`.ultrabornologicalSpace`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §6.1–6.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §4.5
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §18.5

## Tags

locally convex direct sum, coproduct, final topology
-/

public section

open Set Filter Function

open scoped Topology DirectSum

namespace DirectSum

variable (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} [DecidableEq ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]

/-- The locally convex direct sum topology on `⨁ i, E i`: the final locally convex topology
for the canonical injections. -/
@[expose, instance_reducible]
def locallyConvexTopology : TopologicalSpace (⨁ i, E i) :=
  locallyConvexFinalTopology (lof 𝕜 ι E)

variable {𝕜 E}

omit [∀ i, IsScalarTower ℝ 𝕜 (E i)] in
/-- The canonical injections into the locally convex direct sum are continuous. -/
theorem continuous_lof (i : ι) :
    @Continuous (E i) (⨁ i, E i) _ (locallyConvexTopology 𝕜 E) (lof 𝕜 ι E i) :=
  locallyConvexFinalTopology.continuous_apply (lof 𝕜 ι E) i

/-- The **universal property** of the locally convex direct sum: a linear map from the direct
sum to a locally convex space is continuous if and only if its restriction to every summand
is. -/
theorem continuous_iff_forall_comp_lof {G : Type*} [AddCommGroup G] [Module 𝕜 G] [Module ℝ G]
    [IsScalarTower ℝ 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    [LocallyConvexSpace ℝ G] (g : (⨁ i, E i) →ₗ[𝕜] G) :
    @Continuous (⨁ i, E i) G (locallyConvexTopology 𝕜 E) _ g ↔
      ∀ i, Continuous (g ∘ lof 𝕜 ι E i) :=
  locallyConvexFinalTopology.continuous_iff (lof 𝕜 ι E) g

variable [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  [∀ i, LocallyConvexSpace ℝ (E i)]

/-- The coordinate projections of the locally convex direct sum are continuous. -/
theorem continuous_component (i : ι) :
    @Continuous (⨁ i, E i) (E i) (locallyConvexTopology 𝕜 E) _ (component 𝕜 ι E i) := by
  rw [continuous_iff_forall_comp_lof]
  intro j
  by_cases hji : j = i
  · subst hji
    have h : (component 𝕜 ι E j ∘ lof 𝕜 ι E j) = id := funext fun b ↦ component.lof_self 𝕜 j b
    rw [h]
    exact continuous_id
  · have h : (component 𝕜 ι E i ∘ lof 𝕜 ι E j) = fun _ ↦ (0 : E i) := funext fun b ↦ by
      rw [Function.comp_apply, component.of]
      simp [hji]
    rw [h]
    exact continuous_const

/-- Every summand is topologically embedded in the locally convex direct sum. -/
theorem isEmbedding_lof (i : ι) :
    @Topology.IsEmbedding (E i) (⨁ i, E i) _ (locallyConvexTopology 𝕜 E) (lof 𝕜 ι E i) :=
  @Function.LeftInverse.isEmbedding (⨁ i, E i) (E i) (locallyConvexTopology 𝕜 E) _
    (component 𝕜 ι E i) (lof 𝕜 ι E i) (component.lof_self 𝕜 i) (continuous_component i)
    (continuous_lof i)

/-- A locally convex direct sum of Hausdorff spaces is Hausdorff. -/
theorem t2Space_locallyConvexTopology [∀ i, T2Space (E i)] :
    @T2Space (⨁ i, E i) (locallyConvexTopology 𝕜 E) := by
  let _ : TopologicalSpace (⨁ i, E i) := locallyConvexTopology 𝕜 E
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, component 𝕜 ι E i x ≠ component 𝕜 ι E i y := by
    by_contra hcon
    push Not at hcon
    exact hxy (ext_component 𝕜 hcon)
  exact separated_by_continuous (continuous_component i) hi

end DirectSum
