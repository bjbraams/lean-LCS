/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.UniformMulAction
public import TopologicalVectorSpaces.Completion

/-!
# The completion of a topological vector space and of a locally convex space

Mathlib gives the completion `UniformSpace.Completion E` of a topological vector space `E` the
structure of a uniform additive group and of a module with continuous multiplication by each
scalar. The imported module `TopologicalVectorSpaces.Completion` proves joint continuity of
scalar multiplication and identifies the continuous duals. This file proves the remaining
locally convex consequence: the completion of a locally convex space is locally convex.
It also identifies zero-neighbourhood polars in the weak-* duals of the space and its
completion. Evaluation of extended functionals is weak-* continuous on these polars.

Mathlib's module structure on the completion assumes `UniformContinuousConstSMul 𝕜 E`. In a
topological vector space this holds by `uniformContinuousConstSMul_of_continuousConstSMul`,
which cannot be an instance; it is therefore a hypothesis here as well.

## Imported definitions from `TopologicalVectorSpaces.Completion`

* `UniformSpace.Completion.coeCLM 𝕜 E`: the canonical map `E → Completion E` as a continuous
  linear map.
* `UniformSpace.Completion.strongDualEquiv 𝕜 E`: restriction to `E` as a linear equivalence
  between the dual of the completion and the dual of `E`.

## Main statements

* Imported from `TopologicalGroups.Completion`:
  `UniformSpace.Completion.hasBasis_nhds_zero_closure_image`: the
  closures of the images of the
  neighbourhoods of zero in `E` form a basis of neighbourhoods of zero in the completion.
* Imported from `TopologicalVectorSpaces.Completion`: `UniformSpace.Completion.instContinuousSMul`:
  the completion is a
  topological vector space.
* `UniformSpace.Completion.instLocallyConvexSpace`: the completion of a locally convex space is
  locally convex.

* `UniformSpace.Completion.mem_polar_closure_image_iff`: restriction identifies the polars
  of a set and of the closure of its image.
* `UniformSpace.Completion.polarHomeomorph`: the identification of zero-neighbourhood polars
  is a weak-* homeomorphism.
* `UniformSpace.Completion.continuousOn_extend_eval_polar`: evaluation after extension is
  weak-* continuous on each zero-neighbourhood polar.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], I §1.5, II §4.1
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], I §1.5, II §4.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §15.3, §18.4

## Tags

completion, topological vector space, locally convex space
-/

public section

open Set Filter Function

open scoped Topology Pointwise

namespace UniformSpace.Completion

section LocallyConvex

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E]
  [UniformContinuousConstSMul ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- The completion of a locally convex space is locally convex. -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (Completion E) := by
  refine LocallyConvexSpace.ofBasisZero ℝ (Completion E)
    (fun V : Set E ↦ closure (((↑) : E → Completion E) '' V))
    (fun V ↦ V ∈ 𝓝 (0 : E) ∧ Convex ℝ V) ?_ fun V hV ↦ ?_
  · refine hasBasis_nhds_zero_closure_image.to_hasBasis (fun V hV ↦ ?_)
      fun V hV ↦ ⟨V, hV.1, Subset.rfl⟩
    obtain ⟨V', ⟨hV', hV'c⟩, hV'V⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hV
    exact ⟨V', ⟨hV', hV'c⟩, closure_mono (image_mono hV'V)⟩
  · exact (hV.2.is_linear_image (coeCLM ℝ E).toLinearMap.isLinear).closure

end LocallyConvex

end UniformSpace.Completion

namespace UniformSpace.Completion

section Polars

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [ProperSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [UniformContinuousConstSMul 𝕜 E] [ContinuousSMul 𝕜 E]

omit [ProperSpace 𝕜] [ContinuousSMul 𝕜 E] in
/-- Restricting a functional on the completion identifies the polar of the closure of the
image of a set with the polar of the original set. -/
theorem mem_polar_closure_image_iff {U : Set E} (ψ : WeakDual 𝕜 (Completion E)) :
    ψ ∈ WeakDual.polar 𝕜 (closure (((↑) : E → Completion E) '' U)) ↔
      StrongDual.toWeakDual (strongDualEquiv 𝕜 E (WeakDual.toStrongDual ψ)) ∈
        WeakDual.polar 𝕜 U := by
  constructor
  · intro h x hx
    exact h _ (subset_closure ⟨x, hx, rfl⟩)
  · intro h x hx
    exact (closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
      (isClosed_le (WeakDual.toStrongDual ψ).continuous.norm continuous_const)) hx

/-- Restriction and extension give a homeomorphism between the weak-* polars of a zero
neighbourhood and of the closure of its image in the completion. Compactness of the polars
makes the inverse continuous; no assertion about the strong dual topologies is needed. -/
@[expose]
noncomputable def polarHomeomorph {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    WeakDual.polar 𝕜 (closure (((↑) : E → Completion E) '' U)) ≃ₜ WeakDual.polar 𝕜 U := by
  let e : WeakDual 𝕜 (Completion E) ≃ₗ[𝕜] WeakDual 𝕜 E :=
    WeakDual.toStrongDual.trans ((strongDualEquiv 𝕜 E).trans StrongDual.toWeakDual)
  let ep := e.toEquiv.subtypeEquiv (mem_polar_closure_image_iff (𝕜 := 𝕜) (U := U))
  have he : Continuous e := WeakDual.continuous_of_continuous_eval fun x ↦
    WeakDual.eval_continuous (x : Completion E)
  have hep : Continuous ep := (he.comp continuous_subtype_val).subtype_mk _
  let : CompactSpace (WeakDual.polar 𝕜 (closure (((↑) : E → Completion E) '' U))) :=
    isCompact_iff_compactSpace.mp (WeakDual.isCompact_polar_of_mem_nhds (𝕜 := 𝕜)
      (hasBasis_nhds_zero_closure_image.mem_of_mem hU))
  exact ep.toHomeomorphOfContinuousClosed hep hep.isClosedMap

/-- Evaluation at a point of the completion, after extending functionals from the original
space, is weak-* continuous on the polar of every zero neighbourhood. -/
theorem continuousOn_extend_eval_polar (z : Completion E) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    ContinuousOn (fun φ : WeakDual 𝕜 E ↦
      (strongDualEquiv 𝕜 E).symm (WeakDual.toStrongDual φ) z) (WeakDual.polar 𝕜 U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (WeakDual.eval_continuous z).comp
    (continuous_subtype_val.comp (polarHomeomorph (𝕜 := 𝕜) hU).symm.continuous)

end Polars

end UniformSpace.Completion
