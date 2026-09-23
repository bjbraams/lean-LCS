/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.TestFunctionTopology
public import LocallyConvexSpaces.DualCompleteness
public import MathlibExtras.Analysis.ContDiffMapSupportedIn
public import TopologicalVectorSpaces.TestFunction

/-!
# Bornological test-function spaces and complete strong duals

For every open subset `Ω` of a real normed space, every real normed target `F`, and every
smoothness order `n : ℕ∞`, the test-function space `𝓓^{n}(Ω, F)` is bornological. Its topology
is final for the inclusions of the first-countable spaces with fixed compact support.
Thus bounded linear maps out of test-function space are continuous, and its real or
complex strong dual is complete for uniform convergence on bounded sets (with a compatible
scalar action on `F`).

These conclusions require neither completeness of `F` nor finite-dimensionality of the
domain. They do not assert completeness of the test-function space itself.
All test-function notation comes from Mathlib's `Distributions` scope.
-/

public section

open Set TopologicalSpace Bornology
open scoped Distributions

namespace TestFunction

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {Ω : Opens E} {n : ℕ∞}

/-- Test-function spaces are bornological: their topology is final for the bornological
spaces of functions supported in fixed compact subsets. -/
instance instBornologicalSpace : BornologicalSpace 𝕜 𝓓^{n}(Ω, F) := by
  have : BornologicalSpace ℝ 𝓓^{n}(Ω, F) := by
    rw [topologicalSpace_eq_locallyConvexFinalTopology]
    exact locallyConvexFinalTopology.bornologicalSpace (inclusionFamily Ω F n)
  exact BornologicalSpace.of_restrictScalars

/-- The real or complex strong dual of test-function space is complete for uniform convergence on
bounded sets, even when the normed target of the test functions is incomplete. -/
instance instCompleteSpaceStrongDual : CompleteSpace (StrongDual 𝕜 𝓓^{n}(Ω, F)) :=
  BornologicalSpace.completeSpace_strongDual

/-- A real or complex linear map from test functions to a locally convex space is continuous exactly
when it maps bounded sets to bounded sets. -/
theorem continuous_iff_forall_isVonNBounded_image {G : Type*} [AddCommGroup G] [Module ℝ G]
    [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    [LocallyConvexSpace ℝ G] (f : 𝓓^{n}(Ω, F) →ₗ[𝕜] G) :
    Continuous f ↔ ∀ B, IsVonNBounded 𝕜 B → IsVonNBounded 𝕜 (f '' B) := by
  exact ⟨fun h _ hB ↦ hB.image (⟨f, h⟩ : 𝓓^{n}(Ω, F) →L[𝕜] G),
    f.continuous_of_forall_isVonNBounded_image⟩

end TestFunction
