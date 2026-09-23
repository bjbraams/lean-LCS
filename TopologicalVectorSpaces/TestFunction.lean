/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TopologicalVectorSpaces.ScalarRestriction

/-!
# Real and complex scalar multiplication on test functions

The topology of `𝓓^{n}(Ω, F)` is defined using real locally convex spaces in Mathlib.
This file proves joint continuity of scalar multiplication over any `RCLike` field,
including complex scalars, using `RCLike.continuousSMul_of_continuous_smul_I` from
`TopologicalVectorSpaces.ScalarRestriction`. The imaginary unit acts continuously by
postcomposition on the target `F`.
-/

public section

open TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {Ω : Opens E} {n : ℕ∞}

/-- Scalar multiplication on test functions is jointly continuous over real or complex
scalars. This completes the scalar-action TODO in Mathlib's test-function construction. -/
instance instContinuousSMulRCLike : ContinuousSMul 𝕜 𝓓^{n}(Ω, F) := by
  let T : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, F) :=
    postcompCLM ((RCLike.I : 𝕜) • ContinuousLinearMap.id 𝕜 F)
  have hT : ∀ f : 𝓓^{n}(Ω, F), T f = (RCLike.I : 𝕜) • f := by
    intro f
    ext x
    rfl
  apply RCLike.continuousSMul_of_continuous_smul_I
  exact T.continuous.congr hT

end TestFunction
