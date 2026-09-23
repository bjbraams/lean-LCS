/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.DualCompleteness
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Completeness of the strong dual of Schwartz space

Mathlib's Schwartz space `𝓢(E, F)` of rapidly decreasing smooth functions is first countable,
hence bornological. Its real or complex strong dual is therefore complete for uniform
convergence on bounded sets, without assuming that the normed target `F` is complete.
In particular this applies to scalar-valued tempered distributions with the strong topology.

Mathlib equips `TemperedDistribution` with the topology of pointwise convergence. The
completeness result here concerns `StrongDual`, and makes no claim about that different
topology. Schwartz notation is from the `SchwartzMap` scope.
-/

public section

open scoped SchwartzMap

namespace SchwartzMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]

/-- The strong dual of Schwartz space is complete, over either the real or complex scalars.
No completeness assumption on the target of the Schwartz functions is needed. -/
instance instCompleteSpaceStrongDual : CompleteSpace (StrongDual 𝕜 𝓢(E, F)) :=
  BornologicalSpace.completeSpace_strongDual

end SchwartzMap
