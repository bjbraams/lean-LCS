/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.FinalTopology
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# The topology of test functions is a final locally convex topology

Mathlib defines the topology on the space `𝓓^{n}(Ω, F)` of test functions as the infimum of all
locally convex topologies that are coarser than the inductive limit topology of the spaces
`𝓓^{n}_{K}(E, F)`, for the compact subsets `K` of `Ω`. This file records that this is the
final locally convex topology, in the sense of `locallyConvexFinalTopology`, for the family of
inclusions `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)`. The general results about final locally convex
topologies therefore apply to test functions.

## Main statements

* `TestFunction.topologicalSpace_eq_locallyConvexFinalTopology`.

## Tags

test functions, distributions, inductive limit, LF space
-/

public section

open Set TopologicalSpace

open scoped Topology Distributions

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

variable (Ω F n) in
/-- The inclusions of the spaces of test functions with support in a compact subset of `Ω`, as
a family of linear maps indexed by those compact subsets. -/
@[expose]
noncomputable def inclusionFamily :
    ∀ K : {K : Compacts E // (K : Set E) ⊆ Ω}, 𝓓^{n}_{K.1}(E, F) →ₗ[ℝ] 𝓓^{n}(Ω, F) :=
  fun K ↦ (ofSupportedInCLM ℝ K.2).toLinearMap

variable (Ω F n) in
/-- The topology of the space of test functions is the final locally convex topology for the
inclusions of the spaces of test functions with support in a fixed compact set. -/
theorem topologicalSpace_eq_locallyConvexFinalTopology :
    TestFunction.topologicalSpace Ω F n = locallyConvexFinalTopology (inclusionFamily Ω F n) := by
  have key (t : TopologicalSpace 𝓓^{n}(Ω, F)) : originalTop Ω F n ≤ t ↔
      ∀ K : {K : Compacts E // (K : Set E) ⊆ Ω},
        @Continuous _ _ _ t (inclusionFamily Ω F n K) := by
    simp only [originalTop, iSup_le_iff, ← continuous_iff_coinduced_le]
    exact ⟨fun h K ↦ h K.1 K.2, fun h K hK ↦ h ⟨K, hK⟩⟩
  refine congrArg sInf (Set.ext fun t ↦ ?_)
  simp only [mem_ofPred_eq, key t]
  tauto

end TestFunction
