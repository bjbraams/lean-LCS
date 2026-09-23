/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion

/-!
# Neighbourhoods in group completions

`UniformSpace.Completion.hasBasis_nhds_zero_closure_image` describes the neighbourhoods
of zero in a completion by closures of images of neighbourhoods in the original space.
It specializes Mathlib's neighbourhood-basis theorem for dense-inducing maps.
The scalar-action and continuous-dual constructions are in
`TopologicalVectorSpaces.Completion`.
-/

public section

open Set Filter

open scoped Topology Pointwise

namespace UniformSpace.Completion

section Group

variable {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]

omit [IsUniformAddGroup E] in
/-- The closures of the images of the neighbourhoods of zero in `E` form a basis of
neighbourhoods of zero in the completion of `E`. -/
theorem hasBasis_nhds_zero_closure_image :
    (𝓝 (0 : Completion E)).HasBasis (fun V : Set E ↦ V ∈ 𝓝 (0 : E))
      fun V ↦ closure (((↑) : E → Completion E) '' V) := by
  simpa only [coe_zero, id_eq] using
    (𝓝 (0 : E)).basis_sets.hasBasis_of_isDenseInducing (isDenseInducing_coe (α := E))

end Group

end UniformSpace.Completion
