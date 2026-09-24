/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion

/-!
# Neighbourhoods in completions

This specializes Mathlib's neighbourhood-basis theorem for dense inducing maps at zero.
Only a uniform space with a distinguished zero is needed, without a group structure. The
scalar-action and continuous-dual constructions are in `TopologicalVectorSpaces.Completion`.

## Main statements

* `UniformSpace.Completion.hasBasis_nhds_zero_closure_image`: the closures of the images of the
  neighbourhoods of zero form a basis of neighbourhoods of zero in the completion.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], I §1.5
-/

public section

open Set Filter

open scoped Topology Pointwise

namespace UniformSpace.Completion

variable {E : Type*} [Zero E] [UniformSpace E]

/-- The closures of the images of the neighbourhoods of zero in `E` form a basis of
neighbourhoods of zero in the completion of `E`. -/
theorem hasBasis_nhds_zero_closure_image :
    (𝓝 (0 : Completion E)).HasBasis (fun V : Set E ↦ V ∈ 𝓝 (0 : E))
      fun V ↦ closure (((↑) : E → Completion E) '' V) := by
  simpa only [coe_zero, id_eq] using
    (𝓝 (0 : E)).basis_sets.hasBasis_of_isDenseInducing (isDenseInducing_coe (α := E))

end UniformSpace.Completion
