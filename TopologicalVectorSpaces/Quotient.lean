/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Neighbourhood bases in module quotients

`Submodule.Quotient.nhds_zero_hasBasis_image` transports any basis at zero through the open
quotient map. The scalar ring need not carry a topology or a norm.
-/

public section

open Set Filter

open scoped Topology

namespace Submodule.Quotient

section Basis

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] (N : Submodule R E)

/-- The images under the quotient map of a basis of neighbourhoods of zero in `E` form a basis
of neighbourhoods of zero in `E ⧸ N`. -/
theorem nhds_zero_hasBasis_image {ι : Sort*} {p : ι → Prop} {b : ι → Set E}
    (h : (𝓝 (0 : E)).HasBasis p b) :
    (𝓝 (0 : E ⧸ N)).HasBasis p fun i ↦ N.mkQ '' b i := by
  have hmap : Filter.map N.mkQ (𝓝 (0 : E)) = 𝓝 (0 : E ⧸ N) := by
    have h0 := N.isOpenMap_mkQ.map_nhds_eq (x := (0 : E))
      N.isQuotientMap_mkQ.continuous.continuousAt
    rwa [map_zero] at h0
  rw [← hmap]
  exact h.map _

end Basis

end Submodule.Quotient
