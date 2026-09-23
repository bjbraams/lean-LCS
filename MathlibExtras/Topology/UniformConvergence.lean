/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Continuity on members of a uniform-convergence family

For `X →ᵤ[𝔖] Y`, the space of functions with uniform convergence on the members of `𝔖`,
continuity on a member of the family is a closed condition. This follows by restriction from
Mathlib's closedness of the continuous functions for uniform convergence.

## Main statements

* `UniformOnFun.isClosed_setOf_continuousOn`.
-/

public section

open Set
open scoped UniformConvergence

namespace UniformOnFun

variable {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
  {𝔖 : Set (Set X)} {S : Set X}

/-- Continuity on a member of a family is a closed condition for uniform convergence
on that family. -/
theorem isClosed_setOf_continuousOn (hS : S ∈ 𝔖) :
    IsClosed {f : X →ᵤ[𝔖] Y | ContinuousOn (toFun 𝔖 f) S} := by
  simpa only [continuousOn_iff_continuous_domRestrict, preimage_ofPred_eq,
    Function.comp_apply, UniformFun.toFun_ofFun] using
    (UniformFun.isClosed_setOfPred_continuous (α := S) (β := Y)).preimage
      (UniformOnFun.uniformContinuous_restrict X Y 𝔖 hS).continuous

end UniformOnFun
