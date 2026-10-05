/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.GDelta.Basic

/-!
# Non-meagre sets

## Main statements

* `nonempty_interior_closure_of_not_isMeagre`: the closure of a non-meagre set has an interior
  point. This is the form in which Baire-category arguments use non-meagreness.
-/

public section

open Set

/-- The closure of a non-meagre set has nonempty interior: a set whose closure has empty interior
is nowhere dense, hence meagre. -/
theorem nonempty_interior_closure_of_not_isMeagre {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : ¬IsMeagre s) : (interior (closure s)).Nonempty := by
  by_contra h
  exact hs (IsNowhereDense.isMeagre (not_nonempty_iff_eq_empty.mp h))
