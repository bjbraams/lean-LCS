/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits

/-!
# Nontrivially normed fields have a zero sequence of units

The Tau Ceti class `TauCeti.HasZeroSequenceOfUnits` asks for a sequence of units tending to zero.
In a nontrivially normed field the powers of an element `c` with `0 < ‖c‖ < 1` are such a
sequence. This makes the Baire-category results of `TauCeti.Topology.Algebra.OpenMapping.Basic`
available for topological vector spaces over such fields.

## Main statements

* `NontriviallyNormedField.toHasZeroSequenceOfUnits`: a nontrivially normed field has a zero
  sequence of units.
-/

public section

open Filter

open scoped Topology

/-- A nontrivially normed field has a sequence of units tending to zero: the powers of an element
of norm strictly between zero and one. -/
instance (priority := 100) NontriviallyNormedField.toHasZeroSequenceOfUnits
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] : TauCeti.HasZeroSequenceOfUnits 𝕜 := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  exact ⟨fun n ↦ Units.mk0 c (norm_pos_iff.mp hc0) ^ n, by
    simpa using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1⟩
