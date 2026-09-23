/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TopologicalGroups.Basic
public import TopologicalGroups.Completion
public import TopologicalGroups.NearlyOpen
public import TopologicalGroups.Series

/-!
# Topological groups

This umbrella imports neighbourhood and Baire lemmas, group completions, convergent
products and series, and the successive-approximation argument for nearly open closed
relations. Multiplicative results provide additive counterparts through `to_additive`.
These modules use general Mathlib additions but no project vector-space or LCS modules.
-/
