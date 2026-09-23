/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import Main

/-!
# Main results and axiom report

This file lists the headline theorems of the library, the ones in the *Main results* table of
the README, and records for each of them the axioms on which its proof depends. Every one of
them uses only Lean's three standard axioms: propositional extensionality (`propext`), the axiom
of choice (`Classical.choice`) and quotient soundness (`Quot.sound`). In particular no proof uses
`sorry` (which would appear as the axiom `sorryAx`) or any axiom introduced by this project.

The report is checked, not just printed. Each `#print axioms` command is wrapped in
`#guard_msgs`, which fails the build if the printed list of axioms differs from the one recorded
in the docstring above it. The file is part of the library, so continuous integration checks the
report on every push. The option `whitespace := lax` only makes the comparison insensitive to
the line breaks Lean inserts in long output.

The statements themselves are in the linked modules and in the API documentation at
<https://bjbraams.github.io/lean-LCS/docs/>.
-/

-- Barrelled spaces: every barrel is a neighbourhood of zero.
/--
info: 'barrelledSpace_iff_forall_isBarrel_mem_nhds' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms barrelledSpace_iff_forall_isBarrel_mem_nhds

-- Closed graph theorem, barrelled domain and complete first-countable codomain.
/--
info: 'LinearMap.continuous_of_isClosed_graph_of_barrelledSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.continuous_of_isClosed_graph_of_barrelledSpace

-- Open mapping theorem, complete first-countable domain and barrelled codomain.
/--
info: 'ContinuousLinearMap.isOpenMap_of_barrelledSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousLinearMap.isOpenMap_of_barrelledSpace

-- Pták's closed graph theorem.
/--
info: 'LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace

-- Pták's open mapping theorem.
/--
info: 'ContinuousLinearMap.isOpenMap_of_ptakSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousLinearMap.isOpenMap_of_ptakSpace

-- De Wilde's closed graph theorem.
/--
info: 'LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace

-- De Wilde's open mapping theorem.
/--
info: 'LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace

-- Bipolar theorem.
/--
info: 'StrongDual.bipolar_eq_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StrongDual.bipolar_eq_self

-- Alaoglu–Bourbaki theorem.
/--
info: 'WeakDual.isCompact_polar_of_mem_nhds' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms WeakDual.isCompact_polar_of_mem_nhds

-- Mackey's theorem: weakly bounded sets are bounded.
/--
info: 'Bornology.isVonNBounded_iff_forall_strongDual' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bornology.isVonNBounded_iff_forall_strongDual

-- Mackey–Arens theorem.
/--
info: 'LinearMap.isCompatibleTopology_iff_mackeyTopology_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.isCompatibleTopology_iff_mackeyTopology_le

-- Krein–Šmulian theorem.
/--
info: 'StrongDual.isClosed_of_isAlmostWeakStarClosed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StrongDual.isClosed_of_isAlmostWeakStarClosed

-- Grothendieck's completeness theorem.
/--
info: 'StrongDual.completeSpace_iff_forall_exists_eq_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StrongDual.completeSpace_iff_forall_exists_eq_apply

-- Reflexive if and only if semi-reflexive and barrelled.
/--
info: 'reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace

-- The strong dual of a bornological space is complete.
/--
info: 'BornologicalSpace.completeSpace_strongDual' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BornologicalSpace.completeSpace_strongDual

-- Dieudonné–Schwartz theorem.
/--
info: 'IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded

-- Completeness of countable strict inductive limits.
/--
info: 'IsStrictInductiveLimit.completeSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsStrictInductiveLimit.completeSpace

-- Milman's converse to the Krein–Milman theorem.
/--
info: 'IsCompact.extremePoints_closure_convexHull_subset_closure' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsCompact.extremePoints_closure_convexHull_subset_closure

-- Fréchet spaces are ultrabornological.
/--
info: 'UltrabornologicalSpace.of_completeSpace_firstCountableTopology' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UltrabornologicalSpace.of_completeSpace_firstCountableTopology

-- Fréchet spaces are strictly webbed.
/--
info: 'StrictlyWebbedSpace.of_completeSpace_firstCountableTopology' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StrictlyWebbedSpace.of_completeSpace_firstCountableTopology
