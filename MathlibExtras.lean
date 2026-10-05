/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import MathlibExtras.Analysis.ConvexCombinations
public import MathlibExtras.Analysis.ContDiffMapSupportedIn
public import MathlibExtras.Analysis.ConvexCompact
public import MathlibExtras.Analysis.ConvexHull
public import MathlibExtras.Analysis.Polar
public import MathlibExtras.Analysis.SeminormEstimates
public import MathlibExtras.Analysis.SpecificLimits
public import MathlibExtras.Analysis.ZeroSequenceOfUnits
public import MathlibExtras.LinearAlgebra.LinearMapFiniteSum
public import MathlibExtras.LinearAlgebra.LinearMapGraph
public import MathlibExtras.Topology.BaireTree
public import MathlibExtras.Topology.Meagre
public import MathlibExtras.Topology.Sequences
public import MathlibExtras.Topology.UniformConvergence

/-!
# General additions to Mathlib

This umbrella imports the general analysis, linear algebra, and topology additions used by this
project. They are independent of its topological-group, topological-vector-space, and
locally-convex-space modules. The subdirectories organize results by mathematical subject, and
individual files can be imported separately. Nontrivially normed fields are registered as
having a zero sequence of units, the hypothesis of Tau Ceti's Baire-category results. The
test-function helper gives first countability for fixed compact support, using Mathlib's
distribution spaces.
-/
