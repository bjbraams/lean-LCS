/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TopologicalVectorSpaces.Basic
public import TopologicalVectorSpaces.Completion
public import TopologicalVectorSpaces.CountableSeminorms
public import TopologicalVectorSpaces.Gauge
public import TopologicalVectorSpaces.LinearMapFiniteSum
public import TopologicalVectorSpaces.LinearMapGraph
public import TopologicalVectorSpaces.LinearRelation
public import TopologicalVectorSpaces.PolarCalculus
public import TopologicalVectorSpaces.Quotient
public import TopologicalVectorSpaces.QuotientSeminorm
public import TopologicalVectorSpaces.ScalarRestriction
public import TopologicalVectorSpaces.SeminormSummability
public import TopologicalVectorSpaces.TestFunction
public import TopologicalVectorSpaces.SeminormCompletion

/-!
# Topological vector spaces

This umbrella imports general scalar-action, boundedness, gauge, polynormability, completion
(including local Banach spaces of seminorms), quotient, and polar results, together with topological
graph identities and finite sums of linear maps, and images under linear relations. Webbed-space
theory is a separate extension. No project LCS or webbed-space module is imported.

Quotient seminorms have a universal property, and seminorm-bounded linear maps extend
functorially to the associated completions. Summability can be checked by absolute
summability in an arbitrary defining family of seminorms. The scalar-restriction criterion
constructs a continuous complex action from the real action and multiplication by the
imaginary unit; the test-function application uses this criterion.
-/
