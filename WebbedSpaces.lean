/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import WebbedSpaces.Baire
public import WebbedSpaces.Basic
public import WebbedSpaces.BoundedSets
public import WebbedSpaces.Criteria
public import WebbedSpaces.DeWilde.ClosedGraph
public import WebbedSpaces.DeWilde.Codimension
public import WebbedSpaces.DeWilde.Complement
public import WebbedSpaces.DeWilde.Kato
public import WebbedSpaces.DeWilde.Localization
public import WebbedSpaces.DeWilde.LocalizationCompleting
public import WebbedSpaces.DeWilde.OpenMapping
public import WebbedSpaces.DeWilde.Relation
public import WebbedSpaces.Frechet
public import WebbedSpaces.Hereditary
public import WebbedSpaces.InductiveLimit
public import WebbedSpaces.LinearHull
public import WebbedSpaces.Product
public import WebbedSpaces.StrongDualHull

/-!
# Webbed spaces and De Wilde's theorems

This umbrella imports completing and strict webs, their hereditary and product constructions,
criteria and examples of webbed spaces, and De Wilde's mapping and localization theorems.
The basic web constructions use topological vector spaces; the applications import the LCS
results they need. The LCS core and its general prerequisites do not import this extension.

## Webs, constructions, and examples

* `WebbedSpaces.Basic`: webs, completing and strict webs, webbed and strictly webbed spaces
  (De Wilde), following Köthe II §35.1; the first structural lemma on strands.
* `WebbedSpaces.Frechet`: the web of a sequence of seminorms; Fréchet spaces are
  strictly webbed.
* `WebbedSpaces.Hereditary`: spaces with an inducing linear map, with sequentially
  closed range, into a webbed space (in particular sequentially closed subspaces), sequentially
  continuous images, countable unions of such images, and quotients of webbed and strictly
  webbed spaces.
* `WebbedSpaces.Product`: countable products, countable projective limits and binary
  products of webbed and strictly webbed spaces.
* `WebbedSpaces.InductiveLimit`: countable locally convex hulls, in particular
  countable inductive limits (LF spaces) and countable locally convex direct sums of webbed and
  strictly webbed spaces.
* `WebbedSpaces.BoundedSets`: a complete space covered by a sequence of closed bounded
  disks is strictly webbed; the strong dual of a first-countable topological vector space is
  strictly webbed.
* `WebbedSpaces.Criteria`: Köthe's criteria for completing and strict webs; a locally
  convex space that is a countable union of Banach disks is strictly webbed.
* `WebbedSpaces.StrongDualHull`: the strong dual of a countable locally convex hull of
  first-countable spaces, in particular of an LF space, is strictly webbed.
* `WebbedSpaces.LinearHull`: the linear hull of a set of a strict web is strictly
  webbed.
* `WebbedSpaces.Baire`: a Hausdorff strictly webbed Baire space is
  first-countable and complete; a webbed Baire space is first-countable.

## De Wilde theorems

* `WebbedSpaces.DeWilde.Relation`: De Wilde's theorem for a (sequentially) closed linear
  relation between a webbed locally convex space and a Baire-like or ultrabornological space,
  the common source of the closed graph and open mapping theorems.
* `WebbedSpaces.DeWilde.ClosedGraph`: De Wilde's closed graph theorems: sequentially
  closed graph and ultrabornological or first-countable Baire domain; closed graph and Baire
  domain, non-meagre domain of a partially defined map, or locally convex hull of Baire spaces.
* `WebbedSpaces.DeWilde.OpenMapping`: De Wilde's open mapping theorems, for everywhere and
  for partially defined maps from a webbed locally convex space, with the same range of
  hypotheses.
* `WebbedSpaces.DeWilde.Localization`: De Wilde's localization theorem for a map with
  sequentially closed graph from a Fréchet space into a strictly webbed space, and Grothendieck's
  factorization theorem for maps into LF spaces.
* `WebbedSpaces.DeWilde.LocalizationCompleting`: the localization theorem for completing
  webs of convex balanced sets, with the closures of the sets of the web.
* `WebbedSpaces.DeWilde.Kato`: De Wilde's open mapping theorem for a sequentially closed
  map whose range has a webbed algebraic complement (Kato's theorem and its generalizations).
* `WebbedSpaces.DeWilde.Codimension`: the finest locally convex topology on `ι →₀ 𝕜`; a
  sequentially closed map whose range has finite or countable codimension has a closed range,
  is open onto it, and every algebraic complement of the range is a topological complement
  (Kato's theorem in De Wilde's form); the codimension is finite if the codomain is metrizable.
* `WebbedSpaces.DeWilde.Complement`: algebraic complements that are webbed, or
  sequentially closed in a webbed space, are topological complements in a Hausdorff
  ultrabornological space.

## Conventions and references

The definition module `WebbedSpaces.Basic` specifies the strand indexing, real coefficients,
and convergence of partial sums used for completing and strict webs. Detailed mathematical
hypotheses and references are given in each module.

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35
* [M. De Wilde, *Closed Graph Theorems and Webbed Spaces*][dewilde1978]
-/
