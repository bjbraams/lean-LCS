/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.BanachDisk
public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.BarrelledDual
public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.BornologicalUltrabornological
public import LocallyConvexSpaces.ClosedGraph
public import LocallyConvexSpaces.CompactConvergenceDual
public import LocallyConvexSpaces.CompactHull
public import LocallyConvexSpaces.CompatibleTopologies
public import LocallyConvexSpaces.Completion
public import LocallyConvexSpaces.CountableSeminorms
public import LocallyConvexSpaces.DirectSum
public import LocallyConvexSpaces.DualCompleteness
public import LocallyConvexSpaces.DualityConstructions
public import LocallyConvexSpaces.FastConvergence
public import LocallyConvexSpaces.FinalTopology
public import LocallyConvexSpaces.FinestTopology
public import LocallyConvexSpaces.FrechetUltrabornological
public import LocallyConvexSpaces.GrothendieckApproximation
public import LocallyConvexSpaces.GrothendieckCompleteness
public import LocallyConvexSpaces.GrothendieckCompletion
public import LocallyConvexSpaces.GrothendieckDualCompleteness
public import LocallyConvexSpaces.KreinSmulian
public import LocallyConvexSpaces.MackeyArens
public import LocallyConvexSpaces.MackeyBounded
public import LocallyConvexSpaces.Milman
public import LocallyConvexSpaces.OpenMapping
public import LocallyConvexSpaces.PairingTopology
public import LocallyConvexSpaces.PolarCalculus
public import LocallyConvexSpaces.PolarTopology
public import LocallyConvexSpaces.Ptak
public import LocallyConvexSpaces.ProjectiveLimit
public import LocallyConvexSpaces.QuasiBarrelled
public import LocallyConvexSpaces.Quotient
public import LocallyConvexSpaces.QuotientBornological
public import LocallyConvexSpaces.LimitPermanence
public import LocallyConvexSpaces.ReflexivePermanence
public import LocallyConvexSpaces.MontelPermanence
public import LocallyConvexSpaces.MontelDual
public import LocallyConvexSpaces.StrongDualProduct
public import LocallyConvexSpaces.Reflexive
public import LocallyConvexSpaces.StrictInductiveLimit
public import LocallyConvexSpaces.StrongDualBanachDisk
public import LocallyConvexSpaces.StrongDualBounded
public import LocallyConvexSpaces.SchwartzDual
public import LocallyConvexSpaces.TestFunctionBornological
public import LocallyConvexSpaces.TestFunctionTopology
public import LocallyConvexSpaces.Transpose
public import LocallyConvexSpaces.UltrabornologicalBanachDisk
public import LocallyConvexSpaces.UltrabornologicalCompactDisk
public import MathlibExtras
public import TopologicalGroups
public import TopologicalVectorSpaces

/-!
# Locally convex spaces

Umbrella module for the LCS core and its general prerequisites. It imports the
`MathlibExtras`, `TopologicalGroups`, and `TopologicalVectorSpaces` layers and the
LCS modules below. Webbed-space theory is a separate extension, imported by `LeanLCS`.
Individual LCS modules import only their specific prerequisites.

## General infrastructure

* `LocallyConvexSpaces.ReflexivePermanence`: semi-reflexivity and reflexivity under products,
  closed subspaces with the appropriate hypotheses, retracts, and bounded-lifting quotients.
* `LocallyConvexSpaces.MontelPermanence` and `LocallyConvexSpaces.MontelDual`: permanence of
  the Heine–Borel property and the Montel property of the strong dual.
* `LocallyConvexSpaces.LimitPermanence`: projective and countable strict inductive limits.
* `LocallyConvexSpaces.StrongDualProduct`: finite coordinate support of strongly bounded
  families of functionals, and quasi-barrelledness of products.
* `LocallyConvexSpaces.ProjectiveLimit`: representation of completions and complete spaces
  as projective limits of local Banach spaces, including the countable Fréchet case.
* `LocallyConvexSpaces.DualityConstructions`: weak-* quotient-dual identifications,
  complemented-subspace duality, and strong-dual identifications under bounded lifting.
* `MathlibExtras`: sequence and Baire-tree lemmas, finite-sum and geometric estimates,
  convex hulls and compactness, algebraic polars, and linear-map constructions.
* `TopologicalGroups`: neighbourhoods, completions, convergent products and series,
  and nearly open closed relations.
* `TopologicalVectorSpaces`: balanced and bounded sets, gauge and countable-seminorm
  results, completions, quotients, polar identities, and topological linear-map lemmas.

## Basic notions

* `LocallyConvexSpaces.Basic`: in a real or complex locally convex space the neighbourhoods of
  zero that are convex over `ℝ` and balanced over `𝕜` form a basis of neighbourhoods of zero.

## Constructions

* `LocallyConvexSpaces.CountableSeminorms`: a first-countable locally convex space is defined
  by a sequence of seminorms.
* `LocallyConvexSpaces.Quotient`: quotients of locally convex spaces are locally convex;
  quotients of barrelled spaces are barrelled; quotients of polynormable spaces are
  polynormable. The quotient-seminorm API is imported from
  `TopologicalVectorSpaces.QuotientSeminorm`.
* `LocallyConvexSpaces.FinalTopology`: the final (inductive limit) locally convex topology for a
  family of linear maps, its universal property, and its barrelledness.

* `LocallyConvexSpaces.FinestTopology`: the finest locally convex topology on finitely
  supported families, its universal property, Hausdorffness, and failure of first countability.
* `LocallyConvexSpaces.DirectSum`: locally convex direct sums: universal property, continuity
  of injections and projections, embedded summands, Hausdorffness.
* `LocallyConvexSpaces.StrictInductiveLimit`: the extension lemma for convex balanced
  neighbourhoods along a linear embedding; in a strict inductive limit every step is
  topologically embedded and, if the steps are closed in one another, closed; Hausdorffness;
  the Dieudonné–Schwartz theorem, including boundedness in the containing step; full
  completeness of countable strict inductive limits of complete locally convex spaces.
* `LocallyConvexSpaces.TestFunctionTopology`: Mathlib's topology on test functions is a final
  locally convex topology.
* `LocallyConvexSpaces.TestFunctionBornological`: test-function spaces are bornological,
  their bounded linear maps are continuous, and their real and complex strong duals are complete.
* `LocallyConvexSpaces.SchwartzDual`: the real and complex strong duals of Schwartz spaces
  are complete for uniform convergence on bounded sets.

## Barrelled and bornological spaces

* `LocallyConvexSpaces.Barrel`: barrels, their correspondence with lower semicontinuous
  seminorms, and the characterization of barrelled spaces as the spaces in which every barrel
  is a neighbourhood of zero. Near continuity and near openness of linear maps from, respectively
  onto, a barrelled space.

* `LocallyConvexSpaces.Bornological`: bornivorous sets; bornological spaces (first-countable
  spaces are bornological; locally bounded linear maps are continuous; inductive limits);
  ultrabornological spaces (seminorms continuous along all maps from Banach spaces, equivalently
  inductive limits of Banach spaces).
* `LocallyConvexSpaces.BanachDisk`: the seminormed spaces `E_B` spanned by a set `B`
  (`DiskSpace 𝕜 B`), continuity of their inclusion for bounded `B`, completeness for complete
  disks; Banach disks.
* `LocallyConvexSpaces.BornologicalUltrabornological`: a bornological space is the inductive
  limit of the spaces `E_B` of its closed bounded disks; quasi-complete bornological spaces are
  ultrabornological.
* `LocallyConvexSpaces.FrechetUltrabornological`: Fréchet spaces are ultrabornological, through
  the maps `ℓ¹(ℕ, 𝕜) → E` defined by the sequences that tend to zero.
* `LocallyConvexSpaces.UltrabornologicalBanachDisk`: the image of the unit ball of a Banach space
  under a continuous linear map is a Banach disk; a locally convex space is ultrabornological if
  and only if the seminorms bounded on its Banach disks are continuous, and if and only if it is
  the locally convex hull of the spaces `E_B` of its Banach disks; linear maps bounded on the
  Banach disks are continuous.
* `LocallyConvexSpaces.UltrabornologicalCompactDisk`: the same with the compact disks.
* `LocallyConvexSpaces.QuotientBornological`: quotients of bornological and of ultrabornological
  spaces are of the same kind.
* `LocallyConvexSpaces.FastConvergence`: fast convergent sequences; a Hausdorff locally convex space
  is ultrabornological if and only if the convex balanced sets that absorb the fast convergent null
  sequences are neighbourhoods of zero; in a Fréchet space every null sequence is fast convergent.

## Duality

* `LocallyConvexSpaces.PolarCalculus`: convex and balanced hulls of bounded sets are bounded;
  polars of closures, hulls and scalar multiples.
* `LocallyConvexSpaces.MackeyBounded`: Mackey's theorem that weakly bounded sets are bounded.

* `LocallyConvexSpaces.Bipolar`: the bipolar theorem, for a locally convex space and its dual and
  for a bilinear pairing.
* `LocallyConvexSpaces.AlaogluBourbaki`: polars of neighbourhoods of zero are equicontinuous and
  weak-* compact; equicontinuous sets lie in such polars.
* `LocallyConvexSpaces.PolarTopology`: topologies of uniform convergence on the dual described
  by polars; the strong dual and the topology of compact convergence.
* `LocallyConvexSpaces.CompactHull`: in a quasi-complete locally convex space a compact set lies in
  a compact convex balanced set.
* `LocallyConvexSpaces.Milman`: extreme points of a compact closed convex hull belong to the
  closure of the generating set; the closure of the extreme points is the least closed
  generating subset of a compact convex set.
* `LocallyConvexSpaces.CompactConvergenceDual`: functionals on the dual that are continuous for
  compact convergence are evaluations at points of a quasi-complete locally convex space.
* `LocallyConvexSpaces.Transpose`: transposes and annihilators: `ker fᵗ = (range f)^⊥`, the
  closure of the range, dense range and injectivity of the transpose; the duals of subspaces and
  of quotients.
* `LocallyConvexSpaces.Completion`: the completion of a locally convex space is locally convex. The
  general completion and continuous-dual API is imported from `TopologicalVectorSpaces.Completion`.
* `LocallyConvexSpaces.PairingTopology`: polar topologies on `E` for a pairing of `E` and `F`.
* `LocallyConvexSpaces.MackeyArens`: the Mackey topology of a pairing and the Mackey–Arens
  theorem.
* `LocallyConvexSpaces.BarrelledDual`: a locally convex space is barrelled if and only if the
  weak-* bounded subsets of its dual are equicontinuous.
* `LocallyConvexSpaces.CompatibleTopologies`: topologies with the same dual have the same closed
  convex sets and the same bounded sets.
* `LocallyConvexSpaces.StrongDualBounded`: polars of bornivorous sets are strongly bounded.
* `LocallyConvexSpaces.Reflexive`: the bidual, semi-reflexive and reflexive spaces;
  semi-reflexivity as compatibility of the strong topology of the dual, and as weak relative
  compactness of the bounded sets.
* `LocallyConvexSpaces.QuasiBarrelled`: quasi-barrelled spaces and their duals; reflexive if and
  only if semi-reflexive and barrelled; barrelled Montel spaces are reflexive; the strong
  dual of a reflexive space is reflexive.
* `LocallyConvexSpaces.GrothendieckApproximation`, `LocallyConvexSpaces.GrothendieckCompleteness`:
  Grothendieck's completeness criterion in both directions.
* `LocallyConvexSpaces.GrothendieckCompletion`: the completion as linear forms on the dual
  weak-* continuous on equicontinuous sets, with uniform convergence on those sets.
* `LocallyConvexSpaces.GrothendieckDualCompleteness`: the general uniform-convergence
  completeness criterion for the dual and its representation formulation for polar topologies.
* `LocallyConvexSpaces.DualCompleteness`: semi-reflexive spaces and strong duals of
  quasi-barrelled spaces are quasi-complete; strong duals of bornological spaces are complete.
* `LocallyConvexSpaces.KreinSmulian`: almost weak-* closed sets; the Banach–Dieudonné and
  Krein–Šmulian theorems.

## Open mapping and closed graph theorems

* `TopologicalGroups.NearlyOpen`: the successive approximation argument, for commutative
  topological groups: a closed relation on a complete first-countable group that is nearly open
  is open; hence a nearly open homomorphism with closed graph is open, and a nearly continuous
  homomorphism with closed graph is continuous.
* `LocallyConvexSpaces.ClosedGraph`: the closed graph theorem for a linear map from a barrelled
  space to a Fréchet space.
* `LocallyConvexSpaces.OpenMapping`: the open mapping theorem for a linear map from a Fréchet
  space onto a barrelled space.
* `TopologicalGroups.Series`: series in topological groups; in a first-countable commutative
  topological group, points of the closure of `S 0` are sums of series `∑ x k` with
  `x k ∈ S k`, when the closures of the `S k` are neighbourhoods of zero.
* `LocallyConvexSpaces.StrongDualBanachDisk`: the polar of a neighbourhood of zero is a Banach
  disk in the strong dual.
* `LocallyConvexSpaces.Ptak`: Pták and infra-Pták spaces; Fréchet spaces are Pták spaces; Pták's
  closed graph theorem for a barrelled domain and an infra-Pták codomain, and Pták's open mapping
  theorem for a Pták domain and a barrelled codomain.
-/

-- Keep the LCS core and its transitive prerequisites independent of webbed-space theory.
assert_not_imported WebbedSpaces.Basic
