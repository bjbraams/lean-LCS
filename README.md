# lean-LCS

[![CI](https://github.com/bjbraams/lean-LCS/actions/workflows/ci.yml/badge.svg)](https://github.com/bjbraams/lean-LCS/actions/workflows/ci.yml)
[![Documentation](https://github.com/bjbraams/lean-LCS/actions/workflows/docs.yml/badge.svg)](https://bjbraams.github.io/lean-LCS/docs/)

**API documentation:** <https://bjbraams.github.io/lean-LCS/docs/>

A Lean 4 formalization of locally convex topological vector spaces, their duality and
completeness theory, and closed graph and open mapping theorems, built on Mathlib.
The project develops results and interfaces intended for contribution to Mathlib.

The mathematical focus is locally convex spaces over the real or complex numbers.
Supporting results use more general scalar fields, rings, modules, and topological
groups where appropriate. General topological vector space and group theory serves the
LCS development; the project does not aim to cover those subjects comprehensively.
Banach-space theory is used from Mathlib, and specialized non-archimedean theory is
outside the scope.

The library contains no `sorry` placeholders and no project-specific axioms. Continuous
integration builds it on every push with warnings treated as errors, which includes Lean's
warning for a `sorry`.

## Main results

A selection of headline theorems, with their Lean names. Spaces are real or complex
locally convex spaces unless stated otherwise.

| Result | Lean name | File |
| --- | --- | --- |
| Barrelled spaces: every barrel is a neighbourhood of zero | `barrelledSpace_iff_forall_isBarrel_mem_nhds` | [Barrel](LocallyConvexSpaces/Barrel.lean) |
| Closed graph theorem, barrelled domain and complete first-countable codomain | `LinearMap.continuous_of_isClosed_graph_of_barrelledSpace` | [ClosedGraph](LocallyConvexSpaces/ClosedGraph.lean) |
| Open mapping theorem, complete first-countable domain and barrelled codomain | `ContinuousLinearMap.isOpenMap_of_barrelledSpace` | [OpenMapping](LocallyConvexSpaces/OpenMapping.lean) |
| Pták's closed graph and open mapping theorems | `LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace`, `ContinuousLinearMap.isOpenMap_of_ptakSpace` | [Ptak](LocallyConvexSpaces/Ptak.lean) |
| De Wilde's closed graph and open mapping theorems | `LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace`, `LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace` | [DeWilde](WebbedSpaces/DeWilde) |
| Bipolar theorem | `StrongDual.bipolar_eq_self` | [Bipolar](LocallyConvexSpaces/Bipolar.lean) |
| Alaoglu–Bourbaki theorem | `WeakDual.isCompact_polar_of_mem_nhds` | [AlaogluBourbaki](LocallyConvexSpaces/AlaogluBourbaki.lean) |
| Mackey's theorem: weakly bounded sets are bounded | `Bornology.isVonNBounded_iff_forall_strongDual` | [MackeyBounded](LocallyConvexSpaces/MackeyBounded.lean) |
| Mackey–Arens theorem | `LinearMap.isCompatibleTopology_iff_mackeyTopology_le` | [MackeyArens](LocallyConvexSpaces/MackeyArens.lean) |
| Krein–Šmulian theorem | `StrongDual.isClosed_of_isAlmostWeakStarClosed` | [KreinSmulian](LocallyConvexSpaces/KreinSmulian.lean) |
| Grothendieck's completeness theorem | `StrongDual.completeSpace_iff_forall_exists_eq_apply` | [GrothendieckCompleteness](LocallyConvexSpaces/GrothendieckCompleteness.lean) |
| Reflexive if and only if semi-reflexive and barrelled | `reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace` | [QuasiBarrelled](LocallyConvexSpaces/QuasiBarrelled.lean) |
| The strong dual of a bornological space is complete | `BornologicalSpace.completeSpace_strongDual` | [DualCompleteness](LocallyConvexSpaces/DualCompleteness.lean) |
| Dieudonné–Schwartz theorem; completeness of strict inductive limits | `IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded`, `IsStrictInductiveLimit.completeSpace` | [StrictInductiveLimit](LocallyConvexSpaces/StrictInductiveLimit.lean) |
| Milman's converse to the Krein–Milman theorem (real spaces) | `IsCompact.extremePoints_closure_convexHull_subset_closure` | [Milman](LocallyConvexSpaces/Milman.lean) |
| Fréchet spaces are ultrabornological and strictly webbed | `UltrabornologicalSpace.of_completeSpace_firstCountableTopology`, `StrictlyWebbedSpace.of_completeSpace_firstCountableTopology` | [FrechetUltrabornological](LocallyConvexSpaces/FrechetUltrabornological.lean), [Frechet](WebbedSpaces/Frechet.lean) |

[MainResults.lean](MainResults.lean) lists these theorems with an axiom report: each depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The report is
checked by `#guard_msgs`, so continuous integration fails if it ever changes.

## Mathematical content

### Constructions and classes of spaces

The library develops convex balanced neighbourhood bases, quotient seminorms, locally
convex quotients, direct sums, final locally convex topologies, and the finest locally
convex topology on finitely supported families. It treats barrelled, quasi-barrelled,
bornological, ultrabornological, semi-reflexive, reflexive, Montel, Pták, and infra-Pták
spaces, together with their characterizations and permanence properties.

Countable strict inductive limits with closed transition ranges have the expected
bounded-set property: every bounded set is contained and bounded in one step. The
library proves completeness for strict inductive limits of complete Hausdorff locally
convex steps under its embedding and final-topology hypotheses.

Starting points: [Quotient](LocallyConvexSpaces/Quotient.lean),
[FinalTopology](LocallyConvexSpaces/FinalTopology.lean),
[Bornological](LocallyConvexSpaces/Bornological.lean), and
[StrictInductiveLimit](LocallyConvexSpaces/StrictInductiveLimit.lean).

### Duality and convexity

The duality development includes polar calculus, the bipolar theorem, the
Alaoglu–Bourbaki theorem, compatible topologies on dual pairs, the Mackey topology,
the Mackey–Arens theorem, and Mackey's boundedness theorem. It also provides transposes,
annihilator identities, and dual identifications for quotients, complemented subspaces,
and completions.

Weak-* and strong topological identifications are distinguished. Strong-dual
identifications for quotients and completions have an explicit sufficient condition:
each bounded target set must lie in the closure of the image of a bounded source set.

Milman's converse to Krein–Milman is proved: the extreme points of a compact closed
convex hull lie in the closure of the generating set. Together with Mathlib's
Krein–Milman theorem, this characterizes the closed generating subsets of a compact
convex set.

Starting points: [AlaogluBourbaki](LocallyConvexSpaces/AlaogluBourbaki.lean),
[MackeyArens](LocallyConvexSpaces/MackeyArens.lean),
[DualityConstructions](LocallyConvexSpaces/DualityConstructions.lean), and
[Milman](LocallyConvexSpaces/Milman.lean).

### Completeness and reflexivity

The completion of a locally convex space is locally convex. A directed defining
family of seminorms represents its separated completion as a projective limit of
local Banach spaces. First-countable spaces admit countable versions of this
representation.

Grothendieck's completeness criterion and its dual model of the completion are proved,
along with completeness criteria for uniform convergence on families of sets and for
dual pairs. The library also treats Banach–Dieudonné and Krein–Šmulian.

The strong dual of a bornological space is complete, and the strong dual of a
quasi-barrelled space is quasi-complete in the stated real/complex settings. The strong
dual of a reflexive locally convex space is reflexive. Permanence results cover
products, retracts, suitable subspaces and quotients, and strict inductive limits,
with separation, barrelledness, and bounded-lifting hypotheses stated explicitly.

Starting points: [ProjectiveLimit](LocallyConvexSpaces/ProjectiveLimit.lean),
[GrothendieckCompleteness](LocallyConvexSpaces/GrothendieckCompleteness.lean),
[GrothendieckCompletion](LocallyConvexSpaces/GrothendieckCompletion.lean),
[DualCompleteness](LocallyConvexSpaces/DualCompleteness.lean), and
[ReflexivePermanence](LocallyConvexSpaces/ReflexivePermanence.lean).

### Mapping theorems and webbed spaces

The LCS core contains closed graph and open mapping theorems for barrelled spaces
and complete first-countable locally convex spaces, together with Pták's mapping
theorems. Their successive-approximation foundation is a theorem about nearly open
closed relations on commutative topological groups.

The webbed-space extension develops completing and strict webs, subspaces, quotients,
countable products and inductive constructions, and criteria for webbedness. Fréchet
spaces are strictly webbed. De Wilde's theory includes closed graph and open mapping
theorems involving ultrabornological spaces, linear relations and partially defined
maps, localization and factorization, and range and complement theorems.

Starting points: [NearlyOpen](TopologicalGroups/NearlyOpen.lean),
[ClosedGraph](LocallyConvexSpaces/ClosedGraph.lean),
[Ptak](LocallyConvexSpaces/Ptak.lean),
[WebbedSpaces.Basic](WebbedSpaces/Basic.lean), and
[DeWilde.ClosedGraph](WebbedSpaces/DeWilde/ClosedGraph.lean).

### Concrete applications and supporting interfaces

Test-function spaces are bornological, and their real and complex strong duals are
complete. The strong duals of Mathlib's Schwartz spaces of rapidly decreasing smooth
functions are also complete. These conclusions concern the strong topology of uniform
convergence on bounded sets.

The support library provides quotient-seminorm universal properties, bounded maps
between seminorm completions, summability controlled by arbitrary defining seminorm
families, continuity of complex scalar multiplication from the real action, and
compactness of convex joins.

Starting points: [TestFunctionBornological](LocallyConvexSpaces/TestFunctionBornological.lean),
[SchwartzDual](LocallyConvexSpaces/SchwartzDual.lean),
[SeminormCompletion](TopologicalVectorSpaces/SeminormCompletion.lean), and
[SeminormSummability](TopologicalVectorSpaces/SeminormSummability.lean).

## Mathematical conventions

- **Scalars and convexity.** The principal LCS theory uses `RCLike` scalars, encompassing
  the real and complex numbers. Convexity is over the reals; balancedness is with respect
  to the chosen scalar field. A disk is a convex balanced set.
- **Boundedness.** Bounded sets are von Neumann bounded: every neighbourhood of zero
  absorbs them.
- **Separation.** Hausdorffness is an explicit hypothesis where required. The term
  *Fréchet space* means a Hausdorff, complete, metrizable locally convex space. The code
  uses the corresponding individual hypotheses rather than a dedicated Fréchet class.
- **Completeness.** Completeness refers to the additive uniformity. Quasi-completeness
  means completeness of closed bounded subsets. Completions are separated completions.
- **Duality.** Pairings are bilinear, including over the complex numbers. Polars are
  absolute polars, defined by the bound $|\langle x,y\rangle|\leq 1$. The weak-* topology
  is pointwise convergence; the strong dual topology is uniform convergence on bounded
  sets.
- **Reflexivity.** Semi-reflexivity means surjectivity of the canonical map into the
  strong bidual. Reflexivity additionally means that this map induces the original
  topology. Hausdorffness is not included in either class.
- **Montel spaces.** Mathlib's `MontelSpace` asserts that closed bounded sets are compact.
  Barrelledness is a separate assumption when the classical barrelled Montel convention
  is needed.
- **Webs and series.** Convergence in the definition of a web means convergence of
  the sequence of partial sums in its given order. Lean's `Summable` instead concerns
  the net of finite subsums. The two notions are used distinctly.

## Source organization

| Directory | Scope |
| --- | --- |
| [MathlibExtras](MathlibExtras.lean) | General additions in analysis, linear algebra, and topology, organized by subject. |
| [TopologicalGroups](TopologicalGroups.lean) | Neighbourhoods, completions, products and series, and nearly open closed relations. |
| [TopologicalVectorSpaces](TopologicalVectorSpaces.lean) | Balanced and bounded sets, gauges, seminorms, quotients, completions, scalar actions, and linear relations. |
| [LocallyConvexSpaces](LocallyConvexSpaces.lean) | LCS constructions, space classes, duality, completeness, permanence, applications, and web-independent mapping theorems. |
| [WebbedSpaces](WebbedSpaces.lean) | Webs and their constructions; De Wilde's theorems are in `WebbedSpaces/DeWilde/`. |

Imports respect the order

```text
MathlibExtras < TopologicalGroups < TopologicalVectorSpaces < LocallyConvexSpaces < WebbedSpaces
```

A module may use its own layer and any earlier layer. The LCS core has no direct or
transitive dependency on webbed-space theory. Basic web constructions use only their
actual prerequisites and do not impose local convexity merely by their location.

Directories determine import paths. Declarations use mathematical namespaces such as
`Seminorm`, `Submodule`, `StrongDual`, and `UniformSpace.Completion`.

## Building

The project pins **Lean 4.34.0** in [lean-toolchain](lean-toolchain) and **Mathlib
v4.34.0** in [lakefile.toml](lakefile.toml), with resolved dependencies recorded in
[lake-manifest.json](lake-manifest.json). Install Lean through
[elan](https://github.com/leanprover/elan), which selects the pinned toolchain
automatically. Then:

```sh
git clone https://github.com/bjbraams/lean-LCS.git
cd lean-LCS
lake exe cache get   # download precompiled Mathlib files
lake build           # build the complete project
```

The first build of the project itself takes several minutes; afterwards `lake build`
rebuilds only what changed. A single module and its prerequisites can be built with, for
example, `lake build LocallyConvexSpaces.Reflexive`. The same build, with warnings treated
as errors (`lake build --wfail`), runs in continuous integration on every push.

## Using the library

Import the LCS core and its supporting layers with:

```lean
import LocallyConvexSpaces
```

For the complete project, including webbed spaces and De Wilde's theorems, use:

```lean
import LeanLCS
```

Individual modules can be imported directly to keep prerequisites small. For example:

```lean
import TopologicalVectorSpaces.SeminormSummability

#check WithSeminorms.summable_of_forall_summable_seminorm
```

Each source file has a module docstring describing its scope and principal results;
declaration docstrings describe the individual interfaces. The subject umbrella files
linked above provide broader indexes.

### In another project

Add the repository as a dependency in the other project's `lakefile.toml`. The Lake package
is named `LeanLCS`:

```toml
[[require]]
name = "LeanLCS"
git = "https://github.com/bjbraams/lean-LCS.git"
rev = "main"
```

The other project must use the same Lean and Mathlib versions.

## Conventions for contributions

The code follows Mathlib's naming, documentation and style conventions. Every file is a
module with a module docstring, every definition, theorem and structure field has a
docstring, and lines are at most 100 characters. General supporting lemmas belong in the
lowest layer that can state them, and assumptions are stated at the appropriate
mathematical generality. Statements that duplicate material in an open Mathlib pull
request carry a note beside the declaration naming the pull request.

Module headers cite the mathematical literature by keys in [references.bib](references.bib).
Sources include Bourbaki, Schaefer–Wolff, Köthe, Narici–Beckenstein, Casselman, and
De Wilde.

## License

Released under the [Apache License 2.0](LICENSE).
