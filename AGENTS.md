# Project instructions

## Build topology (do not change)

- Lake root is this directory. This directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not
  repair it.
- After every Lean edit: `lake build` from the Lake root.
- For ordinary builds, use lake build > /tmp/SCV-build.log 2>&1; reuse this filename to
  preserve the existing command approval.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.
- Active work: locally convex spaces and the supporting modules described below.

## Project

The objective is to formalize basic theory of locally convex topological vector spaces (LCS)
using Mathlib. The work is meant as a contribution to Mathlib.
Subdirectory References contains PDF files for several basic texts in the area of LCS. These
references provide guidance for material to be included in the formalization. See the Section
"Source material" below for more precision.

## Proof requirements

- Do not introduce axioms.
- Do not replace `sorry` with `by exact Classical.choice ...` or other logically equivalent
  escape mechanisms.
- Search Mathlib for existing results before recreating substantial theory.
- Additional lemmas are welcome when they clarify the mathematical structure.
- Preserve theorem statements unless they are false or require missing assumptions.
- If a statement appears false then mark the issue clearly before changing it.
- When new theory from a trusted source is introduced into the project then it is fine to
  use admitted (`sorry`d) statements; the proofs can come later.

## File organization

Lean code is organized into five sibling directories:

- `MathlibExtras/`: general additions to the pinned Mathlib, grouped into `Analysis/`,
  `LinearAlgebra/`, and `Topology/`. Examples include sequence and Baire-tree lemmas,
  elementary estimates, convex hulls, algebraic polars, and linear-map constructions.
- `TopologicalGroups/`: general topological-group results, including neighbourhoods,
  completions, convergent products and series, and nearly open closed relations.
- `TopologicalVectorSpaces/`: general TVS and topological-module infrastructure, including
  balanced and bounded sets, gauges, countable seminorms, completions, quotients, polar
  identities, images under linear relations, and topological properties of linear maps.
  `SeminormSummability.lean` treats arbitrary defining seminorm families;
  `CountableSeminorms.lean` includes its diagonal summability corollary and selects directed
  or monotone defining seminorm families using only a topology.
  `QuotientSeminorm.lean` includes the universal property and descent bounds.
  `SeminormCompletion.lean` constructs local normed quotients and Banach completions,
  functorial maps under seminorm bounds, and equivalences under mutual domination.
  `ScalarRestriction.lean` derives joint scalar continuity from the real action and
  multiplication by the imaginary unit; `TestFunction.lean` applies this criterion.
- `LocallyConvexSpaces/`: LCS constructions and space classes, the main duality development,
  locally convex inductive limits, and the web-independent closed-graph and open-mapping
  theorems, including Pták theory. `FinestTopology.lean` develops the finest locally convex
  topology on finitely supported families independently of its De Wilde applications.
  `ProjectiveLimit.lean` represents completions by local Banach spaces.
  `DualityConstructions.lean` treats topological duality for quotients, complemented
  subspaces, and completions, with explicit bounded-lifting hypotheses where needed.
  `ReflexivePermanence.lean`, `MontelPermanence.lean`, `MontelDual.lean`, and
  `LimitPermanence.lean` develop permanence properties; `StrongDualProduct.lean` supplies
  the finite-coordinate dual arguments for arbitrary products.
  Reflexive retracts and finite-coordinate decomposition use nontrivially normed fields;
  the general Montel bounded-cover theorem is in `MontelPermanence.lean` over a normed field.
  `TestFunctionBornological.lean` and `SchwartzDual.lean` give concrete bornological and
  strong-dual completeness applications. `Milman.lean` treats extreme points of compact
  closed convex hulls and closed generating subsets.
- `WebbedSpaces/`: completing and strict webs, hereditary and product constructions,
  webbed-space criteria and examples, and applications using the LCS core. The `DeWilde/`
  subdirectory contains De Wilde's mapping, relation, localization, and complement theorems.

Use descriptive filenames within these directories; do not prefix them with `TG` or `TVS`.
Within `WebbedSpaces`, omit redundant `Web` and `DeWilde` filename prefixes; use the
`DeWilde/` subdirectory for the latter theory.
Split general ingredients from LCS consequences when this gives independently useful imports.
Keep mathematically cohesive duality and application developments together; the absence of a
`LocallyConvexSpace` hypothesis alone does not require moving a declaration out of that layer.

Maintain the project dependency direction:

- `MathlibExtras` may import Mathlib and other `MathlibExtras` modules only.
- `TopologicalGroups` may additionally import `TopologicalGroups` modules.
- `TopologicalVectorSpaces` may additionally import `TopologicalVectorSpaces` modules.
- `LocallyConvexSpaces` may import any of the preceding layers and other LCS modules.
- `WebbedSpaces` may import any of the preceding layers and other webbed-space modules.

The first four layers, including their umbrella modules, must not import `WebbedSpaces`
directly or transitively. Basic web constructions should still use only their actual TVS
prerequisites; living in `WebbedSpaces` does not impose local-convexity hypotheses.
Preserve the `assert_not_imported WebbedSpaces.Basic` guard in `LocallyConvexSpaces.lean`.

Import specific prerequisites in implementation files, rather than entire subject umbrellas.
`MathlibExtras.lean`, `TopologicalGroups.lean`, and `TopologicalVectorSpaces.lean` are subject
umbrellas. `LocallyConvexSpaces.lean` imports the LCS core and its general prerequisites;
`WebbedSpaces.lean` imports the webbed-space and De Wilde extension. `Main.lean` imports both
and is the complete-project Lake entry module. Keep the umbrellas and Lake roots/globs in
sync when adding modules; retain the existing package and Lake root.

Directories determine import paths, not declaration namespaces. Continue to use the natural
Mathlib namespaces such as `Submodule`, `LinearMap`, `StrongDual`, and `UniformSpace.Completion`.
Use `inclusionInDoubleDual` for the canonical bidual API, including reflexivity class fields;
the older `inclusionInBidual` names remain as compatibility aliases and accessors.
Use the Hausdorff convention for the term Fréchet space. State non-Hausdorff extensions as
results for complete, first-countable locally convex spaces without adding separation assumptions.
See `PROJECT_ORGANIZATION.md` for the file-move and split map.

## Editing

- Keep changes narrowly related to the requested theorem or proof cluster.
- Preserve unrelated user changes.
- Temporary experiments may go in `Scratch.lean`, but remove that file before finishing
  unless asked to retain it.
- Do not commit changes unless explicitly requested.
- If a new Lean file is created, provide it with a documentation header section.
- If a new Lean statement (definition, theorem, lemma or other) is introduced,
  provide it with a brief docstring.
- If a statement introduced here has content that is also found in a Mathlib pull request
  that is not in the pinned Mathlib, or anywhere else outside Mathlib, leave a note in the
  Lean file next to that statement (in its docstring or a comment directly above it) that
  points to the other location: PR number, author, file and declaration name. Say whether
  the statement or proof was copied, adapted, or obtained independently, and that the copy
  is to be deleted once the PR is in the pinned Mathlib. A mention in the file header alone
  is not enough. The same applies to a proof that follows the organization of a proof
  found elsewhere.
- Files use the Lean module system: `module`, `public import`, and `public section` (or
  `public noncomputable section` when needed).
- A definition that downstream files must unfold, or about which they prove `rfl` lemmas,
  must be exposed; a `public` theorem proved by `rfl` about an unexposed definition fails
  at build time even though `lake env lean` accepts it.
- `lake env lean f.lean` uses the compiled oleans of the imports. After changing an
  upstream file, rebuild it with `lake build Module.Name` before checking dependents.
- The Namespace structure is to be decided still. For now, do what best matches Mathlib.
- Expose definitions whose formulas downstream modules need to unfold, either individually
  with `@[expose]` or in a suitably scoped exposed section. Theorem-only sections and
  private implementation details do not need blanket exposure.

## Validation

For any lean file `f.lean` that has been changed, run:

    lake env lean f.lean

Also run:

    git diff --check
    rg -n '\bsorry\b' ...

## Completion report

Report:

- which theorems were proved;
- which `sorry`s remain;
- validation commands and their results;
- any changed assumptions;
- any theorem found or suspected to be false.

## Documentation files

Do not create dedicated documentation files or any other Markdown files in subdirectories.
Such files should go into the main project directory at the top level.
This includes Markdown files that provide a review of project updates or that describe
planned work.

File README.md is intended as public documentation.

## Mathematical conventions

This project relies on multiple literature sources (textbooks, monographs, lecture notes)
that do not all share the same terminology or conventions. For this project, Mathlib
style and Mathlib conventions are to be followed whenever possible.

## Mathematical scope and exclusions

Included core: Theory of locally convex topological vector spaces and duality. Closed
Graph and Open Mapping theorems.

Include only as needed: General theory of topological vector spaces.

Excluded: Specializations to Banach space; these are elsewhere in Mathlib.

Excluded: Non-archimedean topological vector spaces.

## Source material

The References directory contains PDF files for several books and other publications.
There is no hierarchy among these references. They serve as a guide for statements worth
including in this project, but not every statement from any source needs to be included.
The ranges below identify candidate material, not completed coverage or a requirement
to reproduce each source's proof apparatus.

- Alpay (2015) Chapter 5. Chapters 1-4 only as needed.
- Bogachev and Smolyanov (2017) TVS. Chapters 1 through 3.
- Bourbaki (2003) TVS. Chapters 2 and 4; Chapters 1 and 3 only as needed.
- Casselman (2016) Lecture Notes. All.
- Holmes (1975) Geometric. Chapters 1 and 2.
- Jarchow (1981) LCS. Deferred for now; more advanced material.
- Köthe (1983) TVS Vol 1. Chapters 3 through 5. Chapters 1 and 2 as needed.
- Narici and Beckenstein (2010) TVS, 2nd Ed. Chapters 5 through 14. Ch 1-4 as needed.
- Osborne (2014) LCS. Chapters 3 through 6. Chapters 1 and 2 as needed.
- Schaefer and Wolff (1999) LCS, 2nd Ed. Chapters 2 through 4. Chapter 1 as needed.
- Voigt (2020) TVS. Chapters 2 through 6. Chapter 1 as needed.

## Reminders

- Further API namespace decisions and the Fréchet-space class name remain deferred.
- General helpers are separated into `MathlibExtras`, `TopologicalGroups`, and
  `TopologicalVectorSpaces`. When preparing upstream contributions, place these declarations
  in their appropriate Mathlib files and recheck for overlap with the pinned dependency.
- Track relevant open PRs: #40983 / #41166 (F-space open mapping; our
  `TopologicalGroups/NearlyOpen.lean`
  factors its core and should be offered upstream), #26345 (bipolar), #42983 (normable spaces).
- Preserve the multiplicative APIs and their `to_additive` counterparts in
  `TopologicalGroups`; noncommutative successive approximation remains a separate extension.
