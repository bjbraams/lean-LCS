/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.PolarCalculus
public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.Convex
public import TopologicalVectorSpaces.Basic

/-!
# The bipolar theorem

The bipolar of a set is its closed, convex, balanced hull. This file proves the theorem in a
form that does not mention a hull operator: if `t` is a nonempty, closed, convex, balanced set
containing `s` then `t` contains the bipolar of `s`; in particular a nonempty, closed, convex,
balanced set is its own bipolar. Since polars are closed, convex and balanced and the bipolar of
`s` contains `s`, this characterizes the bipolar of a nonempty set as the smallest closed,
convex, balanced set containing it.

The theorem is given in two settings.

* For a real or complex locally convex space `E` and its continuous dual, with polars taken in
  `StrongDual 𝕜 E` and bipolars in `E`, and closedness referring to the given topology of `E`.
* For a bilinear pairing `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, with closedness referring to the weak
  topology `WeakBilin B` on `E`.

Both rest on one separation lemma, `StrongDual.exists_mem_polar_one_lt_norm`. The weak-* dual of a
topological vector space `E` is covered by the second setting, with `B := topDualPairing 𝕜 E`, for
which `WeakBilin B` unfolds to `WeakDual 𝕜 E`.

## Main statements

* `StrongDual.exists_mem_polar_one_lt_norm`: a point outside a nonempty, closed, convex,
  balanced subset `s` of a locally convex space is separated from it by a functional `φ` in the
  polar of `s` with `1 < ‖φ x‖`.
* `LinearMap.eq_zero_of_forall_norm_le_one`: a linear functional bounded by one on a submodule
  vanishes on it.
* `StrongDual.bipolar_subset`, `StrongDual.bipolar_eq_self`: the bipolar theorem for a locally
  convex space and its continuous dual.
* `LinearMap.flip_polar_polar_subset`, `LinearMap.flip_polar_polar_eq_self`: the bipolar theorem
  for a bilinear pairing.
* `LinearMap.exists_mem_polar_one_lt_norm`: the separation lemma for a bilinear pairing.

## Implementation notes

Convexity is over `ℝ` and balancedness over `𝕜`, as in `LocallyConvexSpaces.Barrel`. The
statements avoid `closedAbsConvexHull 𝕜`, which for `𝕜 = ℂ` refers to the order on `ℂ`.

There is no statement whose hypotheses are phrased for subsets of `WeakDual 𝕜 E`. In the pinned
Mathlib that type carries both a derived `AddCommMonoid` instance and a separate `AddCommGroup`
instance, and unifying `Convex ℝ A` for `A : Set (WeakDual 𝕜 E)` with the hypothesis of a lemma
about an `AddCommGroup` takes several hundred thousand heartbeats or fails. Subsets of
`WeakBilin (topDualPairing 𝕜 E)` do not have this problem.

In `LinearMap.flip_polar_polar_subset` the sets `s` and `t` are subsets of `WeakBilin B`, which
is a type synonym of `E`, and `B` is applied to their elements through that definitional
equality, in the same way as in `LinearMap.polar_isClosed` of Mathlib.

## Relation to work outside Mathlib

Mathlib PR #26345 (C. Hoskin, "Bipolar theorem"), new file
`Mathlib/Analysis/LocallyConvex/Bipolar.lean`, proves the bipolar theorem for a bilinear pairing in
the form `LinearMap.pairing_flip_polar_polar`:
`(pairing B).flip.polar ((pairing B).polar s) = closedAbsConvexHull 𝕜 s` for a nonempty subset `s`
of `WeakBilin B`, where `WeakBilin.pairing` is introduced in the same PR. That is the same
mathematical content as `LinearMap.flip_polar_polar_subset` below, in a different formulation. The
present file was written after reading that PR. The proof here is organized differently, through the
separation lemma for an arbitrary locally convex space, but the central steps are the same classical
ones as in the PR: strict separation of a point from a closed convex set, rotation of the scalar to
pass from the real part to the norm, rescaling of the functional, and the representation of weakly
continuous functionals (`LinearMap.dualEmbedding_surjective`). When that PR is in the pinned
Mathlib, the pairing version here should be restated in terms of it or removed.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §6.3 and IV §1.3
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §1.5
* [J. B. Conway, *A Course in Functional Analysis*][conway1990], V.1.8

## Tags

polar, bipolar, locally convex space, weak topology
-/

public section

open Set

open scoped Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Separation

variable [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- In a locally convex space, a point `x` outside a nonempty, closed, convex, balanced set `s`
is separated from `s` by a continuous linear functional in the polar of `s`: there is `φ` with
`‖φ y‖ ≤ 1` for all `y ∈ s` and `1 < ‖φ x‖`.

The argument is the one used for the pairing version of the bipolar theorem in Mathlib PR
#26345 (C. Hoskin), `LinearMap.pairing_flip_polar_polar`, file
`Mathlib/Analysis/LocallyConvex/Bipolar.lean`. This proof adapts the separation, rotation and
rescaling steps of that proof. Delete the adapted proof when the PR is in pinned Mathlib and
derive this separation corollary from the upstream theorem. -/
theorem StrongDual.exists_mem_polar_one_lt_norm {s : Set E} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) {x : E} (hx : x ∉ s) :
    ∃ φ ∈ StrongDual.polar 𝕜 s, 1 < ‖φ x‖ := by
  obtain ⟨f, u, hf, hu⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hc hcl hx
  have h0 : (0 : E) ∈ s := by
    obtain ⟨y, hy⟩ := hne
    have h := balanced_iff_smul_mem.mp hb (show ‖(0 : 𝕜)‖ ≤ 1 by simp) hy
    simpa using h
  have hu0 : 0 < u := by simpa using hf 0 h0
  -- Rotate the scalar to pass from the real part to the norm.
  have hnorm (a : E) (ha : a ∈ s) : ‖f a‖ < u := by
    obtain ⟨c, hc1, hc2⟩ := RCLike.exists_norm_eq_mul_self (f a)
    have hca : c • a ∈ s := balanced_iff_smul_mem.mp hb hc1.le ha
    have h := hf _ hca
    rwa [map_smul, smul_eq_mul, ← hc2, RCLike.ofReal_re] at h
  refine ⟨((u⁻¹ : ℝ) : 𝕜) • f, fun a ha ↦ ?_, ?_⟩
  · change ‖((u⁻¹ : ℝ) : 𝕜) • f a‖ ≤ 1
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hu0),
      inv_mul_le_iff₀ hu0, mul_one]
    exact (hnorm a ha).le
  · change 1 < ‖((u⁻¹ : ℝ) : 𝕜) • f x‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hu0), lt_inv_mul_iff₀ hu0, mul_one]
    exact hu.trans_le (RCLike.re_le_norm (f x))

end Separation


section Subspaces

variable {𝕜 M : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup M] [Module 𝕜 M]

/-- A linear functional that is bounded by one on a submodule vanishes on it. -/
theorem LinearMap.eq_zero_of_forall_norm_le_one {Q : Submodule 𝕜 M} {φ : M →ₗ[𝕜] 𝕜}
    (h : ∀ x ∈ Q, ‖φ x‖ ≤ 1) {x : M} (hx : x ∈ Q) : φ x = 0 :=
  eq_zero_of_forall_norm_mul_le_one fun c ↦ by
    have := h (c • x) (Q.smul_mem c hx)
    rwa [map_smul, smul_eq_mul] at this

end Subspaces

section StrongDual

variable [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- The **bipolar theorem** for a locally convex space `E` and its continuous dual: a nonempty,
closed, convex, balanced set `t` that contains `s` contains the bipolar of `s`.

Provenance: a reformulated corollary of `LinearMap.pairing_flip_polar_polar` in Mathlib PR
#26345 (C. Hoskin), file `Mathlib/Analysis/LocallyConvex/Bipolar.lean`. This proof uses the
locally adapted separation argument. Once the PR is in pinned Mathlib, delete the duplicate
proof and derive any retained corollary from that upstream theorem. -/
theorem StrongDual.bipolar_subset {s t : Set E} (hst : s ⊆ t) (hc : Convex ℝ t)
    (hb : Balanced 𝕜 t) (hcl : IsClosed t) (hne : t.Nonempty) :
    (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 s) ⊆ t := by
  intro x hx
  by_contra hxt
  obtain ⟨φ, hφ, hφx⟩ := StrongDual.exists_mem_polar_one_lt_norm hc hb hcl hne hxt
  exact hφx.not_ge (hx φ fun y hy ↦ hφ y (hst hy))

/-- The **bipolar theorem** for a locally convex space `E` and its continuous dual: a nonempty,
closed, convex, balanced set is its own bipolar.

Provenance: a reformulated corollary of `LinearMap.pairing_flip_polar_polar` in Mathlib PR
#26345 (C. Hoskin), file `Mathlib/Analysis/LocallyConvex/Bipolar.lean`. This proof uses the
locally adapted separation argument. Once the PR is in pinned Mathlib, delete the duplicate
proof and derive any retained corollary from that upstream theorem. -/
theorem StrongDual.bipolar_eq_self {s : Set E} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) :
    (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 s) = s :=
  (StrongDual.bipolar_subset Subset.rfl hc hb hcl hne).antisymm
    ((topDualPairing 𝕜 E).flip.subset_bipolar s)

end StrongDual

namespace LinearMap

section Pairing

variable [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- For a bilinear pairing `B`, a point `x` outside a nonempty, weakly closed, convex, balanced
subset `t` of `E` is separated from `t` by an element of the polar of `t`: there is `y : F` with
`‖B z y‖ ≤ 1` for all `z ∈ t` and `1 < ‖B x y‖`.

Provenance: a reformulated corollary of `LinearMap.pairing_flip_polar_polar` in Mathlib PR
#26345 (C. Hoskin), file `Mathlib/Analysis/LocallyConvex/Bipolar.lean`. This proof uses the
locally adapted separation argument. Once the PR is in pinned Mathlib, delete the duplicate
proof and derive any retained corollary from that upstream theorem. -/
theorem exists_mem_polar_one_lt_norm {t : Set (WeakBilin B)} (hc : Convex ℝ t)
    (hb : Balanced 𝕜 t) (hcl : IsClosed t) (hne : t.Nonempty) {x : WeakBilin B} (hx : x ∉ t) :
    ∃ y ∈ B.polar t, 1 < ‖B x y‖ := by
  obtain ⟨φ, hφ, hφx⟩ := StrongDual.exists_mem_polar_one_lt_norm hc hb hcl hne hx
  obtain ⟨y, rfl⟩ := B.dualEmbedding_surjective φ
  exact ⟨y, fun z hz ↦ hφ z hz, hφx⟩

/-- The **bipolar theorem** for a bilinear pairing: a nonempty, weakly closed, convex, balanced
set `t` that contains `s` contains the bipolar of `s`.

The same content, formulated as `bipolar s = closedAbsConvexHull 𝕜 s`, is
`LinearMap.pairing_flip_polar_polar` of Mathlib PR #26345 (C. Hoskin), file
`Mathlib/Analysis/LocallyConvex/Bipolar.lean`. The statement is reformulated and the proof is
adapted via the separation lemma. Delete this duplicate when the PR is in pinned Mathlib, or
retain its API as a corollary of the upstream theorem. -/
theorem flip_polar_polar_subset {s t : Set (WeakBilin B)} (hst : s ⊆ t) (hc : Convex ℝ t)
    (hb : Balanced 𝕜 t) (hcl : IsClosed t) (hne : t.Nonempty) :
    B.flip.polar (B.polar s) ⊆ t := by
  intro x hx
  by_contra hxt
  obtain ⟨y, hy, hyx⟩ := B.exists_mem_polar_one_lt_norm hc hb hcl hne hxt
  exact hyx.not_ge (hx y fun z hz ↦ hy z (hst hz))

/-- The **bipolar theorem** for a bilinear pairing: a nonempty, weakly closed, convex, balanced
set is its own bipolar.

Provenance: a reformulated corollary of `LinearMap.pairing_flip_polar_polar` in Mathlib PR
#26345 (C. Hoskin), file `Mathlib/Analysis/LocallyConvex/Bipolar.lean`. This proof uses the
locally adapted separation argument. Once the PR is in pinned Mathlib, delete the duplicate
proof and derive any retained corollary from that upstream theorem. -/
theorem flip_polar_polar_eq_self {s : Set (WeakBilin B)} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) : B.flip.polar (B.polar s) = s :=
  (B.flip_polar_polar_subset Subset.rfl hc hb hcl hne).antisymm (B.subset_bipolar s)

end Pairing

end LinearMap
