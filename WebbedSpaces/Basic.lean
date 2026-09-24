/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.MetricSpace.PiNat
public import MathlibExtras.Topology.Sequences
public import TopologicalGroups.Series
public import TopologicalVectorSpaces.Basic

/-!
# Webs and webbed spaces

This file sets up De Wilde's notion of a web in a topological vector space, following
[G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.1.

A *web* on `E` is a family of subsets `C_{n₁,…,n_k}` of `E`, indexed by finite sequences of
natural numbers, with `E = ⋃ n₁, C_{n₁}` and `C_{n₁,…,n_{k-1}} = ⋃ n_k, C_{n₁,…,n_k}`. Here a
web is a function `C : List ℕ → Set E` with `C [] = univ` and `⋃ n, C (n :: l) = C l`; the most
recent index is at the head of the list. This is the representation that Mathlib uses for
schemes of sets indexed by finite sequences (`CantorScheme`), and the sets along the *strand*
of a sequence `σ : ℕ → ℕ` are `C (PiNat.res σ k)`.

A web is *completing* (a `𝒞`-web, a web of type `𝒞`) if for every strand `σ` there are numbers
`ρ k > 0` such that the series `∑ λ k • x k` converges whenever `x k ∈ C (res σ (k + 1))` and
`0 ≤ λ k ≤ ρ k`. It is *strict* if moreover its sets are `ℝ`-convex and `𝕜`-balanced and the tails
`∑_{k ≥ k₀} λ k • x k` of these series lie in `C (res σ (k₀ + 1))`. A space is *webbed*
(*strictly webbed*) if it has a completing (strict) web.

The general restriction and tail-extension lemmas are imported from
`MathlibExtras.Topology.Sequences`.

## Main definitions

* `IsWeb C`, `IsCompletingWeb C`, `IsStrictWeb 𝕜 C`.
* `WebbedSpace E`, `StrictlyWebbedSpace 𝕜 E`.

## Main statements

* `Set.exists_seq_forall_mem_forall_add_eq`: a sequence of points `Y j ∈ S (k₀ + j)` is the tail
  of a sequence `X k ∈ S k`, if the sets `S k` with `k < k₀` are nonempty.
* `IsWeb.cons_subset`, `IsWeb.res_antitone`: the sets of a web decrease along a strand.
* `IsWeb.exists_mem_res`: every point lies on a strand to any depth.
* `IsStrictWeb.toIsCompletingWeb`: a strict web is completing.
* `IsWeb.exists_forall_smul_subset_of_tendsto`, `IsCompletingWeb.exists_forall_smul_subset`:
  along a strand, the sets `ρ k • C (res σ (k + 1))` are eventually contained in any given
  neighbourhood of zero ([Köthe II][kothe1979], §35.1.(3)).

## Implementation notes

Convergence of a series means convergence of its sequence of partial sums, as in the source;
it is not unconditional summability (`Summable`). The scalars `λ k` are real, so that only a
real vector space structure is needed for a completing web.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35
* [M. De Wilde, *Closed Graph Theorems and Webbed Spaces*][dewilde1978]

## Tags

web, webbed space, De Wilde, closed graph theorem
-/

public section

open Set Filter PiNat

open scoped Topology Pointwise


variable {E : Type*}

/-- A **web** on `E`: a family of subsets indexed by finite sequences of natural numbers, with
`C [] = univ`, such that every set is the union of its successors `C (n :: l)`. -/
structure IsWeb (C : List ℕ → Set E) : Prop where
  /-- The root of a web is the whole space. -/
  nil : C [] = univ
  /-- Every set of a web is the union of its successors. -/
  iUnion_cons : ∀ l : List ℕ, ⋃ n, C (n :: l) = C l

namespace IsWeb

variable {C : List ℕ → Set E}

/-- A successor of a set of a web is contained in it. -/
theorem cons_subset (hC : IsWeb C) (n : ℕ) (l : List ℕ) : C (n :: l) ⊆ C l := by
  rw [← hC.iUnion_cons l]
  exact subset_iUnion (fun n ↦ C (n :: l)) n

/-- The sets of a web decrease along a strand. -/
theorem res_antitone (hC : IsWeb C) (σ : ℕ → ℕ) : Antitone fun k ↦ C (res σ k) :=
  antitone_nat_of_succ_le fun k ↦ by
    rw [res_succ]
    exact hC.cons_subset _ _

/-- Every point of a set of a web lies in one of its successors. -/
theorem exists_mem_cons (hC : IsWeb C) {l : List ℕ} {x : E} (hx : x ∈ C l) :
    ∃ n, x ∈ C (n :: l) := by
  rw [← hC.iUnion_cons l] at hx
  exact mem_iUnion.mp hx

/-- Every point lies on some strand of a web, to any given depth. -/
theorem exists_mem_res (hC : IsWeb C) (x : E) (k : ℕ) : ∃ σ : ℕ → ℕ, x ∈ C (res σ k) := by
  induction k with
  | zero => exact ⟨fun _ ↦ 0, by rw [res_zero, hC.nil]; exact mem_univ x⟩
  | succ k ih =>
    obtain ⟨σ, hσ⟩ := ih
    obtain ⟨n, hn⟩ := hC.exists_mem_cons hσ
    refine ⟨fun i ↦ if i = k then n else σ i, ?_⟩
    have hres : res (fun i ↦ if i = k then n else σ i) k = res σ k := by
      refine res_eq_res.mpr fun i hi ↦ ?_
      simp [Nat.ne_of_lt hi]
    rw [res_succ, hres]
    simpa using hn

end IsWeb

section Completing

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A web is **completing** (a `𝒞`-web) if along every strand `σ` there are numbers `ρ k > 0`
such that the series `∑ λ k • x k` converges whenever `x k ∈ C (res σ (k + 1))` and
`0 ≤ λ k ≤ ρ k` for all `k`. -/
structure IsCompletingWeb (C : List ℕ → Set E) : Prop extends IsWeb C where
  /-- Along every strand there is a sequence of radii for which the associated series
  converge. -/
  exists_radius : ∀ σ : ℕ → ℕ, ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧
    ∀ (x : ℕ → E) (c : ℕ → ℝ), (∀ k, x k ∈ C (res σ (k + 1))) → (∀ k, 0 ≤ c k ∧ c k ≤ ρ k) →
      ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c k • x k) atTop (𝓝 s)

/-- A web is **strict** if its sets are `ℝ`-convex and `𝕜`-balanced and along every strand `σ` there
are numbers `ρ k > 0` such that for `x k ∈ C (res σ (k + 1))` and `0 ≤ λ k ≤ ρ k` the series
`∑ λ k • x k` converges and each of its tails `∑_{k ≥ k₀} λ k • x k` lies in
`C (res σ (k₀ + 1))`. -/
structure IsStrictWeb (𝕜 : Type*) [NormedField 𝕜] [Module 𝕜 E] (C : List ℕ → Set E) :
    Prop extends IsWeb C where
  /-- The sets of a strict web are `ℝ`-convex. -/
  convex : ∀ l, Convex ℝ (C l)
  /-- The sets of a strict web are balanced over `𝕜`. -/
  balanced : ∀ l, Balanced 𝕜 (C l)
  /-- Along every strand there is a sequence of radii for which the associated series converge
  and their tails stay in the sets of the strand. -/
  exists_radius : ∀ σ : ℕ → ℕ, ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧
    ∀ (x : ℕ → E) (c : ℕ → ℝ), (∀ k, x k ∈ C (res σ (k + 1))) → (∀ k, 0 ≤ c k ∧ c k ≤ ρ k) →
      ∀ k₀, ∃ s ∈ C (res σ (k₀ + 1)),
        Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c (k₀ + k) • x (k₀ + k)) atTop (𝓝 s)

/-- The underlying web of a completing web. -/
add_decl_doc IsCompletingWeb.toIsWeb

/-- The underlying web of a strict web. -/
add_decl_doc IsStrictWeb.toIsWeb

/-- A strict web is completing. -/
theorem IsStrictWeb.toIsCompletingWeb {𝕜 : Type*} [NormedField 𝕜] [Module 𝕜 E]
    {C : List ℕ → Set E} (hC : IsStrictWeb 𝕜 C) : IsCompletingWeb C where
  toIsWeb := hC.toIsWeb
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := hC.exists_radius σ
    refine ⟨ρ, hρ, fun x c hx hc ↦ ?_⟩
    obtain ⟨s, -, hs⟩ := h x c hx hc 0
    exact ⟨s, by simpa using hs⟩

variable (E) in
/-- A topological vector space is **webbed** if it has a completing web. -/
class WebbedSpace : Prop where
  /-- A webbed space has a completing web. -/
  exists_isCompletingWeb : ∃ C : List ℕ → Set E, IsCompletingWeb C

/-- A topological vector space is **strictly webbed** if it has a strict web. -/
class StrictlyWebbedSpace (𝕜 F : Type*) [NormedField 𝕜] [AddCommGroup F] [Module ℝ F]
    [Module 𝕜 F] [TopologicalSpace F] : Prop where
  /-- A strictly webbed space has a strict web. -/
  exists_isStrictWeb : ∃ C : List ℕ → Set F, IsStrictWeb 𝕜 C

/-- A strictly webbed space is webbed. This is not an instance, because the scalar field `𝕜`
cannot be inferred from the conclusion. -/
theorem StrictlyWebbedSpace.toWebbedSpace {𝕜 : Type*} [NormedField 𝕜]
    [Module 𝕜 E] [StrictlyWebbedSpace 𝕜 E] : WebbedSpace E := by
  obtain ⟨C, hC⟩ := StrictlyWebbedSpace.exists_isStrictWeb (F := E) (𝕜 := 𝕜)
  exact ⟨C, hC.toIsCompletingWeb⟩

/-- Along a strand `σ` of a web, if `ρ` is a sequence of radii for which the associated series
converge, then the sets `ρ k • C (res σ (k + 1))` are eventually contained in any given
neighbourhood of zero, Köthe II §35.1.(3). -/
theorem IsWeb.exists_forall_smul_subset_of_tendsto [IsTopologicalAddGroup E]
    {C : List ℕ → Set E} (hC : IsWeb C) {σ : ℕ → ℕ} {ρ : ℕ → ℝ}
    (h : ∀ x : ℕ → E, (∀ k, x k ∈ C (res σ (k + 1))) →
      ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, ρ k • x k) atTop (𝓝 s))
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : ∃ k₀, ∀ k, k₀ ≤ k → ρ k • C (res σ (k + 1)) ⊆ U := by
  classical
  -- If some set of the strand is empty, all later ones are.
  by_cases hne : ∀ k, (C (res σ (k + 1))).Nonempty
  · -- Choose `x k` with `ρ k • x k ∉ U` whenever possible.
    have hex (k : ℕ) : ∃ x ∈ C (res σ (k + 1)),
        (∃ y ∈ C (res σ (k + 1)), ρ k • y ∉ U) → ρ k • x ∉ U := by
      by_cases hk : ∃ y ∈ C (res σ (k + 1)), ρ k • y ∉ U
      · obtain ⟨y, hy, hyU⟩ := hk
        exact ⟨y, hy, fun _ ↦ hyU⟩
      · obtain ⟨y, hy⟩ := hne k
        exact ⟨y, hy, fun hk' ↦ absurd hk' hk⟩
    choose x hx hxU using hex
    obtain ⟨s, hs⟩ := h x hx
    -- The terms of a convergent series tend to zero.
    have hterm : Tendsto (fun k ↦ ρ k • x k) atTop (𝓝 (0 : E)) := by
      have h1 : Tendsto (fun N ↦ ∑ k ∈ Finset.range (N + 1), ρ k • x k) atTop (𝓝 s) :=
        hs.comp (tendsto_add_atTop_nat 1)
      have h2 := h1.sub hs
      rw [sub_self] at h2
      refine h2.congr fun N ↦ ?_
      rw [Finset.sum_range_succ, add_sub_cancel_left]
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hterm.eventually hU)
    refine ⟨k₀, fun k hk ↦ ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyU
    exact hxU k ⟨y, hy, hyU⟩ (hk₀ k hk)
  · push Not at hne
    obtain ⟨k₀, hk₀⟩ := hne
    refine ⟨k₀, fun k hk ↦ ?_⟩
    have hempty : C (res σ (k + 1)) = ∅ :=
      subset_empty_iff.mp ((hC.res_antitone σ (Nat.succ_le_succ hk)).trans
        (subset_empty_iff.mpr hk₀))
    rw [hempty, smul_set_empty]
    exact empty_subset U

/-- Along a strand of a completing web, with radii `ρ` as in the definition, the sets
`ρ k • C (res σ (k + 1))` are eventually contained in any given neighbourhood of zero. -/
theorem IsCompletingWeb.exists_forall_smul_subset [IsTopologicalAddGroup E]
    {C : List ℕ → Set E} (hC : IsCompletingWeb C) (σ : ℕ → ℕ) :
    ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧
      (∀ (x : ℕ → E) (c : ℕ → ℝ), (∀ k, x k ∈ C (res σ (k + 1))) →
        (∀ k, 0 ≤ c k ∧ c k ≤ ρ k) →
        ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c k • x k) atTop (𝓝 s)) ∧
      ∀ U ∈ 𝓝 (0 : E), ∃ k₀, ∀ k, k₀ ≤ k → ρ k • C (res σ (k + 1)) ⊆ U := by
  obtain ⟨ρ, hρ, h⟩ := hC.exists_radius σ
  exact ⟨ρ, hρ, h, fun U hU ↦ hC.toIsWeb.exists_forall_smul_subset_of_tendsto
    (fun x hx ↦ h x ρ hx fun k ↦ ⟨(hρ k).le, le_rfl⟩) hU⟩

end Completing
