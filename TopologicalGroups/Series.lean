/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Series in topological groups

In this file and in the definitions of webs, convergence of a series `∑ a k` means convergence
of the ordered partial sums `∑ k ∈ Finset.range N, a k`. Elsewhere, `Summable` and `HasSum` retain
their Mathlib meaning of convergence of the net of finite subsums. This file states the group
lemmas multiplicatively and generates their additive forms with `to_additive`.

The main result is the successive approximation step in De Wilde's proof of the closed graph
theorem, which is also the step in the classical proof of the open mapping theorem. Let `G` be a
first-countable commutative topological group and let `S k` be a sequence of subsets whose
closures are neighbourhoods of zero. Then every point `x₀` of the closure of `S 0` is the sum of
a series `∑ x k` with `x k ∈ S k` for all `k`. No completeness is needed, because the limit of
the series is prescribed. Without first countability the same construction gives terms
`x k ∈ S k` whose remainders `x₀ - ∑ k < n + 1, x k` lie in the closure of `S (n + 1)` and in
prescribed neighbourhoods of zero.

## Main statements

* `Finset.sum_range_add_mem_of_add_subset`: finite sums of `x k ∈ V (k + 1)` stay in `V j` when
  `V (k + 1) + V (k + 1) ⊆ V k`.
* `tendsto_sum_range_of_tendsto_sum_range_add`, `tendsto_sum_range_add_of_tendsto_sum_range`:
  a series converges if and only if one of its tails does, with the expected sums.
* `tendsto_sum_pi`, `tendsto_sum_prod`: series in products converge coordinatewise.
* `exists_seq_mem_sub_sum_mem_closure`
* `exists_seq_mem_tendsto_sum_of_mem_closure`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.2

## Tags

series, successive approximation, topological group, closed graph theorem
-/

public section

open Set Filter

open scoped Topology Pointwise

/-- Let `V k` be sets that contain one, with `V (k + 1) * V (k + 1) ⊆ V k`. If `x k ∈ V (k + 1)`
for all `k` then every finite product `∏ l ∈ range p, x (j + l)` lies in `V j`. -/
@[to_additive /-- Let `V k` be sets that contain zero, with `V (k + 1) + V (k + 1) ⊆ V k`. If
`x k ∈ V (k + 1)` for all `k` then every finite sum `∑ l ∈ range p, x (j + l)` lies in `V j`. -/]
theorem Finset.prod_range_add_mem_of_mul_subset {G : Type*} [CommMonoid G] {V : ℕ → Set G}
    (h0 : ∀ k, (1 : G) ∈ V k) (hadd : ∀ k, V (k + 1) * V (k + 1) ⊆ V k) {x : ℕ → G}
    (hx : ∀ k, x k ∈ V (k + 1)) (p j : ℕ) : ∏ l ∈ Finset.range p, x (j + l) ∈ V j := by
  induction p generalizing j with
  | zero => simpa using h0 j
  | succ p ih =>
    have e (l : ℕ) : x (j + (l + 1)) = x (j + 1 + l) := congrArg x (by omega)
    rw [Finset.prod_range_succ']
    simp only [e, add_zero]
    exact hadd j (Set.mul_mem_mul (ih (j + 1)) (hx j))

section Tails

variable {G : Type*} [CommMonoid G] [TopologicalSpace G] [ContinuousMul G]

/-- If the infinite product `∏ a (m + k)` converges to `s` then the infinite product `∏ a k`
converges to `(∏ k < m, a k) * s`. -/
@[to_additive /-- If the series `∑ a (m + k)` converges to `s` then the series `∑ a k` converges to
`(∑ k < m, a k) + s`. -/]
theorem tendsto_prod_range_of_tendsto_prod_range_add {a : ℕ → G} {m : ℕ} {s : G}
    (h : Tendsto (fun N ↦ ∏ k ∈ Finset.range N, a (m + k)) atTop (𝓝 s)) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, a k) atTop
      (𝓝 ((∏ k ∈ Finset.range m, a k) * s)) := by
  have h1 : Tendsto (fun N ↦ ∏ k ∈ Finset.range (N + m), a k) atTop
      (𝓝 ((∏ k ∈ Finset.range m, a k) * s)) := by
    refine (tendsto_const_nhds.mul h).congr fun N ↦ ?_
    rw [Nat.add_comm N m, Finset.prod_range_add]
  exact (tendsto_add_atTop_iff_nat m).mp h1

end Tails

section Products

variable {ι : Type*} {E : ι → Type*} [∀ j, CommMonoid (E j)] [∀ j, TopologicalSpace (E j)]

/-- In a product of monoids, the partial products of a sequence converge if their coordinates
do. -/
@[to_additive /-- In a product of additive monoids, the partial sums of a sequence converge if
their coordinates do. -/]
theorem tendsto_prod_pi {y : ℕ → ∀ j, E j} {s : ∀ j, E j}
    (h : ∀ j, Tendsto (fun N ↦ ∏ k ∈ Finset.range N, y k j) atTop (𝓝 (s j))) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, y k) atTop (𝓝 s) := by
  rw [tendsto_pi_nhds]
  intro j
  exact (h j).congr fun N ↦ (Finset.prod_apply j _ _).symm

variable {E F : Type*} [CommMonoid E] [CommMonoid F] [TopologicalSpace E]
  [TopologicalSpace F]

/-- In a product `E × F` of monoids, the partial products of a sequence converge if their two
components do. -/
@[to_additive tendsto_sum_prod /-- In a product `E × F` of additive monoids, the partial sums of a
sequence converge if their two components do. -/]
theorem tendsto_prod_prod {y : ℕ → E × F} {s : E} {t : F}
    (hs : Tendsto (fun N ↦ ∏ k ∈ Finset.range N, (y k).1) atTop (𝓝 s))
    (ht : Tendsto (fun N ↦ ∏ k ∈ Finset.range N, (y k).2) atTop (𝓝 t)) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, y k) atTop (𝓝 (s, t)) := by
  refine (hs.prodMk_nhds ht).congr fun N ↦ ?_
  rw [Prod.ext_iff, Prod.fst_prod, Prod.snd_prod]
  exact ⟨rfl, rfl⟩

end Products

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- If the infinite product `∏ a k` converges to `s` then its tail `∏ a (m + k)` converges to
`s / ∏ k < m, a k`. -/
@[to_additive /-- If the series `∑ a k` converges to `s` then its tail `∑ a (m + k)` converges to
`s - ∑ k < m, a k`. -/]
theorem tendsto_prod_range_add_of_tendsto_prod_range {a : ℕ → G} {s : G}
    (h : Tendsto (fun N ↦ ∏ k ∈ Finset.range N, a k) atTop (𝓝 s)) (m : ℕ) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, a (m + k)) atTop
      (𝓝 (s / ∏ k ∈ Finset.range m, a k)) := by
  have h1 : Tendsto (fun N ↦ ∏ k ∈ Finset.range (N + m), a k) atTop (𝓝 s) :=
    (tendsto_add_atTop_iff_nat m).mpr h
  refine (h1.div_const' (∏ k ∈ Finset.range m, a k)).congr fun N ↦ ?_
  rw [Nat.add_comm N m, Finset.prod_range_add, mul_div_cancel_left]

/-- Let `S k` be subsets of a commutative topological group whose closures are neighbourhoods of the
identity, and let `B k` be neighbourhoods of the identity. Then for every point `x₀` of the closure
of `S 0` there are `x k ∈ S k` such that the remainder `x₀ / ∏ k < n + 1, x k` lies in the closure
of `S (n + 1)` and in `B n`, for all `n`. -/
@[to_additive /-- Let `S k` be subsets of a commutative topological group whose closures are
neighbourhoods of zero, and let `B k` be neighbourhoods of zero. Then for every point `x₀` of the
closure of `S 0` there are `x k ∈ S k` such that the remainder `x₀ - ∑ k < n + 1, x k` lies in the
closure of `S (n + 1)` and in `B n`, for all `n`. -/]
theorem exists_seq_mem_div_prod_mem_closure {S B : ℕ → Set G}
    (hS : ∀ k, closure (S k) ∈ 𝓝 (1 : G)) (hB : ∀ k, B k ∈ 𝓝 (1 : G)) {x₀ : G}
    (hx₀ : x₀ ∈ closure (S 0)) :
    ∃ x : ℕ → G, (∀ k, x k ∈ S k) ∧
      ∀ n, x₀ / ∏ k ∈ Finset.range (n + 1), x k ∈ closure (S (n + 1)) ∩ B n := by
  -- The remainders `r k` lie in the closure of `S k` and, for `k ≥ 1`, in `B (k - 1)`.
  let B' : ℕ → Set G := fun k ↦ Nat.casesOn k univ B
  let P : ℕ → G → Prop := fun k r ↦ r ∈ closure (S k) ∧ r ∈ B' k
  have step (k : ℕ) (r : G) (hr : P k r) : ∃ x ∈ S k, P (k + 1) (r / x) := by
    have hN : closure (S (k + 1)) ∩ B k ∈ 𝓝 (1 : G) := inter_mem (hS (k + 1)) (hB k)
    have hc : ContinuousAt (fun z : G ↦ r / z) r := by fun_prop
    have hpre : {z : G | r / z ∈ closure (S (k + 1)) ∩ B k} ∈ 𝓝 r :=
      hc.preimage_mem_nhds (by simpa using hN)
    obtain ⟨z, hz, hzS⟩ := mem_closure_iff_nhds.mp hr.1 _ hpre
    exact ⟨z, hzS, hz⟩
  let R : ∀ k, {r : G // P k r} := fun k ↦
    Nat.rec (motive := fun k ↦ {r : G // P k r}) ⟨x₀, hx₀, trivial⟩
      (fun k r ↦ ⟨r.1 / Classical.choose (step k r.1 r.2),
        (Classical.choose_spec (step k r.1 r.2)).2⟩) k
  let x : ℕ → G := fun k ↦ Classical.choose (step k (R k).1 (R k).2)
  have hxS (k : ℕ) : x k ∈ S k := (Classical.choose_spec (step k (R k).1 (R k).2)).1
  have hR (k : ℕ) : (R (k + 1)).1 = (R k).1 / x k := rfl
  have hsum (n : ℕ) : ∏ k ∈ Finset.range n, x k = x₀ / (R n).1 := by
    induction n with
    | zero => simp [R]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, hR]
      simp only [div_div_eq_mul_div, div_mul_eq_mul_div]
  refine ⟨x, hxS, fun n ↦ ?_⟩
  rw [hsum, div_div_cancel]
  exact (R (n + 1)).2

/-- Let `S k` be subsets of a first-countable commutative topological group whose closures are
neighbourhoods of the identity. Then every point of the closure of `S 0` is the value of an
infinite product `∏ x k` with `x k ∈ S k`. -/
@[to_additive /-- Let `S k` be subsets of a first-countable commutative topological group whose
closures are neighbourhoods of zero. Then every point of the closure of `S 0` is the sum of a series
`∑ x k` with `x k ∈ S k`. -/]
theorem exists_seq_mem_tendsto_prod_of_mem_closure [FirstCountableTopology G] {S : ℕ → Set G}
    (hS : ∀ k, closure (S k) ∈ 𝓝 (1 : G)) {x₀ : G} (hx₀ : x₀ ∈ closure (S 0)) :
    ∃ x : ℕ → G, (∀ k, x k ∈ S k) ∧
      Tendsto (fun n ↦ ∏ k ∈ Finset.range n, x k) atTop (𝓝 x₀) := by
  obtain ⟨b, hb⟩ := (𝓝 (1 : G)).exists_antitone_basis
  obtain ⟨x, hxS, hx⟩ := exists_seq_mem_div_prod_mem_closure hS hb.mem hx₀
  refine ⟨x, hxS, ?_⟩
  -- The remainders tend to the identity.
  have hR0 : Tendsto (fun n ↦ x₀ / ∏ k ∈ Finset.range (n + 1), x k) atTop (𝓝 (1 : G)) :=
    hb.tendsto fun n ↦ (hx n).2
  have h := (tendsto_const_nhds (x := x₀)).div' hR0
  rw [div_one] at h
  refine (tendsto_add_atTop_iff_nat 1).mp (h.congr fun n ↦ ?_)
  rw [div_div_cancel]
