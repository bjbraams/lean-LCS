/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Finite sums of coordinate linear maps

`LinearMap.finsetSumProj` sums a finite family of coordinate maps. If the ranges of the
coordinate maps span the target, the ranges of these finite sums cover it, as expressed
by `LinearMap.iUnion_range_finsetSumProj`. No topologies are needed.
-/

public section

open Set

section Span

variable {R : Type*} [Semiring R] {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] [AddCommMonoid F] [Module R F]

/-- The linear map `x ↦ ∑ i ∈ s, f i (x i)` on the product, for a finite set `s` of indices. -/
@[expose]
def LinearMap.finsetSumProj (f : ∀ i, E i →ₗ[R] F) (s : Finset ι) : (∀ i, E i) →ₗ[R] F :=
  ∑ i ∈ s, (f i).comp (LinearMap.proj i)

/-- The value of `LinearMap.finsetSumProj`. -/
theorem LinearMap.finsetSumProj_apply (f : ∀ i, E i →ₗ[R] F) (s : Finset ι) (x : ∀ i, E i) :
    LinearMap.finsetSumProj f s x = ∑ i ∈ s, f i (x i) := by
  simp [LinearMap.finsetSumProj]

/-- If the ranges of the maps `f i` span `F` then `F` is the union of the ranges of the maps
`x ↦ ∑ i ∈ s, f i (x i)`. -/
theorem LinearMap.iUnion_range_finsetSumProj {f : ∀ i, E i →ₗ[R] F}
    (hf : ⨆ i, LinearMap.range (f i) = ⊤) :
    ⋃ s : Finset ι, Set.range (LinearMap.finsetSumProj f s) = univ := by
  classical
  refine eq_univ_of_forall fun y ↦ ?_
  have hy : y ∈ ⨆ i, LinearMap.range (f i) := hf ▸ Submodule.mem_top
  simp only [mem_iUnion, Set.mem_range, LinearMap.finsetSumProj_apply]
  -- Extension by zero from a subset of the index set.
  have key (s u : Finset ι) (hsu : s ⊆ u) (x : ∀ i, E i) :
      ∑ i ∈ u, f i (if i ∈ s then x i else 0) = ∑ i ∈ s, f i (x i) := by
    rw [← Finset.sum_subset hsu fun i _ his ↦ by simp [his]]
    exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]
  induction hy using Submodule.iSup_induction' with
  | mem i y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨{i}, Pi.single i x, by rw [Finset.sum_singleton, Pi.single_eq_same]⟩
  | zero => exact ⟨∅, 0, Finset.sum_empty⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨s, x, rfl⟩ := h₁
    obtain ⟨t, x', rfl⟩ := h₂
    refine ⟨s ∪ t, fun i ↦ (if i ∈ s then x i else 0) + (if i ∈ t then x' i else 0), ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    rw [key s (s ∪ t) Finset.subset_union_left, key t (s ∪ t) Finset.subset_union_right]

end Span
