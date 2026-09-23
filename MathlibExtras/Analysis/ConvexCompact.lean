/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Topology

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compactness of convex unions

The ambient real module needs continuous addition and scalar multiplication, without local
convexity or separation assumptions.

## Main statements

* `IsCompact.convexJoin`: the convex join of two compact sets is compact.
* `IsCompact.convexHull_union`: the convex hull of the union of two compact convex sets is
  compact.
* `Set.Finite.isCompact_convexHull_biUnion`: the same for finite unions.
-/

public section

open Set Filter

open scoped Topology Pointwise

section Union

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [ContinuousAdd X]
  [ContinuousSMul ℝ X]

/-- The convex join of two compact sets is compact. Neither set needs to be convex. -/
theorem IsCompact.convexJoin {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  -- The convex join is the image of `s × t × [0, 1]` under `(a, b, θ) ↦ (1 - θ) • a + θ • b`.
  let f : X × X × ℝ → X := fun p ↦ (1 - p.2.2) • p.1 + p.2.2 • p.2.1
  have hf : Continuous f := by fun_prop
  have himage : _root_.convexJoin ℝ s t = f '' (s ×ˢ t ×ˢ Icc (0 : ℝ) 1) := by
    ext x
    rw [mem_convexJoin]
    constructor
    · rintro ⟨a, ha, b, hb, u, v, hu, hv, huv, rfl⟩
      refine ⟨(a, b, v), ⟨ha, hb, hv, by linarith⟩, ?_⟩
      change (1 - v) • a + v • b = u • a + v • b
      rw [show 1 - v = u by linarith]
    · rintro ⟨⟨a, b, θ⟩, ⟨ha, hb, hθ0, hθ1⟩, rfl⟩
      exact ⟨a, ha, b, hb, 1 - θ, θ, by linarith, hθ0, by ring, rfl⟩
  rw [himage]
  exact (hs.prod (ht.prod isCompact_Icc)).image hf

/-- The convex hull of the union of two compact convex sets is compact. -/
theorem IsCompact.convexHull_union {s t : Set X} (hs : IsCompact s) (ht : IsCompact t)
    (hsc : Convex ℝ s) (htc : Convex ℝ t) : IsCompact (convexHull ℝ (s ∪ t)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs₀
  · rwa [empty_union, htc.convexHull_eq]
  rcases t.eq_empty_or_nonempty with rfl | ht₀
  · rwa [union_empty, hsc.convexHull_eq]
  rw [Convex.convexHull_union hsc htc hs₀ ht₀]
  exact hs.convexJoin ht

end Union

section FiniteUnion

variable {X ι : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- The convex hull of a finite union of compact convex sets is compact. -/
theorem Set.Finite.isCompact_convexHull_biUnion {s : Set ι} (hs : s.Finite)
    {K : ι → Set X} (hK : ∀ i ∈ s, IsCompact (K i))
    (hconv : ∀ i ∈ s, Convex ℝ (K i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ s, K i)) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert i s hi hs ih =>
    rw [biUnion_insert, ← convexHull_convexHull_union_right]
    exact (hK i (by simp)).convexHull_union
      (ih (fun j hj ↦ hK j (by simp [hj])) (fun j hj ↦ hconv j (by simp [hj])))
      (hconv i (by simp)) (convex_convexHull _ _)

end FiniteUnion
