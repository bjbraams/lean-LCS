/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.TotallyBounded
public import MathlibExtras.Analysis.ConvexCompact

import Mathlib.Tactic.Linarith

/-!
# Milman's converse to the Krein–Milman theorem

If the closed convex hull of a set is compact, its extreme points belong to the closure of the
original set. In particular, a compact generating set contains all extreme points. Together with
the Krein–Milman theorem, this characterizes the closed subsets that generate a compact convex
set: they are exactly those containing the closure of its extreme points.

All convex hulls and extreme points are over the real scalars. The ambient space is a Hausdorff
locally convex real topological vector space; no completeness or metrizability assumption is
imposed. For a compact generating set in a quasi-complete space, compactness of its closed
convex hull is automatic.

## Main statements

* `IsCompact.extremePoints_closure_convexHull_subset_closure`: **Milman's theorem**.
* `IsCompact.extremePoints_closure_convexHull_subset`: the case of a compact generating set.
* `IsCompact.closure_convexHull_eq_iff_closure_extremePoints_subset`: the closure of the
  extreme points is the least closed generating subset of a compact convex set.
* `IsCompact.extremePoints_closure_convexHull_subset_of_quasiCompleteSpace`: the quasi-complete
  case, without a compactness hypothesis on the hull.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §10.5
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {s C : Set E}

/-- **Milman's converse**: the extreme points of a compact closed convex hull belong to
the closure of the generating set. The finite-cover proof adapts the mathematical argument
in Schaefer–Wolff, *Topological Vector Spaces*, II §10.5, using separating half-spaces. -/
theorem IsCompact.extremePoints_closure_convexHull_subset_closure
    (hC : IsCompact (closure (convexHull ℝ s))) :
    (closure (convexHull ℝ s)).extremePoints ℝ ⊆ closure s := by
  classical
  let C := closure (convexHull ℝ s)
  have hc : Convex ℝ C := (convex_convexHull ℝ s).closure
  have hsC : closure s ⊆ C := closure_mono (subset_convexHull ℝ s)
  have hs : IsCompact (closure s) := hC.of_isClosed_subset isClosed_closure hsC
  intro x hx
  by_contra hxs
  have hsep (y : closure s) : ∃ f : StrongDual ℝ E, f y < f x :=
    geometric_hahn_banach_point_point (fun h ↦ hxs (h ▸ y.property))
  choose f hf using hsep
  let r (y : closure s) := (f y y + f y x) / 2
  let U (y : closure s) : Set E := {z | f y z < r y}
  let K (y : closure s) : Set E := C ∩ {z | f y z ≤ r y}
  have hK (y : closure s) : IsCompact (K y) :=
    hC.inter_right (isClosed_le (f y).continuous continuous_const)
  have hconv (y : closure s) : Convex ℝ (K y) :=
    hc.inter ((convex_Iic (r y)).linear_preimage (f y).toLinearMap)
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover U
    (fun y ↦ isOpen_lt (f y).continuous continuous_const) (by
      intro y hy
      refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
      change f ⟨y, hy⟩ y < (f ⟨y, hy⟩ y + f ⟨y, hy⟩ x) / 2
      linarith [hf ⟨y, hy⟩])
  have hcover : s ⊆ ⋃ y ∈ (↑t : Set (closure s)), K y := by
    intro z hz
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht (subset_closure hz))
    exact mem_iUnion₂.mpr
      ⟨y, hyt, hsC (subset_closure hz), (show f y z < r y from hy).le⟩
  have hcomp := t.finite_toSet.isCompact_convexHull_biUnion
    (fun y _ ↦ hK y) (fun y _ ↦ hconv y)
  have heq : convexHull ℝ (⋃ y ∈ (↑t : Set (closure s)), K y) = C := by
    apply Subset.antisymm
    · exact convexHull_min (iUnion₂_subset fun _ _ ↦ inter_subset_left) hc
    · exact closure_minimal (convexHull_mono hcover) hcomp.isClosed
  have hx' : x ∈ (convexHull ℝ (⋃ y ∈ (↑t : Set (closure s)), K y)).extremePoints ℝ :=
    heq.symm ▸ hx
  obtain ⟨y, _, hy⟩ := mem_iUnion₂.mp (extremePoints_convexHull_subset hx')
  have hle : f y x ≤ (f y y + f y x) / 2 := hy.2
  linarith [hf y]

/-- A compact generating set contains all extreme points of its compact closed convex hull.
This is the compact-set form of Milman's converse (Schaefer–Wolff, II §10.5). -/
theorem IsCompact.extremePoints_closure_convexHull_subset (hs : IsCompact s)
    (hC : IsCompact (closure (convexHull ℝ s))) :
    (closure (convexHull ℝ s)).extremePoints ℝ ⊆ s := by
  simpa only [hs.isClosed.closure_eq] using
    hC.extremePoints_closure_convexHull_subset_closure

/-- Every set generating a compact convex set has all its extreme points in its closure. -/
theorem IsCompact.extremePoints_subset_closure_of_closure_convexHull_eq
    (hC : IsCompact C) (h : closure (convexHull ℝ s) = C) :
    C.extremePoints ℝ ⊆ closure s := by
  subst C
  exact hC.extremePoints_closure_convexHull_subset_closure

/-- A closed subset of a compact convex set generates it exactly when it contains the
closure of the extreme points. Thus that closure is the least closed generating subset. -/
theorem IsCompact.closure_convexHull_eq_iff_closure_extremePoints_subset
    (hC : IsCompact C) (hconv : Convex ℝ C) (hs : IsClosed s) (hsC : s ⊆ C) :
    closure (convexHull ℝ s) = C ↔ closure (C.extremePoints ℝ) ⊆ s := by
  constructor
  · intro h
    exact closure_minimal (by
      simpa only [hs.closure_eq] using
        hC.extremePoints_subset_closure_of_closure_convexHull_eq h) hs
  · intro h
    apply Subset.antisymm (closure_minimal (convexHull_min hsC hconv) hC.isClosed)
    rw [← closure_convexHull_extremePoints hC hconv]
    exact closure_mono (convexHull_mono (subset_closure.trans h))

/-- In a Hausdorff quasi-complete locally convex space, a compact set contains every extreme
point of its closed convex hull. This combines Milman's converse with compactness of the
closed convex hull; it applies, in particular, in complete spaces. -/
theorem IsCompact.extremePoints_closure_convexHull_subset_of_quasiCompleteSpace
    {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [T2Space F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [QuasiCompleteSpace 𝕜 F]
    {s : Set F} (hs : IsCompact s) :
    (closure (convexHull ℝ s)).extremePoints ℝ ⊆ s := by
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  exact hs.extremePoints_closure_convexHull_subset
    (isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := 𝕜) hs.totallyBounded.convexHull)
