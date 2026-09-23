/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.Bipolar
public import Mathlib.Analysis.LocallyConvex.Barrelled

/-!
# Barrelled spaces and their duals

A locally convex space is barrelled if and only if every weak-* bounded subset of its dual is
equicontinuous. One direction is the Banach–Steinhaus theorem of Mathlib; the other uses the
bipolar theorem: the polar of a barrel is weak-* bounded, and a barrel is its own bipolar.

## Main statements

* `BarrelledSpace.equicontinuous_of_forall_isVonNBounded`: in the dual of a barrelled space the
  pointwise bounded sets are equicontinuous.
* `StrongDual.isVonNBounded_image_polar_of_absorbent`: the polar of an absorbent set is pointwise
  bounded.
* `barrelledSpace_iff_forall_equicontinuous`: the characterization of barrelled spaces.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §4.1, IV §2.2
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.2

## Tags

barrelled space, equicontinuous, Banach–Steinhaus, polar
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

section General

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- In the dual of a barrelled space every pointwise bounded set is equicontinuous. This is the
Banach–Steinhaus theorem for functionals, stated for subsets of the dual. -/
theorem BarrelledSpace.equicontinuous_of_forall_isVonNBounded [BarrelledSpace 𝕜 E]
    {H : Set (StrongDual 𝕜 E)}
    (hH : ∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜 E ↦ φ x) '' H)) :
    Equicontinuous ((↑) : H → E → 𝕜) := by
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have h := PolynormableSpace.banach_steinhaus (𝕜₁ := 𝕜) (𝕜₂ := 𝕜) (E := E) (F := 𝕜)
    (𝓕 := fun φ : H ↦ (φ : StrongDual 𝕜 E)) fun x ↦ by
      have hr : (range fun φ : H ↦ (φ : StrongDual 𝕜 E) x) =
          (fun φ : StrongDual 𝕜 E ↦ φ x) '' H := by
        rw [image_eq_range]
      rw [hr]
      exact hH x
  exact h.equicontinuous

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The polar of an absorbent set is pointwise bounded. -/
theorem StrongDual.isVonNBounded_image_polar_of_absorbent {T : Set E} (hT : Absorbent 𝕜 T)
    (x : E) : IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜 E ↦ φ x) '' StrongDual.polar 𝕜 T) := by
  obtain ⟨c, hc, hc0⟩ := ((hT x).and (eventually_ne_cobounded (0 : 𝕜))).exists
  obtain ⟨t, ht, htx⟩ := hc (mem_singleton x)
  have htx' : c • t = x := htx
  refine (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 ‖c‖).subset ?_
  rintro _ ⟨φ, hφ, rfl⟩
  rw [mem_closedBall_zero_iff]
  change ‖φ x‖ ≤ ‖c‖
  rw [← htx', map_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg c) (hφ t ht)

end General

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- A locally convex space in whose dual every pointwise bounded set is equicontinuous is
barrelled. -/
theorem BarrelledSpace.of_forall_equicontinuous
    (h : ∀ H : Set (StrongDual 𝕜 E),
      (∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜 E ↦ φ x) '' H)) →
        Equicontinuous ((↑) : H → E → 𝕜)) : BarrelledSpace 𝕜 E := by
  refine BarrelledSpace.of_forall_isBarrel_mem_nhds fun T hT ↦ ?_
  -- The polar of the barrel `T` is pointwise bounded, hence equicontinuous.
  obtain ⟨U, hU, hTU⟩ := StrongDual.exists_mem_nhds_subset_polar
    (h _ (StrongDual.isVonNBounded_image_polar_of_absorbent hT.absorbent))
  -- By the bipolar theorem `U` lies in `T`.
  refine mem_of_superset hU fun x hx ↦ ?_
  rw [← StrongDual.bipolar_eq_self (𝕜 := 𝕜) hT.convex hT.balanced hT.isClosed hT.nonempty]
  exact fun φ hφ ↦ hTU hφ x hx

/-- **Characterization of barrelled spaces**: a locally convex space is barrelled if and only if
every pointwise bounded (that is, weak-* bounded) subset of its dual is equicontinuous. -/
theorem barrelledSpace_iff_forall_equicontinuous :
    BarrelledSpace 𝕜 E ↔ ∀ H : Set (StrongDual 𝕜 E),
      (∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜 E ↦ φ x) '' H)) →
        Equicontinuous ((↑) : H → E → 𝕜) :=
  ⟨fun _ _ hH ↦ BarrelledSpace.equicontinuous_of_forall_isVonNBounded hH,
    BarrelledSpace.of_forall_equicontinuous⟩
