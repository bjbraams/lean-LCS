/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TopologicalVectorSpaces.QuotientSeminorm

/-!
# Quotients of locally convex spaces

Mathlib equips the quotient `E ⧸ N` of a topological module by a submodule with the quotient
topology and shows that it is a topological module (`Mathlib/Topology/Algebra/Module/Basic.lean`).
This file adds that the quotient of a locally convex space is locally convex and that the
quotient of a barrelled space is barrelled. Both follow from the fact that the quotient map is
an open, continuous, surjective linear map. The core local-convexity theorem allows an
ordered semiring of scalars and scalar restriction; the core barrelledness theorem works over
a seminormed ring by pulling back lower semicontinuous seminorms.

## Main statements

* `Submodule.Quotient.instLocallyConvexSpace`: a quotient of a locally convex space is locally
  convex.
* `Submodule.Quotient.instBarrelledSpace`: a quotient of a barrelled space is barrelled.
* `Submodule.Quotient.instPolynormableSpace`: a quotient of a polynormable space is
  polynormable; its topology is defined by the quotients of the continuous seminorms.

## Implementation notes

For a real or complex space, local convexity is `LocallyConvexSpace ℝ E` while the submodule `N`
is a `𝕜`-submodule. The real module structure on `E ⧸ N` is Mathlib's
`Submodule.Quotient.module'`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §4.4 and III §4.1
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §4 and II §7.2

## Tags

quotient space, locally convex space, barrelled space
-/

public section

open Set Filter

open scoped Topology

namespace Submodule.Quotient


section General

/-- Local convexity descends to quotients, including after restriction of scalars. -/
theorem locallyConvexSpace_restrictScalars {R 𝕜 E : Type*} [Semiring R] [PartialOrder R]
    [Ring 𝕜] [SMul R 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module R E]
    [IsScalarTower R 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyConvexSpace R E] (N : Submodule 𝕜 E) : LocallyConvexSpace R (E ⧸ N) :=
  LocallyConvexSpace.ofBasisZero R (E ⧸ N) _ _
    (nhds_zero_hasBasis_image N (LocallyConvexSpace.convex_basis_zero R E))
    fun _ hs ↦ hs.2.is_linear_image (N.mkQ.restrictScalars R).isLinear

/-- Barrelledness descends to a module quotient over a seminormed ring. -/
theorem barrelledSpace {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (N : Submodule 𝕜 E) :
    BarrelledSpace 𝕜 (E ⧸ N) := by
  constructor
  intro p hp
  apply N.isQuotientMap_mkQ.continuous_iff.mpr
  exact (p.comp N.mkQ).continuous_of_lowerSemicontinuous
    (hp.comp N.isQuotientMap_mkQ.continuous)

end General

/-- A quotient of a locally convex module is locally convex, also after restricting scalars. -/
instance instLocallyConvexSpace {R 𝕜 E : Type*} [Semiring R] [PartialOrder R]
    [Ring 𝕜] [SMul R 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module R E]
    [IsScalarTower R 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyConvexSpace R E] (N : Submodule 𝕜 E) : LocallyConvexSpace R (E ⧸ N) :=
  locallyConvexSpace_restrictScalars N

/-- A quotient of a barrelled module over a seminormed ring is barrelled. -/
instance instBarrelledSpace {𝕜 E : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (N : Submodule 𝕜 E) :
    BarrelledSpace 𝕜 (E ⧸ N) :=
  barrelledSpace N


end Submodule.Quotient


namespace Submodule.Quotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] (N : Submodule 𝕜 E)

/-- A quotient of a polynormable space is polynormable: its topology is defined by the quotients
of the continuous seminorms. -/
instance instPolynormableSpace [PolynormableSpace 𝕜 E] : PolynormableSpace 𝕜 (E ⧸ N) := by
  have : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup 𝕜 E
  let Q : SeminormFamily 𝕜 (E ⧸ N) {p : Seminorm 𝕜 E // Continuous p} := fun p ↦ p.1.quotient N
  refine WithSeminorms.toPolynormableSpace (p := Q) (Q.withSeminorms_of_hasBasis
    ⟨fun V ↦ ⟨fun hV ↦ ?_, ?_⟩⟩)
  · -- A neighbourhood of zero contains the image of a ball of a continuous seminorm.
    have hpre : N.mkQ ⁻¹' V ∈ 𝓝 (0 : E) :=
      N.isQuotientMap_mkQ.continuous.continuousAt.preimage_mem_nhds (by simpa using hV)
    obtain ⟨p, hp, hpV⟩ := (PolynormableSpace.hasBasis_zero_ball 𝕜 E).mem_iff.mp hpre
    refine ⟨(Q ⟨p, hp⟩).ball 0 1, Q.basisSets_singleton_mem ⟨p, hp⟩ one_pos, ?_⟩
    rw [id, ← Seminorm.image_mkQ_ball]
    exact image_subset_iff.mpr hpV
  · rintro ⟨U, hU, hUV⟩
    refine mem_of_superset ?_ hUV
    obtain ⟨s, r, hr, rfl⟩ := Q.basisSets_iff.mp hU
    rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
    refine (Filter.biInter_finset_mem s).2 fun p _ ↦ ?_
    have hcont : Continuous (Q p) := Seminorm.continuous_quotient p.1 N p.2
    have h := (isOpen_lt hcont continuous_const : IsOpen {q | Q p q < r}).mem_nhds
      (show (0 : E ⧸ N) ∈ {q | Q p q < r} by simpa using hr)
    exact mem_of_superset h fun q hq ↦ by simpa [Seminorm.mem_ball_zero] using hq

end Submodule.Quotient
