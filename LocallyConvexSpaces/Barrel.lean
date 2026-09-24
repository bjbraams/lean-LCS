/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import TopologicalVectorSpaces.Basic

/-!
# Barrels

A *barrel* in a topological vector space over `ℝ` or `ℂ` is a set that is closed, `ℝ`-convex,
balanced and absorbent. Mathlib defines `BarrelledSpace 𝕜 E` by the requirement that every lower
semicontinuous seminorm on `E` is continuous. This file introduces barrels and shows that this
agrees with the classical definition: `E` is barrelled if and only if every barrel is a
neighbourhood of zero. This resolves the TODO in `Mathlib/Analysis/LocallyConvex/Barrelled.lean`.

## Main definitions

* `IsBarrel 𝕜 s`: the set `s` is closed, `ℝ`-convex, balanced and absorbent.
* `IsBarrel.gaugeSeminorm`: the gauge of a barrel, as a seminorm.

## Main statements

* `Seminorm.isBarrel_closedBall`: closed balls of positive radius of a lower semicontinuous
  seminorm are barrels.
* `IsBarrel.closedBall_gaugeSeminorm`, `IsBarrel.lowerSemicontinuous_gaugeSeminorm`: a barrel is
  the closed unit ball of its gauge, and the gauge is lower semicontinuous.
* `isBarrel_iff_exists_seminorm`: barrels are exactly the closed unit balls of lower
  semicontinuous seminorms.
* `barrelledSpace_iff_forall_isBarrel_mem_nhds`: `E` is barrelled if and only if every barrel in
  `E` is a neighbourhood of zero. Local convexity is not needed for this equivalence.
* `nhds_zero_hasBasis_isBarrel`: in a polynormable (in particular, in a locally convex) space
  the barrels that are neighbourhoods of zero form a basis of neighbourhoods of zero.
* `IsBarrel.preimage`: the preimage of a barrel under a continuous linear map is a barrel.
* `isBarrel_closure_preimage`, `LinearMap.closure_preimage_mem_nhds_of_barrelledSpace`: for a
  linear   map `f` (not assumed continuous) the closure of the preimage of a `ℝ`-convex balanced
  neighbourhood of zero is a barrel; hence it is a neighbourhood of zero if the domain is
  barrelled.   This "near   continuity" is the point of entry of barrelledness into the closed
  graph theorem.
* `isBarrel_closure_image`, `LinearMap.closure_image_mem_nhds_of_barrelledSpace`: for a surjective
  linear map `f` (not assumed continuous) the closure of the image of a `ℝ`-convex balanced
  neighbourhood of zero is a barrel; hence it is a neighbourhood of zero if the codomain is
  barrelled. This "near openness" is the point of entry of barrelledness into the open mapping
  theorem.

## Implementation notes

Convexity is expressed over `ℝ` and balancedness and absorbency over `𝕜`. This is the convention
of `gaugeSeminorm` and `Seminorm.convex_closedBall`, and it avoids the order on `ℂ` that
`AbsConvex ℂ` relies on.

The imported lemmas in `TopologicalVectorSpaces.Basic`, including `Absorbent.preimage`,
`Balanced.preimage`, `Absorbent.image_of_surjective`, `Balanced.image` and
`Absorbent.restrictScalars_real` are of a general nature and belong with
`Mathlib/Analysis/LocallyConvex/Basic.lean`. The two image lemmas are named as in Mathlib PR
#40983, which states them in greater generality; they are to be deleted here once that PR has
been merged and Mathlib has been bumped; provenance is recorded beside their declarations.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §4.1
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §7

## Tags

barrel, barrelled space, gauge, lower semicontinuous seminorm
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

variable {𝕜 E F : Type*}

section Defs

variable (𝕜) [SeminormedRing 𝕜] [AddCommMonoid E] [SMul 𝕜 E] [Module ℝ E] [TopologicalSpace E]

/-- A set is a **barrel** if it is closed, convex over `ℝ`, and balanced and absorbent over `𝕜`. -/
structure IsBarrel (s : Set E) : Prop where
  /-- A barrel is closed. -/
  isClosed : IsClosed s
  /-- A barrel is `ℝ`-convex. -/
  convex : Convex ℝ s
  /-- A barrel is balanced. -/
  balanced : Balanced 𝕜 s
  /-- A barrel is absorbent. -/
  absorbent : Absorbent 𝕜 s

end Defs

section Basic

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [TopologicalSpace E] {s t : Set E}

/-- The whole space is a barrel. -/
theorem isBarrel_univ : IsBarrel 𝕜 (univ : Set E) :=
  ⟨isClosed_univ, convex_univ, balanced_univ, absorbent_univ⟩

namespace IsBarrel

/-- A barrel contains the origin. -/
theorem zero_mem (hs : IsBarrel 𝕜 s) : (0 : E) ∈ s :=
  hs.absorbent.zero_mem

/-- A barrel is nonempty. -/
theorem nonempty (hs : IsBarrel 𝕜 s) : s.Nonempty :=
  ⟨0, hs.zero_mem⟩

/-- The intersection of two barrels is a barrel. -/
theorem inter (hs : IsBarrel 𝕜 s) (ht : IsBarrel 𝕜 t) : IsBarrel 𝕜 (s ∩ t) :=
  ⟨hs.isClosed.inter ht.isClosed, hs.convex.inter ht.convex, hs.balanced.inter ht.balanced,
    fun x ↦ (hs.absorbent x).inter (ht.absorbent x)⟩

end IsBarrel

/-- The closure of a `ℝ`-convex, balanced and absorbent set is a barrel. -/
theorem isBarrel_closure [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [ContinuousConstSMul ℝ E]
    (hc : Convex ℝ s) (hb : Balanced 𝕜 s) (ha : Absorbent 𝕜 s) : IsBarrel 𝕜 (closure s) :=
  ⟨isClosed_closure, hc.closure, hb.closure, ha.mono subset_closure⟩

end Basic

section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] {s : Set E}

/-- Closed balls of positive radius of a lower semicontinuous seminorm are barrels. -/
theorem Seminorm.isBarrel_closedBall (p : Seminorm 𝕜 E) (hp : LowerSemicontinuous p) {r : ℝ}
    (hr : 0 < r) : IsBarrel 𝕜 (p.closedBall 0 r) where
  isClosed := by simpa [p.closedBall_zero_eq] using! hp.isClosed_preimage r
  convex := p.convex_closedBall 0 r
  balanced := p.balanced_closedBall_zero r
  absorbent := p.absorbent_closedBall_zero hr

namespace IsBarrel

/-- The gauge of a barrel, as a seminorm. -/
@[expose]
noncomputable def gaugeSeminorm (hs : IsBarrel 𝕜 s) : Seminorm 𝕜 E :=
  _root_.gaugeSeminorm hs.balanced hs.convex hs.absorbent.restrictScalars_real

/-- The gauge seminorm of a barrel is its gauge. -/
@[simp]
theorem gaugeSeminorm_apply (hs : IsBarrel 𝕜 s) (x : E) : hs.gaugeSeminorm x = gauge s x :=
  rfl

variable [ContinuousSMul ℝ E]

/-- A barrel is the set where its gauge is at most one. -/
theorem setOfPred_gauge_le_one (hs : IsBarrel 𝕜 s) : {x | gauge s x ≤ 1} = s :=
  Subset.antisymm
    (fun _ hx ↦ hs.isClosed.closure_eq ▸ mem_closure_of_gauge_le_one hs.convex hs.zero_mem
      hs.absorbent.restrictScalars_real hx)
    self_subset_setOfPred_gauge_le_one

/-- A barrel is the closed unit ball of its gauge seminorm. -/
theorem closedBall_gaugeSeminorm (hs : IsBarrel 𝕜 s) : hs.gaugeSeminorm.closedBall 0 1 = s := by
  rw [Seminorm.closedBall_zero_eq]
  exact hs.setOfPred_gauge_le_one

/-- The gauge of a barrel is lower semicontinuous. -/
theorem lowerSemicontinuous_gauge (hs : IsBarrel 𝕜 s) : LowerSemicontinuous (gauge s) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  rcases lt_or_ge a 0 with ha | ha
  · have : gauge s ⁻¹' Iic a = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ (ha.trans_le (gauge_nonneg x)).not_ge hx
    rw [this]
    exact isClosed_empty
  · have : gauge s ⁻¹' Iic a = ⋂ (r : ℝ) (_ : a < r), r • s :=
      setOfPred_gauge_le_eq hs.convex hs.zero_mem hs.absorbent.restrictScalars_real ha
    rw [this]
    exact isClosed_iInter fun r ↦ isClosed_iInter fun hr ↦
      hs.isClosed.smul_of_ne_zero (ha.trans_lt hr).ne'

/-- The gauge seminorm of a barrel is lower semicontinuous. -/
theorem lowerSemicontinuous_gaugeSeminorm (hs : IsBarrel 𝕜 s) :
    LowerSemicontinuous hs.gaugeSeminorm :=
  hs.lowerSemicontinuous_gauge

/-- In a barrelled space every barrel is a neighbourhood of zero. -/
theorem mem_nhds_zero [BarrelledSpace 𝕜 E] (hs : IsBarrel 𝕜 s) : s ∈ 𝓝 (0 : E) := by
  have hc : Continuous hs.gaugeSeminorm :=
    Seminorm.continuous_of_lowerSemicontinuous _ hs.lowerSemicontinuous_gaugeSeminorm
  have h : {x | hs.gaugeSeminorm x < 1} ∈ 𝓝 (0 : E) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  refine mem_of_superset h fun x hx ↦ ?_
  rw [← hs.closedBall_gaugeSeminorm, Seminorm.mem_closedBall_zero]
  exact le_of_lt hx

end IsBarrel

/-- Barrels are exactly the closed unit balls of lower semicontinuous seminorms. -/
theorem isBarrel_iff_exists_seminorm [ContinuousSMul ℝ E] :
    IsBarrel 𝕜 s ↔ ∃ p : Seminorm 𝕜 E, LowerSemicontinuous p ∧ p.closedBall 0 1 = s :=
  ⟨fun hs ↦ ⟨hs.gaugeSeminorm, hs.lowerSemicontinuous_gaugeSeminorm, hs.closedBall_gaugeSeminorm⟩,
    fun ⟨p, hp, hps⟩ ↦ hps ▸ p.isBarrel_closedBall hp one_pos⟩

/-- A topological vector space in which every barrel is a neighbourhood of zero is barrelled. -/
theorem BarrelledSpace.of_forall_isBarrel_mem_nhds [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] (h : ∀ s : Set E, IsBarrel 𝕜 s → s ∈ 𝓝 (0 : E)) :
    BarrelledSpace 𝕜 E where
  continuous_of_lowerSemicontinuous p hp :=
    Seminorm.continuous' (r := 1) (h _ (p.isBarrel_closedBall hp one_pos))

/-- A topological vector space over `ℝ` or `ℂ` is barrelled if and only if every barrel is a
neighbourhood of zero. -/
theorem barrelledSpace_iff_forall_isBarrel_mem_nhds [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] [ContinuousSMul ℝ E] :
    BarrelledSpace 𝕜 E ↔ ∀ s : Set E, IsBarrel 𝕜 s → s ∈ 𝓝 (0 : E) :=
  ⟨fun _ _ hs ↦ hs.mem_nhds_zero, BarrelledSpace.of_forall_isBarrel_mem_nhds⟩

variable (𝕜 E) in
/-- In a polynormable space, in particular in a locally convex space, the barrels that are
neighbourhoods of zero form a basis of neighbourhoods of zero. -/
theorem nhds_zero_hasBasis_isBarrel [PolynormableSpace 𝕜 E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E ↦ s ∈ 𝓝 (0 : E) ∧ IsBarrel 𝕜 s) id := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨s, ⟨hs, _⟩, hsU⟩ ↦ mem_of_superset hs hsU⟩⟩
  obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball 𝕜 E).mem_iff.1 hU
  have hp : Continuous p := hp
  refine ⟨p.closedBall 0 2⁻¹,
    ⟨?_, p.isBarrel_closedBall hp.lowerSemicontinuous (by norm_num)⟩, ?_⟩
  · have h : {x | p x < 2⁻¹} ∈ 𝓝 (0 : E) :=
      (isOpen_lt hp continuous_const).mem_nhds (by simp)
    refine mem_of_superset h fun x hx ↦ ?_
    rw [Seminorm.mem_closedBall_zero]
    exact le_of_lt hx
  · refine Subset.trans (fun x hx ↦ ?_) hpU
    rw [id, Seminorm.mem_closedBall_zero] at hx
    rw [Seminorm.mem_ball_zero]
    linarith

section NearContinuity

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The closure of the preimage under a linear map of a `ℝ`-convex, balanced and absorbent set is
a barrel. The linear map is not assumed to be continuous. -/
theorem isBarrel_closure_preimage (f : E →ₗ[𝕜] F) {V : Set F} (hc : Convex ℝ V)
    (hb : Balanced 𝕜 V) (ha : Absorbent 𝕜 V) : IsBarrel 𝕜 (closure (f ⁻¹' V)) :=
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  isBarrel_closure (hc.is_linear_preimage (f.restrictScalars ℝ).isLinear)
    (hb.preimage f) (ha.preimage f)

/-- A linear map from a barrelled space is *nearly continuous*: the closure of the preimage of a
`ℝ`-convex balanced neighbourhood of zero is a neighbourhood of zero. The linear map is not assumed
to be continuous. -/
theorem LinearMap.closure_preimage_mem_nhds_of_barrelledSpace [BarrelledSpace 𝕜 E]
    [TopologicalSpace F]
    [ContinuousSMul 𝕜 F] (f : E →ₗ[𝕜] F) {V : Set F} (hc : Convex ℝ V) (hb : Balanced 𝕜 V)
    (hV : V ∈ 𝓝 (0 : F)) : closure (f ⁻¹' V) ∈ 𝓝 (0 : E) :=
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  (isBarrel_closure_preimage f hc hb (absorbent_nhds_zero hV)).mem_nhds_zero

end NearContinuity

section Preimage

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The preimage of a barrel under a continuous linear map is a barrel. -/
theorem IsBarrel.preimage {s : Set F} (hs : IsBarrel 𝕜 s) (f : E →L[𝕜] F) :
    IsBarrel 𝕜 (f ⁻¹' s) :=
  ⟨hs.isClosed.preimage f.continuous,
    hs.convex.is_linear_preimage (f.toLinearMap.restrictScalars ℝ).isLinear,
    hs.balanced.preimage f.toLinearMap, hs.absorbent.preimage f.toLinearMap⟩

end Preimage

section NearOpenness

variable [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

omit [TopologicalSpace E] [ContinuousSMul 𝕜 E] in
/-- The closure of the image under a surjective linear map of a `ℝ`-convex, balanced and absorbent
set is a barrel. The linear map is not assumed to be continuous. -/
theorem isBarrel_closure_image {f : E →ₗ[𝕜] F} (hf : Function.Surjective f) {U : Set E}
    (hc : Convex ℝ U) (hb : Balanced 𝕜 U) (ha : Absorbent 𝕜 U) :
    IsBarrel 𝕜 (closure (f '' U)) :=
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  isBarrel_closure (hc.is_linear_image (f.restrictScalars ℝ).isLinear)
    (hb.image f) (ha.image_of_surjective hf)

/-- A surjective linear map onto a barrelled space is *nearly open*: the closure of the image
of a `ℝ`-convex balanced neighbourhood of zero is a neighbourhood of zero. The linear map is not
assumed to be continuous. -/
theorem LinearMap.closure_image_mem_nhds_of_barrelledSpace [BarrelledSpace 𝕜 F] {f : E →ₗ[𝕜] F}
    (hf : Function.Surjective f) {U : Set E} (hc : Convex ℝ U) (hb : Balanced 𝕜 U)
    (hU : U ∈ 𝓝 (0 : E)) : closure (f '' U) ∈ 𝓝 (0 : F) :=
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  (isBarrel_closure_image hf hc hb (absorbent_nhds_zero hU)).mem_nhds_zero

end NearOpenness

end RCLike
