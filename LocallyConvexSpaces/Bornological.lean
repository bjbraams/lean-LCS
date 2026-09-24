/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.FinalTopology
public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Bornological and ultrabornological spaces

A subset of a topological vector space is *bornivorous* if it absorbs every bounded set. A
topological vector space is *bornological* if every seminorm that is bounded on the bounded sets is
continuous. This follows Mathlib's seminorm definition of `BarrelledSpace` and makes sense over any
seminormed ring. For real or complex spaces it is equivalent to the classical condition that every
convex, balanced, bornivorous set is a neighbourhood of zero, and it implies that every linear map
into a locally convex space that maps bounded sets to bounded sets is continuous.

A topological vector space `E` is *ultrabornological* if every seminorm whose compositions with
the continuous linear maps from complete seminormed spaces into `E` are continuous is itself
continuous. The test spaces are taken in the universe of `E`, as for Mathlib's
`CompactlyGeneratedSpace`. For a real or complex locally convex space this says that `E` is an
inductive limit of Banach spaces: its topology is the final locally convex topology of the
continuous linear maps from complete seminormed spaces, and also of the inclusions of the spaces
spanned by its Banach disks (`LocallyConvexSpaces.UltrabornologicalBanachDisk`). Complete
seminormed rather than normed test spaces make the definition behave well without separation.

Ultrabornological spaces are the natural domains for De Wilde's closed graph theorem: a linear
map on such a space is continuous as soon as its restrictions to Banach spaces are.

## Main definitions

* `Bornology.IsBornivorous 𝕜 s`: the set `s` absorbs every von Neumann bounded set.
* `BornologicalSpace 𝕜 E`: every seminorm on `E` that is bounded on the von Neumann bounded
  sets is continuous.
* `UltrabornologicalSpace 𝕜 E`: every seminorm on `E` whose compositions with the continuous
  linear maps from complete seminormed spaces are continuous is continuous.

## Main statements

* `Bornology.IsBornivorous.mem_nhds_zero_of_firstCountableTopology`: every bornivorous set in a
  first-countable topological vector space is a neighbourhood of zero.
* `Seminorm.isBornivorous_ball`, `Seminorm.bddAbove_image_of_isBornivorous`: a seminorm is
  bounded on the bounded sets if and only if its balls are bornivorous.
* `BornologicalSpace.mem_nhds_zero`, `BornologicalSpace.of_forall_mem_nhds_zero`,
  `bornologicalSpace_iff_forall_mem_nhds_zero`: the characterization of real or complex
  bornological spaces by convex, balanced, bornivorous sets.
* `BornologicalSpace.of_firstCountableTopology`: first-countable (in particular metrizable, in
  particular normed) spaces are bornological.
* `LinearMap.continuous_of_forall_isVonNBounded_image`: a linear map from a bornological space
  to a polynormable space that maps bounded sets to bounded sets is continuous.
* `locallyConvexFinalTopology.bornologicalSpace`: inductive limits of bornological spaces are
  bornological.
* `BornologicalSpace.of_restrictScalars`: real-bornological spaces with a compatible
  real or complex topological scalar action are bornological over those scalars.
* `UltrabornologicalSpace.toBornologicalSpace`, `UltrabornologicalSpace.toBarrelledSpace`:
  ultrabornological spaces are bornological and barrelled.
* `UltrabornologicalSpace.of_completeSpace_normedSpace`: complete seminormed spaces, in
  particular Banach spaces, are ultrabornological.
* `UltrabornologicalSpace.continuous_of_forall_comp`: a linear map from an ultrabornological
  space `E` to a polynormable space is continuous as soon as its composition with every
  continuous linear map from a complete seminormed space into `E` is continuous.
* `UltrabornologicalSpace.mem_nhds_zero`, `UltrabornologicalSpace.of_forall_mem_nhds_zero`,
  `ultrabornologicalSpace_iff_forall_mem_nhds_zero`: the characterization of real or complex
  ultrabornological spaces by convex, balanced, absorbent sets.
* `UltrabornologicalSpace.of_eq_locallyConvexFinalTopology`: a final locally convex topology of
  complete seminormed spaces is ultrabornological.
* `locallyConvexFinalTopology.ultrabornologicalSpace`: inductive limits of ultrabornological
  spaces are ultrabornological.

## Implementation notes

The imported proof of `mem_nhds_zero_of_forall_absorbs_range` in `TopologicalVectorSpaces.Basic`
follows that of `LinearMap.continuousAt_zero_of_locally_bounded` in
`Mathlib/Analysis/LocallyConvex/ContinuousOfBounded.lean`, which is the same argument for linear
maps.

That Fréchet spaces are ultrabornological is proved in
`LocallyConvexSpaces.FrechetUltrabornological`, through maps from `ℓ¹`. Banach disks (the normed
spaces spanned by bounded, convex, balanced sets) are in `LocallyConvexSpaces.BanachDisk`; that
every quasi-complete bornological space is ultrabornological is in
`LocallyConvexSpaces.BornologicalUltrabornological`, and the characterizations of
ultrabornological spaces by Banach disks, compact disks and fast convergent sequences are in
`LocallyConvexSpaces.UltrabornologicalBanachDisk`,
`LocallyConvexSpaces.UltrabornologicalCompactDisk` and `LocallyConvexSpaces.FastConvergence`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §2
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §8
* [L. Narici and E. Beckenstein, *Topological Vector Spaces*][narici2010], Chapter 13

## Tags

bornological space, ultrabornological space, bornivorous, inductive limit of Banach spaces
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

universe u v

section Bornivorous

variable (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A set is **bornivorous** if it absorbs every von Neumann bounded set. -/
@[expose]
def Bornology.IsBornivorous (s : Set E) : Prop :=
  ∀ t : Set E, IsVonNBounded 𝕜 t → Absorbs 𝕜 s t

variable {𝕜}

/-- A neighbourhood of zero is bornivorous. -/
theorem Bornology.isBornivorous_of_mem_nhds {s : Set E} (hs : s ∈ 𝓝 (0 : E)) : IsBornivorous 𝕜 s :=
  fun _ ht ↦ ht hs

/-- A superset of a bornivorous set is bornivorous. -/
theorem Bornology.IsBornivorous.mono {s t : Set E} (hs : IsBornivorous 𝕜 s) (hst : s ⊆ t) :
    IsBornivorous 𝕜 t := fun u hu ↦ (hs u hu).mono_left hst

/-- A bornivorous set is absorbent. -/
theorem Bornology.IsBornivorous.absorbent [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsBornivorous 𝕜 s) :
    Absorbent 𝕜 s :=
  fun x ↦ hs {x} (isVonNBounded_singleton x)

/-- The preimage of a bornivorous set under a linear map that maps bounded sets to bounded sets
is bornivorous. -/
theorem Bornology.IsBornivorous.preimage {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F]
    {s : Set F} (hs : IsBornivorous 𝕜 s) (f : E →ₗ[𝕜] F)
    (hf : ∀ t : Set E, IsVonNBounded 𝕜 t → IsVonNBounded 𝕜 (f '' t)) :
    IsBornivorous 𝕜 (f ⁻¹' s) := by
  intro t ht
  filter_upwards [hs _ (hf t ht), eventually_ne_cobounded (0 : 𝕜)] with c hc hc0 x hx
  obtain ⟨y, hy, hxy⟩ := hc ⟨x, hx, rfl⟩
  refine ⟨c⁻¹ • x, ?_, smul_inv_smul₀ hc0 x⟩
  have h1 : f (c⁻¹ • x) = y := by
    rw [map_smul, ← hxy]
    exact inv_smul_smul₀ hc0 y
  rw [mem_preimage, h1]
  exact hy

/-- In a first-countable topological vector space every bornivorous set is a neighbourhood of
zero. -/
theorem Bornology.IsBornivorous.mem_nhds_zero_of_firstCountableTopology [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] {s : Set E} (hs : IsBornivorous 𝕜 s) :
    s ∈ 𝓝 (0 : E) :=
  mem_nhds_zero_of_forall_absorbs_range fun _ hx ↦ hs _ (hx.isVonNBounded_range 𝕜)

end Bornivorous

section SeminormBounds

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A seminorm is bounded on every set that is absorbed by its closed unit ball. -/
theorem Seminorm.bddAbove_image_of_absorbs_closedBall (p : Seminorm 𝕜 E) {t : Set E}
    (h : Absorbs 𝕜 (p.closedBall 0 1) t) : BddAbove (p '' t) := by
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp h
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
  refine ⟨‖c‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hr c hc.le hx
  rw [map_smul_eq_mul]
  exact mul_le_of_le_one_right (norm_nonneg c) (p.mem_closedBall_zero.mp hy)

/-- The open balls of positive radius of a seminorm that is bounded on the von Neumann bounded
sets are bornivorous. -/
theorem Seminorm.isBornivorous_ball [TopologicalSpace E] (p : Seminorm 𝕜 E)
    (hp : ∀ s : Set E, IsVonNBounded 𝕜 s → BddAbove (p '' s)) {r : ℝ} (hr : 0 < r) :
    IsBornivorous 𝕜 (p.ball 0 r) := by
  intro s hs
  obtain ⟨C, hC⟩ := hp s hs
  refine (p.ball_zero_absorbs_ball_zero (r₂ := C + 1) hr).mono_right fun x hx ↦ ?_
  rw [p.mem_ball_zero]
  exact (hC ⟨x, hx, rfl⟩).trans_lt (lt_add_one C)

/-- A seminorm whose closed unit ball contains a bornivorous set is bounded on the von Neumann
bounded sets. -/
theorem Seminorm.bddAbove_image_of_isBornivorous [TopologicalSpace E] (p : Seminorm 𝕜 E)
    {s : Set E} (hs : IsBornivorous 𝕜 s) (hsp : s ⊆ p.closedBall 0 1) {t : Set E}
    (ht : IsVonNBounded 𝕜 t) : BddAbove (p '' t) :=
  p.bddAbove_image_of_absorbs_closedBall ((hs.mono hsp) t ht)

end SeminormBounds

section Bornological

variable (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] [TopologicalSpace E]

/-- A topological vector space is **bornological** if every seminorm that is bounded on the von
Neumann bounded sets is continuous. This mirrors Mathlib's seminorm definition of
`BarrelledSpace`. For real or complex spaces it is equivalent to the classical condition that
every convex, balanced, bornivorous set is a neighbourhood of zero; see
`bornologicalSpace_iff_forall_mem_nhds_zero`. -/
class BornologicalSpace : Prop where
  /-- In a bornological space every seminorm that is bounded on the bounded sets is
  continuous. -/
  continuous_of_bddAbove : ∀ p : Seminorm 𝕜 E,
    (∀ s : Set E, IsVonNBounded 𝕜 s → BddAbove (p '' s)) → Continuous p

end Bornological

section BornologicalField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- A topological vector space in which every bornivorous set is a neighbourhood of zero is
bornological. -/
theorem BornologicalSpace.of_forall_isBornivorous_mem_nhds [ContinuousConstSMul 𝕜 E]
    (h : ∀ s : Set E, IsBornivorous 𝕜 s → s ∈ 𝓝 (0 : E)) : BornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ Seminorm.continuous (r := 1) (h _ (p.isBornivorous_ball hp one_pos))⟩

/-- A first-countable topological vector space is bornological. In particular metrizable
locally convex spaces and normed spaces are bornological. -/
instance (priority := 100) BornologicalSpace.of_firstCountableTopology [ContinuousSMul 𝕜 E]
    [FirstCountableTopology E] : BornologicalSpace 𝕜 E :=
  .of_forall_isBornivorous_mem_nhds fun _ hs ↦ hs.mem_nhds_zero_of_firstCountableTopology

/-- A linear map from a bornological space to a polynormable space, in particular to a locally
convex space, that maps bounded sets to bounded sets is continuous. -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image [BornologicalSpace 𝕜 E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [PolynormableSpace 𝕜 F]
    (f : E →ₗ[𝕜] F)
    (hf : ∀ t : Set E, IsVonNBounded 𝕜 t → IsVonNBounded 𝕜 (f '' t)) : Continuous f := by
  have hq := PolynormableSpace.withSeminorms 𝕜 F
  refine hq.continuous_of_continuous_comp f fun q ↦
    BornologicalSpace.continuous_of_bddAbove _ fun t ht ↦ ?_
  obtain ⟨r, -, hr⟩ := hq.isVonNBounded_iff_seminorm_bounded.mp (hf t ht) q
  exact ⟨r, by rintro _ ⟨x, hx, rfl⟩; exact (hr (f x) ⟨x, hx, rfl⟩).le⟩

end BornologicalField

section BornologicalRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- In a real or complex bornological space every convex, balanced, bornivorous set is a
neighbourhood of zero. -/
theorem BornologicalSpace.mem_nhds_zero [BornologicalSpace 𝕜 E] (s : Set E) (hc : Convex ℝ s)
    (hb : Balanced 𝕜 s) (hs : IsBornivorous 𝕜 s) : s ∈ 𝓝 (0 : E) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have ha := hs.absorbent.restrictScalars_real
  set p := gaugeSeminorm hb hc ha
  have hsp : s ⊆ p.closedBall 0 1 := fun x hx ↦ by
    rw [p.mem_closedBall_zero, gaugeSeminorm_toFun]
    exact gauge_le_one_of_mem hx
  have hpc : Continuous p := BornologicalSpace.continuous_of_bddAbove p fun _ ht ↦
    p.bddAbove_image_of_isBornivorous hs hsp ht
  refine mem_of_superset ((p.continuous_iff one_pos).mp hpc) fun x hx ↦ ?_
  rw [p.mem_ball_zero, gaugeSeminorm_toFun] at hx
  exact setOfPred_gauge_lt_one_subset_self hc hs.absorbent.zero_mem ha hx

/-- A real or complex topological vector space in which every convex, balanced, bornivorous set
is a neighbourhood of zero is bornological. -/
theorem BornologicalSpace.of_forall_mem_nhds_zero
    (h : ∀ s : Set E, Convex ℝ s → Balanced 𝕜 s → IsBornivorous 𝕜 s → s ∈ 𝓝 (0 : E)) :
    BornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ Seminorm.continuous (r := 1) (h _ (p.convex_ball 0 1) (p.balanced_ball_zero 1)
    (p.isBornivorous_ball hp one_pos))⟩

/-- A real or complex topological vector space is bornological if and only if every convex,
balanced, bornivorous set is a neighbourhood of zero. -/
theorem bornologicalSpace_iff_forall_mem_nhds_zero :
    BornologicalSpace 𝕜 E ↔
      ∀ s : Set E, Convex ℝ s → Balanced 𝕜 s → IsBornivorous 𝕜 s → s ∈ 𝓝 (0 : E) :=
  ⟨fun _ ↦ BornologicalSpace.mem_nhds_zero, BornologicalSpace.of_forall_mem_nhds_zero⟩

omit [IsTopologicalAddGroup E] in
/-- A real-bornological space with a compatible real or complex topological scalar action
is bornological over those scalars. -/
theorem BornologicalSpace.of_restrictScalars [BornologicalSpace ℝ E] : BornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ BornologicalSpace.continuous_of_bddAbove (p.restrictScalars ℝ)
    fun s hs ↦ hp s (hs.extend_scalars 𝕜)⟩

end BornologicalRCLike

section FinalTopology

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The final locally convex topology for a family of maps from bornological spaces is
bornological. In particular inductive limits of bornological spaces are bornological. -/
theorem locallyConvexFinalTopology.bornologicalSpace [∀ i, BornologicalSpace 𝕜 (E i)]
    (f : ∀ i, E i →ₗ[𝕜] F) :
    @BornologicalSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  have h2 : ContinuousSMul 𝕜 F := locallyConvexFinalTopology.continuousSMul f
  refine BornologicalSpace.of_forall_mem_nhds_zero fun s hc hb hs ↦ ?_
  refine locallyConvexFinalTopology.mem_nhds_zero f hc hb hs.absorbent fun i ↦ ?_
  have hfi : Continuous (f i) := locallyConvexFinalTopology.continuous_apply f i
  exact BornologicalSpace.mem_nhds_zero _
    (hc.is_linear_preimage ((f i).restrictScalars ℝ).isLinear) (hb.preimage (f i))
    (hs.preimage (f i) fun t ht ↦ ht.image (⟨f i, hfi⟩ : E i →L[𝕜] F))

end FinalTopology

section Ultrabornological

variable (𝕜 : Type*) (E : Type u) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A topological vector space `E` is **ultrabornological** if every seminorm on `E` whose
composition with every continuous linear map from a complete seminormed space into `E` is
continuous, is itself continuous. This mirrors Mathlib's seminorm definition of
`BarrelledSpace`, with the bounded sets of `BornologicalSpace` replaced by the images of complete
seminormed spaces. The test spaces are taken in the universe of `E`, as for Mathlib's
`CompactlyGeneratedSpace`; this suffices because the spaces `E_B` spanned by Banach disks lie in
that universe. For a real or complex locally convex space it says that the topology is the final
locally convex topology of the continuous linear maps from Banach spaces
(`UltrabornologicalSpace.of_eq_locallyConvexFinalTopology`,
`UltrabornologicalSpace.eq_locallyConvexFinalTopology_banachDisks`). -/
class UltrabornologicalSpace : Prop where
  /-- In an ultrabornological space a seminorm is continuous as soon as its compositions with
  the continuous linear maps from complete seminormed spaces are continuous. -/
  continuous_of_forall_continuous_comp : ∀ p : Seminorm 𝕜 E,
    (∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      (f : X →L[𝕜] E), Continuous fun x ↦ p (f x)) → Continuous p

variable {𝕜 E}

/-- A seminorm on a seminormed space that is bounded on the closed unit ball is continuous. -/
theorem Seminorm.continuous_of_bddAbove_closedBall {X : Type*} [SeminormedAddCommGroup X]
    [NormedSpace 𝕜 X] (q : Seminorm 𝕜 X) (h : BddAbove (q '' Metric.closedBall (0 : X) 1)) :
    Continuous q := by
  obtain ⟨C, hC⟩ := h
  refine Seminorm.continuous (r := C + 1)
    (mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun x hx ↦ ?_)
  rw [q.mem_ball_zero]
  exact (hC ⟨x, Metric.ball_subset_closedBall hx, rfl⟩).trans_lt (lt_add_one C)

/-- A continuous seminorm on a seminormed space is bounded on the closed unit ball. -/
theorem Seminorm.bddAbove_image_closedBall_of_continuous {X : Type*} [SeminormedAddCommGroup X]
    [NormedSpace 𝕜 X] (q : Seminorm 𝕜 X) (hq : Continuous q) :
    BddAbove (q '' Metric.closedBall (0 : X) 1) := by
  obtain ⟨C, hC, h⟩ := q.bound_of_continuous_normedSpace hq
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (h x).trans (mul_le_of_le_one_right hC.le (mem_closedBall_zero_iff.mp hx))

/-- An ultrabornological space is bornological. -/
instance (priority := 100) UltrabornologicalSpace.toBornologicalSpace
    [UltrabornologicalSpace 𝕜 E] : BornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ UltrabornologicalSpace.continuous_of_forall_continuous_comp p fun X _ _ _ f ↦ by
    obtain ⟨C, hC⟩ := hp _ ((NormedSpace.isVonNBounded_closedBall 𝕜 X 1).image f)
    exact (p.comp f.toLinearMap).continuous_of_bddAbove_closedBall
      ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC ⟨f x, ⟨x, hx, rfl⟩, rfl⟩⟩⟩

/-- An ultrabornological space is barrelled: a lower semicontinuous seminorm is continuous on
every complete seminormed space, which is barrelled by Baire's theorem. -/
instance (priority := 100) UltrabornologicalSpace.toBarrelledSpace
    [UltrabornologicalSpace 𝕜 E] : BarrelledSpace 𝕜 E :=
  ⟨fun p hp ↦ UltrabornologicalSpace.continuous_of_forall_continuous_comp p fun _ _ _ _ f ↦
    (p.comp f.toLinearMap).continuous_of_lowerSemicontinuous (hp.comp f.continuous)⟩

/-- A complete seminormed space, in particular a Banach space, is ultrabornological. -/
instance (priority := 100) UltrabornologicalSpace.of_completeSpace_normedSpace {X : Type u}
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] :
    UltrabornologicalSpace 𝕜 X :=
  ⟨fun _ hp ↦ hp X (ContinuousLinearMap.id 𝕜 X)⟩

/-- A linear map `g` from an ultrabornological space `E` to a polynormable space, in particular
to a locally convex space, is continuous as soon as `g ∘ f` is continuous for every continuous
linear map `f` from a complete seminormed space into `E`. This reduces continuity questions on
ultrabornological spaces to Banach spaces. -/
theorem UltrabornologicalSpace.continuous_of_forall_comp [UltrabornologicalSpace 𝕜 E]
    [IsTopologicalAddGroup E] {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [PolynormableSpace 𝕜 G] (g : E →ₗ[𝕜] G)
    (h : ∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      (f : X →L[𝕜] E), Continuous (g ∘ f)) :
    Continuous g :=
  (PolynormableSpace.withSeminorms 𝕜 G).continuous_of_continuous_comp g fun q ↦
    UltrabornologicalSpace.continuous_of_forall_continuous_comp _ fun X _ _ _ f ↦
      q.2.comp (h X f)

end Ultrabornological

section UltrabornologicalRCLike

variable {𝕜 : Type*} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-- In a real or complex ultrabornological space a convex, balanced, absorbent set is a
neighbourhood of zero as soon as its preimage under every continuous linear map from a complete
seminormed space is a neighbourhood of zero. -/
theorem UltrabornologicalSpace.mem_nhds_zero [UltrabornologicalSpace 𝕜 E] {S : Set E}
    (hc : Convex ℝ S) (hb : Balanced 𝕜 S) (ha : Absorbent 𝕜 S)
    (h : ∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      (f : X →L[𝕜] E), f ⁻¹' S ∈ 𝓝 (0 : X)) :
    S ∈ 𝓝 (0 : E) := by
  set p := gaugeSeminorm hb hc ha.restrictScalars_real
  have hpc : Continuous p :=
    UltrabornologicalSpace.continuous_of_forall_continuous_comp p fun X _ _ _ f ↦
      Seminorm.continuous' (p := p.comp f.toLinearMap) (r := 1) (mem_of_superset (h X f)
        fun x hx ↦ by
          rw [Seminorm.mem_closedBall_zero, Seminorm.comp_apply]
          exact gauge_le_one_of_mem hx)
  refine mem_of_superset ((hpc.isOpen_preimage _ (isOpen_Iio (a := (1 : ℝ)))).mem_nhds
    (by simp)) fun x hx ↦ ?_
  exact setOfPred_gauge_lt_one_subset_self hc ha.zero_mem ha.restrictScalars_real hx

/-- A real or complex topological vector space is ultrabornological if every convex, balanced,
absorbent set whose preimages under the continuous linear maps from complete seminormed spaces
are neighbourhoods of zero is itself a neighbourhood of zero. -/
theorem UltrabornologicalSpace.of_forall_mem_nhds_zero [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E]
    (h : ∀ S : Set E, Convex ℝ S → Balanced 𝕜 S → Absorbent 𝕜 S →
      (∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
        (f : X →L[𝕜] E), f ⁻¹' S ∈ 𝓝 (0 : X)) → S ∈ 𝓝 (0 : E)) :
    UltrabornologicalSpace 𝕜 E :=
  ⟨fun p hp ↦ Seminorm.continuous (r := 1) (h _ (p.convex_ball 0 1) (p.balanced_ball_zero 1)
    (p.absorbent_ball_zero one_pos) fun X _ _ _ f ↦
      mem_of_superset (((hp X f).isOpen_preimage _ (isOpen_Iio (a := (1 : ℝ)))).mem_nhds
        (by simp)) fun x hx ↦ by
          rw [mem_preimage, p.mem_ball_zero]
          exact hx)⟩

/-- A real or complex topological vector space is ultrabornological if and only if every
convex, balanced, absorbent set whose preimages under the continuous linear maps from complete
seminormed spaces are neighbourhoods of zero is itself a neighbourhood of zero. -/
theorem ultrabornologicalSpace_iff_forall_mem_nhds_zero [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] :
    UltrabornologicalSpace 𝕜 E ↔
      ∀ S : Set E, Convex ℝ S → Balanced 𝕜 S → Absorbent 𝕜 S →
        (∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
          (f : X →L[𝕜] E), f ⁻¹' S ∈ 𝓝 (0 : X)) → S ∈ 𝓝 (0 : E) :=
  ⟨fun _ _ hc hb ha h ↦ UltrabornologicalSpace.mem_nhds_zero hc hb ha h,
    UltrabornologicalSpace.of_forall_mem_nhds_zero⟩

/-- A space whose topology is the final locally convex topology for a family of linear maps
from complete seminormed spaces is ultrabornological. The spaces of the family lie in the
universe of `E`; for arbitrary universes see
`UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_of_completeSpace`. -/
theorem UltrabornologicalSpace.of_eq_locallyConvexFinalTopology {ι : Type*} {X : ι → Type u}
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)] [∀ i, CompleteSpace (X i)]
    (f : ∀ i, X i →ₗ[𝕜] E)
    (h : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology f) :
    UltrabornologicalSpace 𝕜 E := by
  refine ⟨fun p hp ↦ ?_⟩
  have hfi (i : ι) : Continuous (f i) := by
    have h1 := locallyConvexFinalTopology.continuous_apply f i
    rwa [← h] at h1
  have key := locallyConvexFinalTopology.continuous_seminorm f p fun i ↦ hp (X i) ⟨f i, hfi i⟩
  rwa [← h] at key

end UltrabornologicalRCLike

section UltrabornologicalFinal

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type u} {F : Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The final locally convex topology for a family of maps from ultrabornological spaces is
ultrabornological. In particular inductive limits of ultrabornological spaces, such as LF
spaces, are ultrabornological. The spaces are taken in one universe. -/
theorem locallyConvexFinalTopology.ultrabornologicalSpace
    [∀ i, UltrabornologicalSpace 𝕜 (E i)] (f : ∀ i, E i →ₗ[𝕜] F) :
    @UltrabornologicalSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  refine ⟨fun p hp ↦ locallyConvexFinalTopology.continuous_seminorm f p fun i ↦ ?_⟩
  have hfi : Continuous (f i) := locallyConvexFinalTopology.continuous_apply f i
  exact UltrabornologicalSpace.continuous_of_forall_continuous_comp (p.comp (f i))
    fun X _ _ _ g ↦ hp X ((⟨f i, hfi⟩ : E i →L[𝕜] F).comp g)

end UltrabornologicalFinal
