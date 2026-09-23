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
locally convex space is *bornological* if every convex, balanced, bornivorous set is a
neighbourhood of zero; equivalently, if every linear map into a locally convex space that maps
bounded sets to bounded sets is continuous. A locally convex space is *ultrabornological* if
its topology is the final locally convex topology for a family of linear maps from Banach
spaces, that is, if it is an inductive limit of Banach spaces.

Ultrabornological spaces are the natural domains for De Wilde's closed graph theorem: by the
universal property of the final topology a linear map on such a space is continuous as soon as
its restrictions to the Banach spaces of the family are.

## Main definitions

* `IsBornivorous 𝕜 s`: the set `s` absorbs every von Neumann bounded set.
* `BornologicalSpace 𝕜 E`: every convex, balanced, bornivorous subset of `E` is a neighbourhood
  of zero.
* `UltrabornologicalSpace 𝕜 E`: the topology of `E` is the final locally convex topology for a
  family of linear maps from Banach spaces.

## Main statements

* `IsBornivorous.mem_nhds_zero_of_firstCountable`: every bornivorous set in a first-countable
  topological vector space is a neighbourhood of zero. It uses the imported null-sequence
  absorption lemma `mem_nhds_zero_of_forall_absorbs_range` from `TopologicalVectorSpaces.Basic`.
* `BornologicalSpace.of_firstCountableTopology`: first-countable (in particular metrizable, in
  particular normed) spaces are bornological.
* `LinearMap.continuous_of_forall_isVonNBounded_image`: a linear map from a bornological space
  to a locally convex space that maps bounded sets to bounded sets is continuous.
* `locallyConvexFinalTopology.bornologicalSpace`: inductive limits of bornological spaces are
  bornological.
* `BornologicalSpace.of_restrictScalars`: real-bornological spaces with a compatible
  real or complex topological scalar action are bornological over those scalars.
* `UltrabornologicalSpace.toBornologicalSpace`, `UltrabornologicalSpace.toBarrelledSpace`:
  ultrabornological spaces are bornological and barrelled.
* `locallyConvexFinalTopology.ultrabornologicalSpace`: inductive limits of ultrabornological
  spaces are ultrabornological.
* `UltrabornologicalSpace.of_completeSpace_normedSpace`: Banach spaces are ultrabornological.
* `UltrabornologicalSpace.continuous_of_forall_comp`: a linear map from an ultrabornological
  space `E` to a locally convex space is continuous as soon as its composition with every
  continuous linear map from a Banach space into `E` is continuous.

## Implementation notes

The imported proof of `mem_nhds_zero_of_forall_absorbs_range` in `TopologicalVectorSpaces.Basic`
follows that of
`LinearMap.continuousAt_zero_of_locally_bounded` in
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
def IsBornivorous (s : Set E) : Prop :=
  ∀ t : Set E, IsVonNBounded 𝕜 t → Absorbs 𝕜 s t

variable {𝕜}

/-- A neighbourhood of zero is bornivorous. -/
theorem isBornivorous_of_mem_nhds {s : Set E} (hs : s ∈ 𝓝 (0 : E)) : IsBornivorous 𝕜 s :=
  fun _ ht ↦ ht hs

/-- A superset of a bornivorous set is bornivorous. -/
theorem IsBornivorous.mono {s t : Set E} (hs : IsBornivorous 𝕜 s) (hst : s ⊆ t) :
    IsBornivorous 𝕜 t := fun u hu ↦ (hs u hu).mono_left hst

/-- A bornivorous set is absorbent. -/
theorem IsBornivorous.absorbent [ContinuousSMul 𝕜 E] {s : Set E} (hs : IsBornivorous 𝕜 s) :
    Absorbent 𝕜 s :=
  fun x ↦ hs {x} (isVonNBounded_singleton x)

/-- The preimage of a bornivorous set under a linear map that maps bounded sets to bounded sets
is bornivorous. -/
theorem IsBornivorous.preimage {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
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
theorem IsBornivorous.mem_nhds_zero_of_firstCountable [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] {s : Set E} (hs : IsBornivorous 𝕜 s) :
    s ∈ 𝓝 (0 : E) :=
  mem_nhds_zero_of_forall_absorbs_range fun _ hx ↦ hs _ (hx.isVonNBounded_range 𝕜)

end Bornivorous

section Bornological

variable (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [TopologicalSpace E]

/-- A topological vector space over `ℝ` or `ℂ` is **bornological** if every convex, balanced,
bornivorous set is a neighbourhood of zero. -/
class BornologicalSpace : Prop where
  /-- In a bornological space every convex, balanced, bornivorous set is a neighbourhood of
  zero. -/
  mem_nhds_zero : ∀ s : Set E, Convex ℝ s → Balanced 𝕜 s → IsBornivorous 𝕜 s → s ∈ 𝓝 (0 : E)

variable {𝕜 E}

/-- A first-countable topological vector space is bornological. In particular metrizable
locally convex spaces and normed spaces are bornological. -/
instance (priority := 100) BornologicalSpace.of_firstCountableTopology [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] : BornologicalSpace 𝕜 E :=
  ⟨fun _ _ _ hs ↦ hs.mem_nhds_zero_of_firstCountable⟩

variable [IsScalarTower ℝ 𝕜 E]

/-- A real-bornological space with a compatible real or complex topological scalar action
is bornological over those scalars. -/
theorem BornologicalSpace.of_restrictScalars [ContinuousSMul 𝕜 E]
    [BornologicalSpace ℝ E] : BornologicalSpace 𝕜 E := by
  refine ⟨fun s hc hb hs ↦ BornologicalSpace.mem_nhds_zero (𝕜 := ℝ) s hc ?_ ?_⟩
  · rw [balanced_iff_smul_mem]
    intro a ha x hx
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hb.smul_mem (by simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using ha) hx
  · intro B hB
    apply (hs B (hB.extend_scalars 𝕜)).restrict_scalars
    simpa only [Algebra.smul_def, mul_one, RCLike.algebraMap_eq_ofReal,
      RCLike.ofRealLI_apply] using
      (RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜).isometry.antilipschitzWith.tendsto_cobounded

/-- A linear map from a bornological space to a locally convex space that maps bounded sets to
bounded sets is continuous. -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image [IsTopologicalAddGroup E]
    [BornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] (f : E →ₗ[𝕜] F)
    (hf : ∀ t : Set E, IsVonNBounded 𝕜 t → IsVonNBounded 𝕜 (f '' t)) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  intro V hV
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWV⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  refine mem_of_superset ?_ (preimage_mono hWV)
  exact BornologicalSpace.mem_nhds_zero _
    (hWc.is_linear_preimage (f.restrictScalars ℝ).isLinear) (hWb.preimage f)
    ((isBornivorous_of_mem_nhds hW).preimage f hf)

end Bornological

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
    @BornologicalSpace 𝕜 F _ _ _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  have h2 : ContinuousSMul 𝕜 F := locallyConvexFinalTopology.continuousSMul f
  refine ⟨fun s hc hb hs ↦ ?_⟩
  refine locallyConvexFinalTopology.mem_nhds_zero f hc hb hs.absorbent fun i ↦ ?_
  have hfi : Continuous (f i) := locallyConvexFinalTopology.continuous_apply f i
  exact BornologicalSpace.mem_nhds_zero _
    (hc.is_linear_preimage ((f i).restrictScalars ℝ).isLinear) (hb.preimage (f i))
    (hs.preimage (f i) fun t ht ↦ ht.image (⟨f i, hfi⟩ : E i →L[𝕜] F))

end FinalTopology

section Ultrabornological

variable (𝕜 : Type v) (E : Type u) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [t : TopologicalSpace E]

/-- A topological vector space over `ℝ` or `ℂ` is **ultrabornological** if its topology is the
final locally convex topology for a family of linear maps from Banach spaces. The Banach spaces
are taken in the universe `max u v` of `E` and `𝕜`, so that both subspaces of `E` and sequence
spaces over `𝕜` qualify. -/
class UltrabornologicalSpace : Prop where
  /-- The topology of an ultrabornological space is the final locally convex topology for a
  family of linear maps from Banach spaces. -/
  exists_family : ∃ (ι : Type u) (X : ι → Type (max u v)) (_ : ∀ i, NormedAddCommGroup (X i))
    (_ : ∀ i, NormedSpace 𝕜 (X i)) (_ : ∀ i, NormedSpace ℝ (X i))
    (_ : ∀ i, IsScalarTower ℝ 𝕜 (X i)) (_ : ∀ i, CompleteSpace (X i))
    (f : ∀ i, X i →ₗ[𝕜] E), t = locallyConvexFinalTopology f

variable {𝕜 E} [IsScalarTower ℝ 𝕜 E]

/-- An ultrabornological space is bornological. -/
instance (priority := 100) UltrabornologicalSpace.toBornologicalSpace
    [UltrabornologicalSpace 𝕜 E] : BornologicalSpace 𝕜 E := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  subst hf
  exact locallyConvexFinalTopology.bornologicalSpace f

/-- An ultrabornological space is barrelled. -/
instance (priority := 100) UltrabornologicalSpace.toBarrelledSpace
    [UltrabornologicalSpace 𝕜 E] : BarrelledSpace 𝕜 E := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  subst hf
  exact locallyConvexFinalTopology.barrelledSpace f

variable (𝕜 E) in
omit [IsScalarTower ℝ 𝕜 E] in
/-- An ultrabornological space is a topological additive group. -/
theorem UltrabornologicalSpace.isTopologicalAddGroup [UltrabornologicalSpace 𝕜 E] :
    IsTopologicalAddGroup E := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  subst hf
  exact locallyConvexFinalTopology.isTopologicalAddGroup f

variable (𝕜 E) in
omit [IsScalarTower ℝ 𝕜 E] in
/-- Scalar multiplication on an ultrabornological space is continuous. -/
theorem UltrabornologicalSpace.continuousSMul [UltrabornologicalSpace 𝕜 E] :
    ContinuousSMul 𝕜 E := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  subst hf
  exact locallyConvexFinalTopology.continuousSMul f

variable (𝕜 E) in
omit [IsScalarTower ℝ 𝕜 E] in
/-- An ultrabornological space is locally convex. -/
theorem UltrabornologicalSpace.locallyConvexSpace [UltrabornologicalSpace 𝕜 E] :
    LocallyConvexSpace ℝ E := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  subst hf
  exact locallyConvexFinalTopology.locallyConvexSpace f

/-- A linear map `g` from an ultrabornological space `E` to a locally convex space is continuous
as soon as `g ∘ f` is continuous for every continuous linear map `f` from a Banach space into
`E`. This reduces continuity questions on ultrabornological spaces to Banach spaces. -/
theorem UltrabornologicalSpace.continuous_of_forall_comp [UltrabornologicalSpace 𝕜 E]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [Module ℝ G] [IsScalarTower ℝ 𝕜 G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G] [LocallyConvexSpace ℝ G]
    (g : E →ₗ[𝕜] G)
    (h : ∀ (X : Type (max u v)) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X]
      [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] (f : X →L[𝕜] E), Continuous (g ∘ f)) :
    Continuous g := by
  obtain ⟨ι, X, _, _, _, _, _, f, hf⟩ := UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E)
  have hfi (i : ι) : Continuous (f i) := by
    have h1 := locallyConvexFinalTopology.continuous_apply f i
    rwa [← hf] at h1
  have key := (locallyConvexFinalTopology.continuous_iff f g).mpr
    fun i ↦ h (X i) ⟨f i, hfi i⟩
  rwa [← hf] at key

end Ultrabornological

section UltrabornologicalFinal

universe w u'

variable {𝕜 : Type v} [RCLike 𝕜] {ι : Type w} {E : ι → Type (max w u')} {F : Type (max w u')}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The final locally convex topology for a family of maps from ultrabornological spaces is
ultrabornological. In particular inductive limits of ultrabornological spaces, such as LF
spaces, are ultrabornological. -/
theorem locallyConvexFinalTopology.ultrabornologicalSpace
    [∀ i, UltrabornologicalSpace 𝕜 (E i)] (f : ∀ i, E i →ₗ[𝕜] F) :
    @UltrabornologicalSpace 𝕜 F _ _ _ _ (locallyConvexFinalTopology f) := by
  choose κ X i1 i2 i3 i4 i5 h hh using
    fun i ↦ UltrabornologicalSpace.exists_family (𝕜 := 𝕜) (E := E i)
  exact @UltrabornologicalSpace.mk 𝕜 F _ _ _ _ (locallyConvexFinalTopology f)
    ⟨Σ i, κ i, fun p ↦ X p.1 p.2, fun p ↦ i1 p.1 p.2, fun p ↦ i2 p.1 p.2, fun p ↦ i3 p.1 p.2,
      fun p ↦ i4 p.1 p.2, fun p ↦ i5 p.1 p.2, fun p ↦ f p.1 ∘ₗ h p.1 p.2,
      locallyConvexFinalTopology.trans f h hh⟩

end UltrabornologicalFinal

section Banach

variable {𝕜 : Type v} {X : Type u} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

/-- A Banach space is ultrabornological. -/
instance (priority := 100) UltrabornologicalSpace.of_completeSpace_normedSpace :
    UltrabornologicalSpace 𝕜 X := by
  let f : PUnit.{u + 1} → ULift.{v} X →ₗ[𝕜] X := fun _ ↦ (ULift.moduleEquiv : _ ≃ₗ[𝕜] X)
  refine ⟨PUnit, fun _ ↦ ULift.{v} X, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance, f, ?_⟩
  refine le_antisymm ?_ ?_
  · -- The norm topology is finer: the identity factors through `ULift.up`.
    have h := locallyConvexFinalTopology.continuous_apply f PUnit.unit
    have hup : Continuous (ULift.up : X → ULift.{v} X) := continuous_uliftUp
    have hid : @Continuous X X _ (locallyConvexFinalTopology f) id :=
      @Continuous.comp X (ULift.{v} X) X _ _ (locallyConvexFinalTopology f) _ _ h hup
    exact continuous_id_iff_le.mp hid
  · exact (locallyConvexFinalTopology.le_iff f).mpr fun _ ↦ continuous_uliftDown

end Banach
