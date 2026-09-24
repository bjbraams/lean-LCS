/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TopologicalVectorSpaces.SeminormCompletion
public import TopologicalVectorSpaces.Completion
public import TopologicalVectorSpaces.CountableSeminorms
public import Mathlib.Topology.UniformSpace.AbstractCompletion

/-!
# Projective representation by local Banach spaces

A directed defining family of seminorms gives a system of local Banach spaces
`Seminorm.LocalBanachSpace` and contraction maps between them. Its projective limit is the closed
subspace of compatible families in the product. The original space maps densely and uniformly
inducingly into this limit, which identifies the limit with the separated completion. The proof
uses Mathlib's uniqueness of completions. The directed and monotone defining families are
provided by `TopologicalVectorSpaces.CountableSeminorms`.

## Main definitions

* `SeminormFamily.toLocalBanachSpaceProduct`: the diagonal map into the product of local Banach
  spaces.
* `SeminormFamily.projectiveLimit`: the projective limit of the local Banach spaces.
* `SeminormFamily.toProjectiveLimit`, `SeminormFamily.projectiveLimitLift`: the canonical map
  and the universal property.
* `SeminormFamily.projectiveCompletion`: the projective limit as an `AbstractCompletion`.
* `SeminormFamily.completionEquiv`, `PolynormableSpace.completionEquiv`: the completion as a
  projective limit.

## Main statements

* `SeminormFamily.isUniformInducing_toProjectiveLimit`,
  `SeminormFamily.denseRange_toProjectiveLimit`.
* `SeminormFamily.equivProjectiveLimit`: a complete Hausdorff space is the projective limit of
  its local Banach spaces.
* `PolynormableSpace.exists_countable_completionEquiv`,
  `PolynormableSpace.exists_countable_equivProjectiveLimit`: countable representations in the
  first-countable case, in particular for Fréchet spaces.

## References

* [B. Casselman, *Introduction to Topological Vector Spaces*][casselman2016], §5
-/

@[expose] public noncomputable section

open Set Function UniformSpace
open scoped Topology Uniformity

namespace SeminormFamily

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  (p : SeminormFamily 𝕜 E ι)

/-- The diagonal map into the product of the local Banach spaces. -/
def toLocalBanachSpaceProduct : E →ₗ[𝕜] ∀ i, (p i).LocalBanachSpace :=
  LinearMap.pi fun i ↦ (p i).toLocalBanachSpace

/-- The projective limit consists of families compatible with all seminorm dominations. -/
def projectiveLimit : Submodule 𝕜 (∀ i, (p i).LocalBanachSpace) where
  carrier := {z | ∀ i j (h : p i ≤ p j), Seminorm.LocalBanachSpace.mapOfLE h (z j) = z i}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i j h; simp [map_add, hx i j h, hy i j h]
  smul_mem' := by intro a x hx i j h; simp [map_smul, hx i j h]

/-- Compatibility is a closed condition in the product of local Banach spaces. -/
theorem isClosed_projectiveLimit :
    IsClosed (p.projectiveLimit : Set (∀ i, (p i).LocalBanachSpace)) := by
  change IsClosed {z : ∀ i, (p i).LocalBanachSpace | ∀ i j (h : p i ≤ p j),
    Seminorm.LocalBanachSpace.mapOfLE h (z j) = z i}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro h
  exact isClosed_eq ((Seminorm.LocalBanachSpace.mapOfLE h).continuous.comp (continuous_apply j))
    (continuous_apply i)

/-- The projective limit is complete as a closed subspace of a product of Banach spaces. -/
instance : CompleteSpace p.projectiveLimit :=
  p.isClosed_projectiveLimit.completeSpace_coe

/-- The projective limit carries the induced additive uniformity. -/
instance : IsUniformAddGroup p.projectiveLimit := p.projectiveLimit.toAddSubgroup.isUniformAddGroup

/-- A compatible family of continuous linear maps induces a map into the projective limit. -/
def projectiveLimitLift {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    (f : ∀ i, F →L[𝕜] (p i).LocalBanachSpace)
    (hf : ∀ i j (h : p i ≤ p j) x, Seminorm.LocalBanachSpace.mapOfLE h (f j x) = f i x) :
    F →L[𝕜] p.projectiveLimit where
  toLinearMap := (LinearMap.pi fun i ↦ (f i).toLinearMap).codRestrict _ (fun x i j h ↦ hf i j h x)
  cont := (continuous_pi fun i ↦ (f i).continuous).subtype_mk _

/-- The map induced by a compatible family has the prescribed coordinates. -/
@[simp] theorem projectiveLimitLift_apply {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] (f : ∀ i, F →L[𝕜] (p i).LocalBanachSpace)
    (hf : ∀ i j (h : p i ≤ p j) x, Seminorm.LocalBanachSpace.mapOfLE h (f j x) = f i x)
    (x : F) (i : ι) : (p.projectiveLimitLift f hf x).val i = f i x := rfl

/-- Continuous linear maps into the projective limit are determined by their coordinates. -/
theorem projectiveLimit_ext {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {f g : F →L[𝕜] p.projectiveLimit} (h : ∀ x i, (f x).val i = (g x).val i) : f = g := by
  apply ContinuousLinearMap.ext
  intro x
  exact Subtype.ext (funext (h x))

/-- The canonical map from the original space to its projective limit. -/
def toProjectiveLimit : E →ₗ[𝕜] p.projectiveLimit :=
  p.toLocalBanachSpaceProduct.codRestrict _ fun x _i _j h ↦
    Seminorm.LocalBanachSpace.mapOfLE_toLocalBanachSpace h x

/-- Evaluation of the canonical projective-limit map. -/
@[simp] theorem toProjectiveLimit_apply (x : E) (i : ι) :
    (p.toProjectiveLimit x).val i = (p i).toLocalBanachSpace x := rfl

/-- A compatible family is approximated simultaneously in finitely many coordinates.
This is the density step of the classical projective completion construction. -/
theorem closure_range_toLocalBanachSpaceProduct [Nonempty ι] (hp : Directed (· ≤ ·) p) :
    closure (range p.toLocalBanachSpaceProduct) = p.projectiveLimit := by
  apply Subset.antisymm
  · apply closure_minimal _ p.isClosed_projectiveLimit
    rintro _ ⟨x, rfl⟩
    exact (p.toProjectiveLimit x).property
  · intro z hz
    classical
    apply mem_closure_iff.mpr
    intro U hU hzU
    obtain ⟨s, V, hV, hVU⟩ := isOpen_pi_iff.mp hU z hzU
    obtain ⟨k, hk⟩ := hp.finset_le s
    let W : Set (p k).LocalBanachSpace := {w | ∀ i : s,
      Seminorm.LocalBanachSpace.mapOfLE (hk i i.property) w ∈ V i}
    have hW : IsOpen W := by
      change IsOpen {w | ∀ i : s, Seminorm.LocalBanachSpace.mapOfLE (hk i i.property) w ∈ V i}
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i ↦
        (hV i i.property).1.preimage
          (Seminorm.LocalBanachSpace.mapOfLE (hk i i.property)).continuous
    have hzW : z k ∈ W := fun i ↦ by
      rw [hz i k (hk i i.property)]
      exact (hV i i.property).2
    obtain ⟨x, hx⟩ := (p k).denseRange_toLocalBanachSpace.exists_mem_open hW ⟨z k, hzW⟩
    refine ⟨p.toLocalBanachSpaceProduct x, hVU ?_, ⟨x, rfl⟩⟩
    intro i hi
    change (p i).toLocalBanachSpace x ∈ V i
    simpa only [Seminorm.LocalBanachSpace.mapOfLE_toLocalBanachSpace] using hx ⟨i, hi⟩

/-- The original space is dense in the projective limit for a directed defining family. -/
theorem denseRange_toProjectiveLimit [Nonempty ι] (hp : Directed (· ≤ ·) p) :
    DenseRange p.toProjectiveLimit := by
  intro z
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  change z.val ∈ closure (Subtype.val '' range p.toProjectiveLimit)
  have him : Subtype.val '' range p.toProjectiveLimit = range p.toLocalBanachSpaceProduct := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨p.toProjectiveLimit x, ⟨x, rfl⟩, rfl⟩
  rw [him, p.closure_range_toLocalBanachSpaceProduct hp]
  exact z.property

variable [UniformSpace E] [IsUniformAddGroup E]

/-- The diagonal map recovers exactly the uniformity of a defining seminorm family. -/
theorem isUniformInducing_toLocalBanachSpaceProduct (hp : WithSeminorms p) :
    IsUniformInducing p.toLocalBanachSpaceProduct := by
  rw [isUniformInducing_iff_uniformSpace, Pi.uniformSpace_eq, UniformSpace.comap_iInf]
  rw [p.withSeminorms_iff_uniformSpace_eq_iInf.mp hp]
  congr 1
  funext i
  rw [← UniformSpace.comap_comap]
  exact (UniformSpace.Completion.isUniformInducing_coe (p i).LocalSpace).comap_uniformSpace

/-- The map into the projective limit recovers the original uniformity. -/
theorem isUniformInducing_toProjectiveLimit (hp : WithSeminorms p) :
    IsUniformInducing p.toProjectiveLimit :=
  (isUniformEmbedding_subtype_val.isUniformInducing.of_comp_iff).mp
    (p.isUniformInducing_toLocalBanachSpaceProduct hp)

/-- A Hausdorff space embeds uniformly in the product of its local Banach spaces. -/
theorem isUniformEmbedding_toLocalBanachSpaceProduct [T2Space E] (hp : WithSeminorms p) :
    IsUniformEmbedding p.toLocalBanachSpaceProduct :=
  ⟨p.isUniformInducing_toLocalBanachSpaceProduct hp,
    (p.isUniformInducing_toLocalBanachSpaceProduct hp).injective⟩

/-- The projective limit is a completion of the space defined by the seminorm family. -/
def projectiveCompletion [Nonempty ι] (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) :
    AbstractCompletion E where
  space := p.projectiveLimit
  coe := p.toProjectiveLimit
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := p.isUniformInducing_toProjectiveLimit hp
  dense := p.denseRange_toProjectiveLimit hd

/-- The separated completion is uniformly isomorphic to the projective limit.
This is the projective completion theorem of Casselman, §5. -/
def completionUniformEquiv [Nonempty ι] (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) :
    UniformSpace.Completion E ≃ᵤ p.projectiveLimit :=
  UniformSpace.Completion.cPkg.compareEquiv (p.projectiveCompletion hp hd)

/-- The completion comparison extends the canonical diagonal map. -/
@[simp] theorem completionUniformEquiv_coe [Nonempty ι]
    (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) (x : E) :
    p.completionUniformEquiv hp hd (x : UniformSpace.Completion E) = p.toProjectiveLimit x :=
  UniformSpace.Completion.cPkg.compare_coe (p.projectiveCompletion hp hd) x

variable [UniformContinuousConstSMul 𝕜 E]

/-- A complete Hausdorff space is itself the projective limit of its local Banach spaces. -/
def equivProjectiveLimit [Nonempty ι] [CompleteSpace E] [T2Space E]
    (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) : E ≃L[𝕜] p.projectiveLimit := by
  let e : E ≃ᵤ p.projectiveLimit := (AbstractCompletion.ofComplete (α := E)).compareEquiv
    (p.projectiveCompletion hp hd)
  have he (x : E) : e x = p.toProjectiveLimit x :=
    (AbstractCompletion.ofComplete (α := E)).compare_coe (p.projectiveCompletion hp hd) x
  exact
    { toLinearEquiv :=
        { p.toProjectiveLimit with
          invFun := e.symm
          left_inv := fun x ↦ by
            change e.symm (p.toProjectiveLimit x) = x
            rw [← he]; exact e.symm_apply_apply x
          right_inv := fun x ↦ by
            change p.toProjectiveLimit (e.symm x) = x
            rw [← he]; exact e.apply_symm_apply x }
      continuous_toFun := (p.isUniformInducing_toProjectiveLimit hp).uniformContinuous.continuous
      continuous_invFun := e.symm.continuous }

/-- The continuous linear extension of the diagonal map to the completion. -/
def completionMap (hp : WithSeminorms p) :
    UniformSpace.Completion E →L[𝕜] p.projectiveLimit :=
  (⟨p.toProjectiveLimit, (p.isUniformInducing_toProjectiveLimit hp).uniformContinuous.continuous⟩ :
    E →L[𝕜] p.projectiveLimit).extend (UniformSpace.Completion.coeCLM 𝕜 E)

/-- The linear extension agrees with the diagonal map on the original space. -/
@[simp] theorem completionMap_coe (hp : WithSeminorms p) (x : E) :
    p.completionMap hp (x : UniformSpace.Completion E) = p.toProjectiveLimit x :=
  ContinuousLinearMap.extend_eq _ (UniformSpace.Completion.denseRange_coeCLM 𝕜 E)
    (UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 E) x

/-- The uniform completion comparison is the continuous linear extension. -/
theorem completionMap_eq_uniformEquiv [Nonempty ι]
    (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) :
    ⇑(p.completionMap hp) = p.completionUniformEquiv hp hd := by
  apply UniformSpace.Completion.ext (p.completionMap hp).continuous
    (p.completionUniformEquiv hp hd).continuous
  intro x
  simp

/-- The projective representation of the completion as a continuous linear equivalence. -/
def completionEquiv [Nonempty ι] (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) :
    UniformSpace.Completion E ≃L[𝕜] p.projectiveLimit where
  toLinearEquiv :=
    { (p.completionMap hp).toLinearMap with
      invFun := (p.completionUniformEquiv hp hd).symm
      left_inv := by
        intro x
        change (p.completionUniformEquiv hp hd).symm (p.completionMap hp x) = x
        rw [p.completionMap_eq_uniformEquiv hp hd]; simp
      right_inv := by
        intro x
        change p.completionMap hp _ = x
        rw [p.completionMap_eq_uniformEquiv hp hd]; simp }
  continuous_toFun := (p.completionMap hp).continuous
  continuous_invFun := (p.completionUniformEquiv hp hd).symm.continuous

/-- The continuous linear representation extends the original diagonal map. -/
@[simp] theorem completionEquiv_coe [Nonempty ι]
    (hp : WithSeminorms p) (hd : Directed (· ≤ ·) p) (x : E) :
    p.completionEquiv hp hd (x : UniformSpace.Completion E) = p.toProjectiveLimit x :=
  p.completionMap_coe hp x

end SeminormFamily

namespace PolynormableSpace

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace 𝕜 E]

variable [UniformContinuousConstSMul 𝕜 E]

/-- All continuous seminorms give a canonical projective representation of the completion. -/
def completionEquiv : UniformSpace.Completion E ≃L[𝕜]
    SeminormFamily.projectiveLimit (fun p : {p : Seminorm 𝕜 E // Continuous p} ↦ p.1) := by
  letI : Nonempty {p : Seminorm 𝕜 E // Continuous p} := ⟨⟨0, continuous_const⟩⟩
  exact SeminormFamily.completionEquiv _ (withSeminorms 𝕜 E) fun p q ↦
    ⟨⟨p.1 ⊔ q.1, p.2.max q.2⟩, le_sup_left, le_sup_right⟩

/-- The completion of a first-countable polynormable space is a countable projective limit
of local Banach spaces. In particular this applies to Fréchet spaces. -/
theorem exists_countable_completionEquiv [FirstCountableTopology E] :
    ∃ p : SeminormFamily 𝕜 E ℕ, WithSeminorms p ∧ Monotone p ∧
      Nonempty (UniformSpace.Completion E ≃L[𝕜] p.projectiveLimit) := by
  obtain ⟨p, hp, hm⟩ := exists_monotone_withSeminorms 𝕜 E
  exact ⟨p, hp, hm, ⟨p.completionEquiv hp fun i j ↦
    ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩⟩⟩

omit [UniformContinuousConstSMul 𝕜 E] in
/-- A complete Hausdorff first-countable polynormable space is a countable projective limit
of local Banach spaces; this is the projective representation of a Fréchet space. -/
theorem exists_countable_equivProjectiveLimit [FirstCountableTopology E] [CompleteSpace E]
    [T2Space E] : ∃ p : SeminormFamily 𝕜 E ℕ, WithSeminorms p ∧ Monotone p ∧
      Nonempty (E ≃L[𝕜] p.projectiveLimit) := by
  obtain ⟨p, hp, hm⟩ := exists_monotone_withSeminorms 𝕜 E
  exact ⟨p, hp, hm, ⟨p.equivProjectiveLimit hp fun i j ↦
    ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩⟩⟩

end PolynormableSpace
