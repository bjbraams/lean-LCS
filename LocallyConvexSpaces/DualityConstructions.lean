/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Transpose
public import LocallyConvexSpaces.Completion
public import LocallyConvexSpaces.PolarTopology

/-!
# Topological duality for quotients, subspaces, and completions

Transposition of a surjective continuous linear map is an embedding of weak-* duals. For the
strong topologies, a sufficient condition is that every bounded target set is contained in the
closure of the image of a bounded source set. This condition yields the strong-dual
identification for quotients and for completions. Complemented subspaces admit continuous
extension operators on their duals.

The statements refine the algebraic identifications in `LocallyConvexSpaces.Transpose` and
`TopologicalVectorSpaces.Completion`. An algebraic identification of duals alone does not assert
a weak-* or strong homeomorphism.

## Main definitions

* `ContinuousLinearMap.weakTranspose`: the transpose between weak-* duals.
* `Submodule.weakAnnihilator`: the annihilator of a subspace, inside the weak-* dual.
* `Submodule.weakDualQuotientEquiv`: the weak-* dual of `E ⧸ M` is the annihilator of `M`.
* `Submodule.strongDualQuotientEquivL`: the same for strong duals, under bounded lifting.
* `Submodule.strongDualSubmoduleEquivL`, `Submodule.weakDualSubmoduleEquiv`: the strong and
  weak-* duals of a complemented subspace `M` are quotients of the dual of `E`.
* `UniformSpace.Completion.strongDualEquivL`: the strong duals of a space and of its completion
  agree under bounded lifting.

## Main statements

* `ContinuousLinearMap.isEmbedding_weakTranspose`: the weak-* transpose of a surjection is a
  topological embedding.
* `ContinuousLinearMap.isInducing_transpose_of_bounded_lifting`,
  `ContinuousLinearMap.isInducing_transpose_of_rightInverse`: sufficient conditions for the
  strong transpose to be inducing.
* `UniformSpace.Completion.continuous_strongDualEquiv_weakDual`: restriction from the
  completion is weak-* continuous.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §1, IV §2
-/

@[expose] public noncomputable section

open Set Function Filter Bornology
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Transposition with the weak-* topologies on both duals. -/
def weakTranspose (f : E →L[𝕜] F) : WeakDual 𝕜 F →L[𝕜] WeakDual 𝕜 E where
  toLinearMap := StrongDual.toWeakDual.toLinearMap.comp
    (f.transpose.toLinearMap.comp WeakDual.toStrongDual.toLinearMap)
  cont := f.continuous_transpose_weakDual

/-- Evaluation of a weak-* transpose. -/
@[simp] theorem weakTranspose_apply (f : E →L[𝕜] F) (φ : WeakDual 𝕜 F) (x : E) :
    f.weakTranspose φ x = φ (f x) := rfl

/-- A surjective map induces the weak-* topology on the dual of its target. -/
theorem isInducing_weakTranspose (f : E →L[𝕜] F) (hf : Surjective f) :
    Topology.IsInducing f.weakTranspose := by
  let g : WeakDual 𝕜 E → (F → 𝕜) := fun φ y ↦ φ (Classical.choose (hf y))
  have hg : Continuous g := continuous_pi fun y ↦ WeakDual.eval_continuous _
  have heq : g ∘ f.weakTranspose = fun φ : WeakDual 𝕜 F ↦ (φ : F → 𝕜) := by
    funext φ y
    exact congrArg φ (Classical.choose_spec (hf y))
  apply Topology.IsInducing.of_comp f.weakTranspose.continuous hg
  rw [heq]
  exact ⟨rfl⟩

/-- The weak-* transpose of a surjection is a topological embedding. -/
theorem isEmbedding_weakTranspose (f : E →L[𝕜] F) (hf : Surjective f) :
    Topology.IsEmbedding f.weakTranspose :=
  ⟨f.isInducing_weakTranspose hf, (f.isInducing_weakTranspose hf).injective⟩

variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/-- If bounded target sets lift up to closure to bounded source sets, transposition induces
the strong dual topology. No surjectivity is needed for this topology statement. -/
theorem isInducing_transpose_of_bounded_lifting (f : E →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (f '' B)) :
    Topology.IsInducing f.transpose := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · have hc := (f.transpose.continuous.tendsto (0 : StrongDual 𝕜 F)).le_comap
    simpa only [map_zero] using hc
  · apply (StrongDual.hasBasis_nhds_zero_polar (𝕜 := 𝕜) (E := F)).ge_iff.mpr
    intro S hS
    obtain ⟨B, hB, hSB⟩ := h S hS
    apply Filter.mem_of_superset (preimage_mem_comap
      ((StrongDual.hasBasis_nhds_zero_polar (𝕜 := 𝕜) (E := E)).mem_of_mem hB))
    intro φ hφ y hy
    have hclosed : IsClosed {z : F | ‖φ z‖ ≤ 1} := isClosed_le φ.continuous.norm continuous_const
    apply closure_minimal ?_ hclosed (hSB hy)
    rintro _ ⟨x, hx, rfl⟩
    exact hφ x hx


/-- A continuous linear right inverse supplies bounded lifts, hence its transpose induces
the strong dual topology. -/
theorem isInducing_transpose_of_rightInverse (f : E →L[𝕜] F) (s : F →L[𝕜] E)
    (h : RightInverse s f) : Topology.IsInducing f.transpose := by
  apply f.isInducing_transpose_of_bounded_lifting
  intro S hS
  refine ⟨s '' S, hS.image s, ?_⟩
  intro y hy
  apply subset_closure
  exact ⟨s y, ⟨y, hy, rfl⟩, h y⟩

end ContinuousLinearMap

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] (M : Submodule 𝕜 E)

/-- The annihilator of a subspace, with the topology inherited from the weak-* dual. -/
def weakAnnihilator : Submodule 𝕜 (WeakDual 𝕜 E) :=
  (StrongDual.polarSubmodule 𝕜 M).comap WeakDual.toStrongDual.toLinearMap

/-- The weak-* dual of a quotient is its annihilator with the induced weak-* topology. -/
def weakDualQuotientEquiv : WeakDual 𝕜 (E ⧸ M) ≃L[𝕜] M.weakAnnihilator := by
  let f : WeakDual 𝕜 (E ⧸ M) →ₗ[𝕜] M.weakAnnihilator :=
    M.mkQL.weakTranspose.toLinearMap.codRestrict _ fun φ ↦ by
      change WeakDual.toStrongDual (M.mkQL.weakTranspose φ) ∈ StrongDual.polarSubmodule 𝕜 M
      rw [StrongDual.mem_polarSubmodule]
      intro x hx
      change φ (Submodule.Quotient.mk x) = 0
      rw [Submodule.Quotient.mk_eq_zero M |>.mpr hx, map_zero]
  have hi : Topology.IsInducing f := Topology.IsInducing.subtypeVal.of_comp_iff.mp
    (M.mkQL.isInducing_weakTranspose M.mkQ_surjective)
  have hs : Surjective f := by
    intro φ
    refine ⟨StrongDual.toWeakDual
      (M.strongDualQuotientEquiv.symm ⟨WeakDual.toStrongDual φ.val, φ.property⟩), ?_⟩
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    exact congrArg Subtype.val (M.strongDualQuotientEquiv.apply_symm_apply
      ⟨WeakDual.toStrongDual φ.val, φ.property⟩)
  let e := LinearEquiv.ofBijective f ⟨hi.injective, hs⟩
  let t := e.toEquiv.toHomeomorphOfIsInducing hi
  exact { e with continuous_toFun := t.continuous, continuous_invFun := t.symm.continuous }

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- Evaluation of the weak-* quotient-dual identification. -/
@[simp] theorem weakDualQuotientEquiv_apply (φ : WeakDual 𝕜 (E ⧸ M)) (x : E) :
    (M.weakDualQuotientEquiv φ).val x = φ (M.mkQ x) := rfl

/-- Bounded lifting up to closure makes the quotient-dual identification a strong
topological isomorphism onto the annihilator. -/
def strongDualQuotientEquivL
    (h : ∀ S : Set (E ⧸ M), IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (M.mkQ '' B)) :
    StrongDual 𝕜 (E ⧸ M) ≃L[𝕜] StrongDual.polarSubmodule 𝕜 M := by
  have hi : Topology.IsInducing M.strongDualQuotientEquiv :=
    Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (M.mkQL.isInducing_transpose_of_bounded_lifting h)
  let e := M.strongDualQuotientEquiv.toEquiv.toHomeomorphOfIsInducing hi
  exact { M.strongDualQuotientEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }


/-- A continuous projection onto a subspace gives the strong dual of that subspace the
quotient topology from the ambient strong dual. -/
def strongDualSubmoduleEquivL (P : E →L[𝕜] M) (hP : ∀ x : M, P x = x) :
    (StrongDual 𝕜 E ⧸ StrongDual.polarSubmodule 𝕜 M) ≃L[𝕜] StrongDual 𝕜 M := by
  let N := StrongDual.polarSubmodule 𝕜 M
  have hk : N ≤ M.subtypeL.transpose.ker := by
    intro φ hφ
    rw [StrongDual.mem_polarSubmodule] at hφ
    ext x
    exact hφ x x.property
  let r := N.liftQL M.subtypeL.transpose hk
  let s := N.mkQL.comp P.transpose
  exact ContinuousLinearEquiv.equivOfInverse r s (fun q ↦ by
    refine Quotient.inductionOn' q fun φ ↦ ?_
    change N.mkQ (P.transpose (M.subtypeL.transpose φ)) = N.mkQ φ
    apply (Submodule.Quotient.eq N).mpr
    rw [StrongDual.mem_polarSubmodule]
    intro x hx
    change φ (P x) - φ x = 0
    rw [hP ⟨x, hx⟩]
    exact sub_self _) (fun φ ↦ by
      ext x
      change φ (P x) = φ x
      rw [hP])

/-- A continuous projection onto a subspace also identifies its weak-* dual with the
quotient of the ambient weak-* dual by the annihilator. -/
def weakDualSubmoduleEquiv (P : E →L[𝕜] M) (hP : ∀ x : M, P x = x) :
    (WeakDual 𝕜 E ⧸ M.weakAnnihilator) ≃L[𝕜] WeakDual 𝕜 M := by
  let N := M.weakAnnihilator
  have hk : N ≤ M.subtypeL.weakTranspose.ker := by
    intro φ hφ
    change WeakDual.toStrongDual φ ∈ StrongDual.polarSubmodule 𝕜 M at hφ
    rw [StrongDual.mem_polarSubmodule] at hφ
    apply WeakDual.toStrongDual.injective
    ext x
    exact hφ x x.property
  let r := N.liftQL M.subtypeL.weakTranspose hk
  let s := N.mkQL.comp P.weakTranspose
  exact ContinuousLinearEquiv.equivOfInverse r s (fun q ↦ by
    refine Quotient.inductionOn' q fun φ ↦ ?_
    change N.mkQ (P.weakTranspose (M.subtypeL.weakTranspose φ)) = N.mkQ φ
    apply (Submodule.Quotient.eq N).mpr
    change WeakDual.toStrongDual (P.weakTranspose (M.subtypeL.weakTranspose φ) - φ) ∈
      StrongDual.polarSubmodule 𝕜 M
    rw [StrongDual.mem_polarSubmodule]
    intro x hx
    change φ (P x) - φ x = 0
    rw [hP ⟨x, hx⟩]
    exact sub_self _) (fun φ ↦ by
      apply WeakDual.toStrongDual.injective
      ext x
      change φ (P x) = φ x
      rw [hP])

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The strong subspace-dual identification sends a class to restriction. -/
@[simp] theorem strongDualSubmoduleEquivL_mk (P : E →L[𝕜] M) (hP : ∀ x : M, P x = x)
    (φ : StrongDual 𝕜 E) (x : M) :
    M.strongDualSubmoduleEquivL P hP (Submodule.Quotient.mk φ) x = φ x := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The inverse strong identification is the class of the extension along the projection. -/
@[simp] theorem strongDualSubmoduleEquivL_symm_apply (P : E →L[𝕜] M)
    (hP : ∀ x : M, P x = x) (φ : StrongDual 𝕜 M) :
    (M.strongDualSubmoduleEquivL P hP).symm φ =
      (StrongDual.polarSubmodule 𝕜 M).mkQ (P.transpose φ) := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The weak-* subspace-dual identification sends a class to restriction. -/
@[simp] theorem weakDualSubmoduleEquiv_mk (P : E →L[𝕜] M) (hP : ∀ x : M, P x = x)
    (φ : WeakDual 𝕜 E) (x : M) :
    M.weakDualSubmoduleEquiv P hP (Submodule.Quotient.mk φ) x = φ x := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- The inverse weak-* identification is the class of the extension along the projection. -/
@[simp] theorem weakDualSubmoduleEquiv_symm_apply (P : E →L[𝕜] M)
    (hP : ∀ x : M, P x = x) (φ : WeakDual 𝕜 M) :
    (M.weakDualSubmoduleEquiv P hP).symm φ = M.weakAnnihilator.mkQ (P.weakTranspose φ) := rfl

end Submodule

namespace UniformSpace.Completion

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [UniformContinuousConstSMul 𝕜 E] [ContinuousSMul 𝕜 E]

omit [ContinuousSMul 𝕜 E] in
/-- Restriction from the completion is weak-* continuous. The inverse need not be. -/
theorem continuous_strongDualEquiv_weakDual : Continuous fun φ : WeakDual 𝕜 (Completion E) ↦
    StrongDual.toWeakDual (strongDualEquiv 𝕜 E (WeakDual.toStrongDual φ)) :=
  (coeCLM 𝕜 E).continuous_transpose_weakDual

/-- Restriction identifies the strong duals when every bounded completion set is contained
in the closure of the image of a bounded original set. -/
def strongDualEquivL
    (h : ∀ S : Set (Completion E), IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (coeCLM 𝕜 E '' B)) :
    StrongDual 𝕜 (Completion E) ≃L[𝕜] StrongDual 𝕜 E := by
  have hi : Topology.IsInducing (strongDualEquiv 𝕜 E) :=
    (coeCLM 𝕜 E).isInducing_transpose_of_bounded_lifting h
  let e := (strongDualEquiv 𝕜 E).toEquiv.toHomeomorphOfIsInducing hi
  exact { strongDualEquiv 𝕜 E with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

end UniformSpace.Completion
