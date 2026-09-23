/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.QuasiBarrelled
public import LocallyConvexSpaces.Transpose
public import LocallyConvexSpaces.Quotient
public import LocallyConvexSpaces.MontelPermanence
public import LocallyConvexSpaces.StrongDualProduct
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Permanence of semi-reflexivity and reflexivity

Semi-reflexivity passes to closed locally convex subspaces, to continuous linear retracts and to
arbitrary products. Reflexivity passes to continuous linear retracts, over a nontrivially normed
field and without local convexity, and to arbitrary products of locally convex spaces. Images
and quotients require a bounded-lifting hypothesis. The subspace and bounded-lifting
reflexivity results additionally require quasi-barrelledness of the resulting space: closed
subspaces of reflexive locally convex spaces need not be reflexive, and quotients need not be
semi-reflexive.

## Main statements

* `SemiReflexiveSpace.of_rightInverse`, `ReflexiveSpace.of_rightInverse`,
  `BarrelledSpace.of_rightInverse`: continuous linear retracts.
* `SemiReflexiveSpace.submodule`, `ReflexiveSpace.submodule_of_quasiBarrelledSpace`: closed
  subspaces.
* `SemiReflexiveSpace.of_bounded_lifting`, `ReflexiveSpace.of_bounded_lifting`,
  `ReflexiveSpace.quotient_of_bounded_lifting`: images that lift bounded sets up to closure.
* `SemiReflexiveSpace.pi`, `ReflexiveSpace.pi`: arbitrary products.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.7, §5.8
-/

public section

open Set Function Bornology

section Retracts

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- Continuous linear retracts of semi-reflexive spaces are semi-reflexive. -/
theorem SemiReflexiveSpace.of_rightInverse [SemiReflexiveSpace 𝕜 E]
    (f : E →L[𝕜] F) (s : F →L[𝕜] E) (h : RightInverse s f) : SemiReflexiveSpace 𝕜 F := by
  constructor
  intro ψ
  obtain ⟨x, hx⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual
    (𝕜 := 𝕜) (E := E) (ψ.comp s.transpose)
  refine ⟨f x, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  have he : s.transpose (f.transpose φ) = φ := by ext y; exact congrArg φ (h y)
  have hh := congrArg (fun u : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ u (f.transpose φ)) hx
  change φ (f x) = ψ (s.transpose (f.transpose φ)) at hh
  rwa [he] at hh

/-- Continuous linear equivalences preserve semi-reflexivity. -/
theorem SemiReflexiveSpace.of_continuousLinearEquiv [SemiReflexiveSpace 𝕜 E]
    (e : E ≃L[𝕜] F) : SemiReflexiveSpace 𝕜 F :=
  of_rightInverse e.toContinuousLinearMap e.symm.toContinuousLinearMap e.apply_symm_apply

/-- Continuous linear retracts of reflexive spaces are reflexive over a nontrivially normed
field, without local convexity or separation assumptions. -/
theorem ReflexiveSpace.of_rightInverse [ReflexiveSpace 𝕜 E]
    (f : E →L[𝕜] F) (s : F →L[𝕜] E) (h : RightInverse s f) : ReflexiveSpace 𝕜 F := by
  have hJE : Topology.IsInducing (StrongDual.inclusionInDoubleDual 𝕜 E) :=
    ReflexiveSpace.isInducing_inclusionInDoubleDual
  have hcont : Continuous (StrongDual.inclusionInDoubleDual 𝕜 F) := by
    have hh := f.transpose.transpose.continuous.comp (hJE.continuous.comp s.continuous)
    convert hh using 1
    funext y
    apply ContinuousLinearMap.ext
    intro φ
    change φ y = φ (f (s y))
    rw [h y]
  refine { SemiReflexiveSpace.of_rightInverse f s h with
    isInducing_inclusionInDoubleDual := ?_ }
  apply Topology.IsInducing.of_comp hcont s.transpose.transpose.continuous
  convert hJE.comp (h.isEmbedding f.continuous s.continuous).isInducing using 1
  funext y
  apply ContinuousLinearMap.ext
  intro φ
  rfl

/-- Continuous linear equivalences preserve reflexivity. -/
theorem ReflexiveSpace.of_continuousLinearEquiv [ReflexiveSpace 𝕜 E]
    (e : E ≃L[𝕜] F) : ReflexiveSpace 𝕜 F :=
  of_rightInverse e.toContinuousLinearMap e.symm.toContinuousLinearMap e.apply_symm_apply

end Retracts

section BarrelledRetracts

variable {𝕜 E F : Type*} [SeminormedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Barrelledness passes to continuous linear retracts. -/
theorem BarrelledSpace.of_rightInverse [BarrelledSpace 𝕜 E]
    (f : E →L[𝕜] F) (s : F →L[𝕜] E) (h : RightInverse s f) : BarrelledSpace 𝕜 F := by
  constructor
  intro p hp
  have hc : Continuous (p.comp f.toLinearMap) :=
    (p.comp f.toLinearMap).continuous_of_lowerSemicontinuous (hp.comp f.continuous)
  convert hc.comp s.continuous using 1
  ext y
  exact congrArg p (h y).symm

end BarrelledRetracts

section Subspaces

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- Closed subspaces of semi-reflexive locally convex spaces are semi-reflexive.
This is the permanence assertion after Schaefer–Wolff IV, Theorem 5.7, proved
using extension of functionals and separation by the annihilator. -/
theorem SemiReflexiveSpace.submodule [SemiReflexiveSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) : SemiReflexiveSpace 𝕜 M := by
  constructor
  intro ψ
  obtain ⟨x, hx⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual
    (𝕜 := 𝕜) (E := E) (ψ.comp M.subtypeL.transpose)
  have hxm : x ∈ M := by
    change x ∈ (M : Set E)
    rw [← hM.closure_eq, Submodule.mem_closure_iff_forall_strongDual]
    intro φ hφ
    have hz : M.subtypeL.transpose φ = 0 := by
      ext y
      exact (StrongDual.mem_polarSubmodule 𝕜 M φ).mp hφ y y.property
    have hh := congrArg (fun u : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ u φ) hx
    change φ x = ψ (M.subtypeL.transpose φ) at hh
    simpa [hz] using hh
  refine ⟨⟨x, hxm⟩, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  obtain ⟨χ, rfl⟩ := M.surjective_transpose_subtypeL φ
  exact congrArg (fun u : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ u χ) hx

/-- A closed subspace of a semi-reflexive space is reflexive if it is quasi-barrelled. -/
theorem ReflexiveSpace.submodule_of_quasiBarrelledSpace [SemiReflexiveSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) [QuasiBarrelledSpace 𝕜 M] :
    ReflexiveSpace 𝕜 M := by
  let : LocallyConvexSpace ℝ M := inferInstanceAs (LocallyConvexSpace ℝ (M.restrictScalars ℝ))
  exact reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace.mpr
    ⟨SemiReflexiveSpace.submodule M hM, inferInstance⟩

end Subspaces

section Images

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F]

/-- A bounded-lifting image of a Hausdorff semi-reflexive locally convex space is semi-reflexive.
Bounded sets need only lift up to closure. -/
theorem SemiReflexiveSpace.of_bounded_lifting [T1Space E] [T1Space F]
    [SemiReflexiveSpace 𝕜 E] (f : E →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (f '' B)) : SemiReflexiveSpace 𝕜 F := by
  let : SeparatingDual 𝕜 F := SeparatingDual.of_locallyConvexSpace_real 𝕜 F
  apply SemiReflexiveSpace.of_forall_isVonNBounded 𝕜 F
  intro S hS
  obtain ⟨B, hB, hSB⟩ := h S hS
  obtain ⟨K, hK, hBK⟩ := SemiReflexiveSpace.exists_mem_mackeyFamily_subset 𝕜 E hB
  let g := WeakSpace.map f
  have hgK : IsCompact (g '' K) := hK.1.image g.continuous
  refine ⟨g '' K, ⟨hgK, hK.2.1.linear_image (g.toLinearMap.restrictScalars ℝ),
    hK.2.2.image g.toLinearMap⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hclosed : IsClosed (toWeakSpace 𝕜 F ⁻¹' (g '' K)) :=
    hgK.isClosed.preimage (toWeakSpaceCLM 𝕜 F).continuous
  apply closure_minimal ?_ hclosed (hSB hy)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨toWeakSpace 𝕜 E x, hBK ⟨x, hx, rfl⟩, rfl⟩

/-- A quasi-barrelled bounded-lifting image of a semi-reflexive space is reflexive. -/
theorem ReflexiveSpace.of_bounded_lifting [T1Space E] [T1Space F]
    [SemiReflexiveSpace 𝕜 E] [QuasiBarrelledSpace 𝕜 F] (f : E →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (f '' B)) : ReflexiveSpace 𝕜 F :=
  reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace.mpr
    ⟨SemiReflexiveSpace.of_bounded_lifting f h, inferInstance⟩

/-- A Hausdorff bounded-lifting quotient of a reflexive space is reflexive. -/
theorem ReflexiveSpace.quotient_of_bounded_lifting [T1Space E] [ReflexiveSpace 𝕜 E]
    (M : Submodule 𝕜 E) [T1Space (E ⧸ M)]
    (h : ∀ S : Set (E ⧸ M), IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (M.mkQ '' B)) :
    ReflexiveSpace 𝕜 (E ⧸ M) := by
  let : BarrelledSpace 𝕜 E :=
    (reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace.mp inferInstance).2
  exact ReflexiveSpace.of_bounded_lifting M.mkQL h

end Images

section Products

variable {𝕜 ι : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]

/-- Arbitrary products of semi-reflexive spaces are semi-reflexive. This is the product assertion of
Schaefer–Wolff IV, Theorem 5.8. -/
instance SemiReflexiveSpace.pi [∀ i, SemiReflexiveSpace 𝕜 (E i)] :
    SemiReflexiveSpace 𝕜 (∀ i, E i) := by
  classical
  constructor
  intro ψ
  let e (i : ι) : (∀ i, E i) →L[𝕜] E i := ContinuousLinearMap.proj i
  choose x hx using fun i ↦ SemiReflexiveSpace.surjective_inclusionInDoubleDual
    (𝕜 := 𝕜) (E := E i) (ψ.comp (e i).transpose)
  refine ⟨x, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  obtain ⟨s, hs⟩ := StrongDual.exists_finset_apply_eq_sum
    (isVonNBounded_singleton (𝕜 := 𝕜) φ)
  let r (i : ι) := (ContinuousLinearMap.single 𝕜 E i).transpose φ
  have hφ : φ = ∑ i ∈ s, (e i).transpose (r i) := by
    ext y
    simpa [e, r] using hs φ (mem_singleton φ) y
  change φ x = ψ φ
  rw [hs φ (mem_singleton φ) x]
  conv_rhs => rw [hφ, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun u : StrongDual 𝕜 (StrongDual 𝕜 (E i)) ↦ u (r i)) (hx i)

/-- Arbitrary products of reflexive locally convex spaces are reflexive.
This is the reflexive product assertion of Schaefer–Wolff IV, Theorem 5.8. -/
instance ReflexiveSpace.pi [∀ i, Module ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, ReflexiveSpace 𝕜 (E i)] :
    ReflexiveSpace 𝕜 (∀ i, E i) := by
  let (i : ι) : QuasiBarrelledSpace 𝕜 (E i) :=
    (reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace.mp inferInstance).2
  exact reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace.mpr
    ⟨inferInstance, inferInstance⟩

end Products
