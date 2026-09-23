/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Bipolar
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Transposes, annihilators, and the duals of subspaces and quotients

The transpose of a continuous linear map `f : E →L[𝕜] F` is the map `φ ↦ φ ∘ f` between the
duals. Mathlib has it as `ContinuousLinearMap.precomp 𝕜 f`, continuous for the strong topologies
(abbreviated here to `f.transpose : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`), and as
`WeakSpace.map f` it records that `f` is weakly continuous. The annihilator of a subspace `M`
of `E` is `StrongDual.polarSubmodule 𝕜 M`. This file proves the orthogonality relations between
a map and its transpose and identifies the duals of subspaces and quotients of a locally convex
space.

## Main definitions

* `ContinuousLinearMap.transpose`: the transpose `φ ↦ φ ∘ f`, between the strong duals.
* `Submodule.strongDualSubmoduleEquiv`: the dual of a subspace `M` is `E' ⧸ M^⊥`.
* `Submodule.strongDualQuotientEquiv`: the dual of the quotient `E ⧸ M` is `M^⊥`.

## Main statements

* `ContinuousLinearMap.continuous_transpose_weakDual`: the transpose is weak-* continuous.
* `Submodule.mem_closure_iff_forall_strongDual`: a point lies in the closure of a subspace of a
  locally convex space if and only if every continuous functional that vanishes on the subspace
  vanishes at the point.
* `ContinuousLinearMap.ker_transpose`: `ker fᵗ = (range f)^⊥`.
* `ContinuousLinearMap.mem_closure_range_iff`: `closure (range f) = (ker fᵗ)_⊥`.
* `ContinuousLinearMap.denseRange_iff_injective_transpose`: `f` has dense range if and only if
  its transpose is injective.
* `ContinuousLinearMap.mem_ker_iff_forall_transpose`: `ker f = (range fᵗ)_⊥`.
* `ContinuousLinearMap.polar_image`: `(f '' s)° = (fᵗ)⁻¹ (s°)`.
* `Submodule.surjective_transpose_subtypeL`, `Submodule.ker_transpose_subtypeL`: the restriction
  of functionals to a subspace `M` is surjective, by the Hahn–Banach theorem, with kernel `M^⊥`.
* `Submodule.isInducing_weakSpace_map_subtypeL`: the weak topology of a subspace is induced by
  the weak topology of the space.
* `Submodule.injective_transpose_mkQL`, `Submodule.range_transpose_mkQL`: the transpose of the
  quotient map `E → E ⧸ M` is injective with range `M^⊥`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §2, IV §4.1
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §6.3–6.5, IV §1.3
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §20.4, §22.1

## Tags

transpose, adjoint, annihilator, dual of a subspace, dual of a quotient
-/

public section

open Set Function

open scoped Topology

section Defs

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The **transpose** of a continuous linear map `f : E →L[𝕜] F`, as a continuous linear map
between the strong duals. This is an abbreviation for Mathlib's
`ContinuousLinearMap.precomp 𝕜 f`, with the types of the duals fixed. -/
abbrev ContinuousLinearMap.transpose (f : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  ContinuousLinearMap.precomp 𝕜 f

/-- The transpose of `f` sends `φ` to `φ ∘ f`. -/
theorem ContinuousLinearMap.transpose_apply (f : E →L[𝕜] F) (φ : StrongDual 𝕜 F) (x : E) :
    f.transpose φ x = φ (f x) :=
  rfl

/-- The transpose of a continuous linear map is continuous for the weak-* topologies. -/
theorem ContinuousLinearMap.continuous_transpose_weakDual (f : E →L[𝕜] F) :
    Continuous fun φ : WeakDual 𝕜 F ↦
      StrongDual.toWeakDual (f.transpose (WeakDual.toStrongDual φ)) :=
  WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (f x)

end Defs

section Annihilator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A point of a locally convex space lies in the closure of a subspace `M` if and only if every
continuous linear functional that vanishes on `M` vanishes at the point. -/
theorem Submodule.mem_closure_iff_forall_strongDual {M : Submodule 𝕜 E} {x : E} :
    x ∈ closure (M : Set E) ↔ ∀ φ ∈ StrongDual.polarSubmodule 𝕜 M, φ x = 0 := by
  constructor
  · intro hx φ hφ
    -- The kernel of `φ` is a closed set that contains `M`.
    have hcl : IsClosed {y : E | φ y = 0} := isClosed_eq φ.continuous continuous_const
    exact closure_minimal (fun y hy ↦ (StrongDual.mem_polarSubmodule 𝕜 M φ).mp hφ y hy) hcl hx
  · intro h
    by_contra hx
    have hMc : (M.topologicalClosure : Set E) = closure (M : Set E) :=
      M.topologicalClosure_coe
    have hconv : Convex ℝ (M.topologicalClosure : Set E) :=
      (M.topologicalClosure.restrictScalars ℝ).convex
    obtain ⟨φ, hφ, hφx⟩ := StrongDual.exists_mem_polar_one_lt_norm (𝕜 := 𝕜) hconv
      M.topologicalClosure.balanced M.isClosed_topologicalClosure
      ⟨0, M.topologicalClosure.zero_mem⟩ (hMc ▸ hx)
    -- A functional in the polar of a subspace vanishes on it.
    have hφ0 : φ ∈ StrongDual.polarSubmodule 𝕜 M := by
      rw [StrongDual.mem_polarSubmodule]
      intro y hy
      refine LinearMap.eq_zero_of_forall_norm_le_one (Q := M) (φ := φ.toLinearMap)
        (fun z hz ↦ hφ z (M.le_topologicalClosure hz)) hy
    rw [h φ hφ0, norm_zero] at hφx
    exact absurd hφx (by norm_num)

end Annihilator

namespace ContinuousLinearMap

section Algebraic

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  (f : E →L[𝕜] F)

/-- The kernel of the transpose is the annihilator of the range: `ker fᵗ = (range f)^⊥`. -/
theorem ker_transpose :
    LinearMap.ker f.transpose.toLinearMap =
      StrongDual.polarSubmodule 𝕜 (LinearMap.range f.toLinearMap) := by
  ext φ
  rw [LinearMap.mem_ker, StrongDual.mem_polarSubmodule]
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact congrArg (fun ψ : StrongDual 𝕜 E ↦ ψ x) h
  · intro h
    ext x
    exact h (f x) ⟨x, rfl⟩

/-- The polar of an image is the preimage of the polar under the transpose. -/
theorem polar_image (s : Set E) :
    StrongDual.polar 𝕜 (f '' s) = f.transpose ⁻¹' StrongDual.polar 𝕜 s := by
  ext φ
  simp only [StrongDual.mem_polar_iff, mem_preimage, forall_mem_image]
  rfl

end Algebraic

section LocallyConvex

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F] (f : E →L[𝕜] F)

/-- The closure of the range of a continuous linear map into a locally convex space consists of
the points at which all functionals in the kernel of the transpose vanish:
`closure (range f) = (ker fᵗ)_⊥`. -/
theorem mem_closure_range_iff {y : F} :
    y ∈ closure (range f) ↔
      ∀ φ : StrongDual 𝕜 F, f.transpose φ = 0 → φ y = 0 := by
  have h := Submodule.mem_closure_iff_forall_strongDual (𝕜 := 𝕜)
    (M := LinearMap.range f.toLinearMap) (x := y)
  rw [← f.ker_transpose] at h
  exact h

/-- A continuous linear map into a locally convex space has dense range if and only if its
transpose is injective. -/
theorem denseRange_iff_injective_transpose :
    DenseRange f ↔ Injective f.transpose := by
  constructor
  · intro hf
    refine (injective_iff_map_eq_zero _).mpr fun φ hφ ↦ ?_
    ext y
    exact (f.mem_closure_range_iff.mp (hf y)) φ hφ
  · intro hinj y
    refine f.mem_closure_range_iff.mpr fun φ hφ ↦ ?_
    rw [(injective_iff_map_eq_zero _).mp hinj φ hφ]
    rfl

end LocallyConvex

section SeparatingDual

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [SeparatingDual 𝕜 F]

/-- The transpose detects the kernel when the target has a separating continuous dual. -/
theorem mem_ker_iff_forall_transpose_of_separatingDual (f : E →L[𝕜] F) {x : E} :
    f x = 0 ↔ ∀ φ : StrongDual 𝕜 F, f.transpose φ x = 0 :=
  SeparatingDual.eq_zero_iff_forall_dual_eq_zero (R := 𝕜) (f x)

end SeparatingDual

section Kernel

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F] [T1Space F] (f : E →L[𝕜] F)

/-- The kernel of a continuous linear map into a Hausdorff locally convex space consists of the
points at which all functionals in the range of the transpose vanish: `ker f = (range fᵗ)_⊥`. -/
theorem mem_ker_iff_forall_transpose {x : E} :
    f x = 0 ↔ ∀ φ : StrongDual 𝕜 F, f.transpose φ x = 0 := by
  have : SeparatingDual 𝕜 F := SeparatingDual.of_locallyConvexSpace_real 𝕜 F
  exact f.mem_ker_iff_forall_transpose_of_separatingDual

end Kernel

end ContinuousLinearMap

namespace Submodule

section Subspace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] (M : Submodule 𝕜 E)

/-- The restriction of functionals to a subspace of a locally convex space is surjective, by the
Hahn–Banach theorem. -/
theorem surjective_transpose_subtypeL :
    Surjective M.subtypeL.transpose := fun ψ ↦ by
  have := PolynormableSpace.of_locallyConvexSpace_real 𝕜 E
  obtain ⟨φ, hφ⟩ := StrongDual.exists_extension M ψ
  exact ⟨φ, ContinuousLinearMap.ext fun x ↦ hφ x⟩

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] in
/-- The kernel of the restriction of functionals to a subspace is the annihilator of the
subspace. -/
theorem ker_transpose_subtypeL :
    LinearMap.ker M.subtypeL.transpose.toLinearMap =
      StrongDual.polarSubmodule 𝕜 M := by
  rw [ContinuousLinearMap.ker_transpose]
  congr 1
  exact M.range_subtype

/-- **The weak topology of a subspace** of a locally convex space is induced by the weak topology
of the space: `σ(M, M')` is the restriction of `σ(E, E')` to `M`. -/
theorem isInducing_weakSpace_map_subtypeL :
    Topology.IsInducing (WeakSpace.map M.subtypeL) := by
  -- Every functional on `M` is the restriction of a functional on `E`.
  choose ext hext using M.surjective_transpose_subtypeL
  -- The weak topologies are induced by the evaluation maps into products of copies of `𝕜`.
  let evalE : WeakSpace 𝕜 E → StrongDual 𝕜 E → 𝕜 := fun y φ ↦ φ y
  let evalM : WeakSpace 𝕜 M → StrongDual 𝕜 M → 𝕜 := fun x ψ ↦ ψ x
  have hE : Topology.IsInducing evalE := ⟨rfl⟩
  have hM : Topology.IsInducing evalM := ⟨rfl⟩
  let R : (StrongDual 𝕜 E → 𝕜) → StrongDual 𝕜 M → 𝕜 := fun u ψ ↦ u (ext ψ)
  have hR : Continuous R := continuous_pi fun ψ ↦ continuous_apply (ext ψ)
  have hcomp : evalM = R ∘ (evalE ∘ WeakSpace.map M.subtypeL) := by
    funext x ψ
    have h := congrArg (fun χ : StrongDual 𝕜 M ↦ χ x) (hext ψ)
    exact h.symm
  have h1 : Topology.IsInducing (evalE ∘ WeakSpace.map M.subtypeL) :=
    Topology.IsInducing.of_comp (hE.continuous.comp (WeakSpace.map M.subtypeL).continuous) hR
      (hcomp ▸ hM)
  exact (hE.of_comp_iff).mp h1

/-- **The dual of a subspace**: the continuous dual of a subspace `M` of a locally convex space
`E` is linearly equivalent to the quotient of the dual of `E` by the annihilator of `M`. -/
@[expose]
noncomputable def strongDualSubmoduleEquiv :
    (StrongDual 𝕜 E ⧸ StrongDual.polarSubmodule 𝕜 M) ≃ₗ[𝕜] StrongDual 𝕜 M :=
  (Submodule.quotEquivOfEq _ _ M.ker_transpose_subtypeL.symm).trans
    (M.subtypeL.transpose.toLinearMap.quotKerEquivOfSurjective
      M.surjective_transpose_subtypeL)

/-- The identification of the dual of a subspace sends the class of `φ` to its restriction. -/
theorem strongDualSubmoduleEquiv_mk (φ : StrongDual 𝕜 E) (x : M) :
    M.strongDualSubmoduleEquiv (Submodule.Quotient.mk φ) x = φ x :=
  rfl

end Subspace

section Quotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (M : Submodule 𝕜 E)

/-- The transpose of the quotient map is injective. -/
theorem injective_transpose_mkQL : Injective M.mkQL.transpose := by
  refine (injective_iff_map_eq_zero _).mpr fun ψ hψ ↦ ?_
  ext q
  obtain ⟨x, rfl⟩ := M.mkQ_surjective q
  exact congrArg (fun χ : StrongDual 𝕜 E ↦ χ x) hψ

/-- The range of the transpose of the quotient map is the annihilator of the subspace. -/
theorem range_transpose_mkQL :
    LinearMap.range M.mkQL.transpose.toLinearMap =
      StrongDual.polarSubmodule 𝕜 M := by
  ext φ
  rw [StrongDual.mem_polarSubmodule]
  constructor
  · rintro ⟨ψ, rfl⟩ x hx
    have h0 : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hx
    change ψ (M.mkQ x) = 0
    rw [h0, map_zero]
  · intro h
    exact ⟨M.liftQL φ fun x hx ↦ h x hx, ContinuousLinearMap.ext fun x ↦ rfl⟩

/-- **The dual of a quotient**: the continuous dual of `E ⧸ M` is linearly equivalent to the
annihilator of `M`. -/
@[expose]
noncomputable def strongDualQuotientEquiv :
    StrongDual 𝕜 (E ⧸ M) ≃ₗ[𝕜] StrongDual.polarSubmodule 𝕜 M :=
  (LinearEquiv.ofInjective M.mkQL.transpose.toLinearMap
    M.injective_transpose_mkQL).trans (LinearEquiv.ofEq _ _ M.range_transpose_mkQL)

/-- The identification of the dual of a quotient sends `ψ` to `ψ ∘ mkQ`. -/
theorem strongDualQuotientEquiv_apply (ψ : StrongDual 𝕜 (E ⧸ M)) (x : E) :
    (M.strongDualQuotientEquiv ψ : StrongDual 𝕜 E) x = ψ (M.mkQ x) :=
  rfl

end Quotient

end Submodule
