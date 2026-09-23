/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.QuasiBarrelled
public import LocallyConvexSpaces.Completion

/-!
# Completeness properties of strong duals

Zero-neighbourhood polars are complete for the strong dual uniformity. Consequently the
strong dual of a quasi-barrelled space, in particular a barrelled space, is quasi-complete.
The strong dual of a bornological space is complete: a limit for bounded convergence remains
linear and maps bounded sets to bounded sets, hence is continuous. Semi-reflexive locally
convex spaces are quasi-complete: a limit in the completion of a bounded set represents a
continuous bidual element.

## Main statements

* `StrongDual.isComplete_polar_of_mem_nhds`.
* `QuasiBarrelledSpace.quasiCompleteSpace_strongDual`.
* `BornologicalSpace.completeSpace_strongDual`.
* `SemiReflexiveSpace.quasiCompleteSpace`.

## References

These are the dual completeness results in Schaefer–Wolff, *Topological Vector Spaces*, IV §6.1. The
uniform-convergence infrastructure is from Mathlib.
-/

public noncomputable section

open Set Filter Function Bornology
open scoped Topology Uniformity UniformConvergence

section Polars

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- The polar of a zero neighbourhood is complete for the strong dual uniformity. -/
theorem StrongDual.isComplete_polar_of_mem_nhds {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsComplete (StrongDual.polar 𝕜 U) := by
  let S : Set (Set E) := {s | IsVonNBounded 𝕜 s}
  let i : StrongDual 𝕜 E → (E →ᵤ[S] 𝕜) := UniformOnFun.ofFun S ∘ DFunLike.coe
  have hi : IsUniformInducing i := UniformConvergenceCLM.isUniformInducing_coeFn _ _ _
  rw [← isComplete_image_iff hi]
  have heq : i '' StrongDual.polar 𝕜 U = (UniformOnFun.toFun S) ⁻¹'
      (((↑) : WeakDual 𝕜 E → E → 𝕜) '' WeakDual.polar 𝕜 U) := by
    ext g
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨StrongDual.toWeakDual φ, hφ, rfl⟩
    · rintro ⟨φ, hφ, hφg⟩
      exact ⟨WeakDual.toStrongDual φ, hφ, hφg⟩
  rw [heq]
  exact ((WeakDual.isClosed_image_coe_polar hU).preimage
    (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).continuous).isComplete

end Polars

section SpaceClasses

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- The strong dual of a quasi-barrelled space is quasi-complete. In particular this applies
to barrelled spaces. -/
theorem QuasiBarrelledSpace.quasiCompleteSpace_strongDual [QuasiBarrelledSpace 𝕜 E] :
    QuasiCompleteSpace 𝕜 (StrongDual 𝕜 E) := by
  refine ⟨fun {B} hB hBcl ↦ ?_⟩
  obtain ⟨U, hU, hBU⟩ := StrongDual.exists_mem_nhds_subset_polar
    (QuasiBarrelledSpace.equicontinuous_of_isVonNBounded hB)
  intro l hl hlB
  let : l.NeBot := hl.1
  obtain ⟨φ, _, hφ⟩ := StrongDual.isComplete_polar_of_mem_nhds hU l hl
    (hlB.trans (principal_mono.mpr hBU))
  exact ⟨φ, hBcl.mem_of_tendsto hφ (le_principal_iff.mp hlB), hφ⟩

end SpaceClasses

section Bornological

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- The strong dual of a bornological space over a complete nontrivially normed field is
complete, without metrizability or completeness assumptions on the original space. -/
theorem BornologicalSpace.completeSpace_strongDual [BornologicalSpace 𝕜 E] :
    CompleteSpace (StrongDual 𝕜 E) := by
  let S : Set (Set E) := {s | IsVonNBounded 𝕜 s}
  let i : StrongDual 𝕜 E → (E →ᵤ[S] 𝕜) := UniformOnFun.ofFun S ∘ DFunLike.coe
  have hi : IsUniformInducing i := UniformConvergenceCLM.isUniformInducing_coeFn _ _ _
  rw [completeSpace_iff_isComplete_range hi]
  apply IsClosed.isComplete
  apply isClosed_of_closure_subset
  intro g hg
  have hc : Continuous (UniformOnFun.toFun (β := 𝕜) S) :=
    (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).continuous
  have hlin : UniformOnFun.toFun S g ∈ range ((↑) : (E →ₗ[𝕜] 𝕜) → E → 𝕜) := by
    exact (closure_minimal (by rintro _ ⟨φ, rfl⟩; exact ⟨φ.toLinearMap, rfl⟩)
      ((LinearMap.isClosed_range_coe E 𝕜 (RingHom.id 𝕜)).preimage hc)) hg
  obtain ⟨f, hf⟩ := hlin
  have hfc : Continuous f := f.continuous_of_forall_isVonNBounded_image fun B hB ↦ by
    have hN := UniformOnFun.gen_mem_nhds 𝕜 S g hB (Metric.dist_mem_uniformity one_pos)
    obtain ⟨_, hφg, φ, rfl⟩ := mem_closure_iff_nhds.mp hg _ hN
    obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).mp
      (hB.image φ)
    refine (NormedSpace.isVonNBounded_iff' 𝕜).mpr ⟨1 + C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hd : ‖f x - φ x‖ < 1 := by
      rw [← dist_eq_norm, congrFun hf x]
      exact hφg x hx
    exact (norm_le_norm_sub_add (f x) (φ x)).trans
      (add_le_add hd.le (hC _ ⟨x, hx, rfl⟩))
  exact ⟨⟨f, hfc⟩, hf⟩

end Bornological

section SemiReflexive

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A semi-reflexive locally convex space is quasi-complete, including with the non-Hausdorff
convention for semi-reflexivity. This is Schaefer–Wolff, IV §5.5,
Corollary 1: a limit in the completion of a bounded set defines a continuous bidual element. -/
theorem SemiReflexiveSpace.quasiCompleteSpace [SemiReflexiveSpace 𝕜 E] :
    QuasiCompleteSpace 𝕜 E := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let : UniformContinuousConstSMul ℝ E :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ E
  let c := UniformSpace.Completion.coeCLM 𝕜 E
  let e := UniformSpace.Completion.strongDualEquiv 𝕜 E
  have hc : IsUniformInducing c := UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 E
  refine ⟨fun {B} hB hBcl ↦ ?_⟩
  rw [← isComplete_image_iff hc]
  apply IsClosed.isComplete
  apply isClosed_of_closure_subset
  intro z hz
  let f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜 :=
    { toFun := fun φ ↦ e.symm φ z
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hbound (φ : StrongDual 𝕜 E) (hφ : φ ∈ StrongDual.polar 𝕜 B) : ‖f φ‖ ≤ 1 := by
    exact (closure_minimal (by
      rintro _ ⟨x, hx, rfl⟩
      change ‖e.symm φ (x : UniformSpace.Completion E)‖ ≤ 1
      rw [UniformSpace.Completion.strongDualEquiv_symm_apply_coe]
      exact hφ x hx) (isClosed_le (e.symm φ).continuous.norm continuous_const)) hz
  have hb : IsVonNBounded 𝕜 (f '' StrongDual.polar 𝕜 B) :=
    (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 1).subset (by
      rintro _ ⟨φ, hφ, rfl⟩
      exact mem_closedBall_zero_iff.mpr (hbound φ hφ))
  let ψ := f.clmOfExistsBoundedImage
    ⟨StrongDual.polar 𝕜 B, StrongDual.hasBasis_nhds_zero_polar.mem_of_mem hB, hb⟩
  obtain ⟨x, hx⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := E) ψ
  have hcx : c x = z := by
    by_contra hne
    obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hne
    have he := congrArg (fun p : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ p (e φ)) hx
    have he' : φ (c x) = φ z := by
      change (e φ) x = e.symm (e φ) z at he
      simpa only [LinearEquiv.symm_apply_apply, e, c,
        UniformSpace.Completion.strongDualEquiv_apply,
        UniformSpace.Completion.coeCLM_apply] using he
    exact (ne_of_lt hφ) (congrArg RCLike.re he')
  refine ⟨x, ?_, hcx⟩
  have hcl := hc.isInducing.closure_eq_preimage_closure_image B
  rw [hBcl.closure_eq] at hcl
  have hz' : x ∈ c ⁻¹' closure (c '' B) := by
    change c x ∈ closure (c '' B)
    rw [hcx]
    exact hz
  exact hcl.symm ▸ hz'

end SemiReflexive
