/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import Mathlib.Topology.Algebra.UniformMulAction
public import TopologicalGroups.Completion

/-!
# Completion of topological vector spaces

The hypothesis `UniformContinuousConstSMul` provides Mathlib's module structure on the
completion. The local-convexity consequence is in `LocallyConvexSpaces.Completion`.

## Main definitions

* `UniformSpace.Completion.coeCLM`: the canonical map as a continuous linear map.
* `UniformSpace.Completion.strongDualEquiv`: restriction identifies the continuous duals of the
  completion and of the space.

## Main statements

* `UniformSpace.Completion.instContinuousSMul`: scalar multiplication on the completion is
  jointly continuous.
* `UniformSpace.Completion.denseRange_coeCLM`, `UniformSpace.Completion.isUniformInducing_coeCLM`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], I §1.5, II §4.1
-/

public section

open Set Filter

open scoped Topology Pointwise

namespace UniformSpace.Completion

section Module

variable (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [UniformSpace E]
  [IsUniformAddGroup E] [UniformContinuousConstSMul 𝕜 E] [ContinuousSMul 𝕜 E]

/-- The completion of a topological vector space is a topological vector space: scalar
multiplication on the completion is jointly continuous. -/
instance instContinuousSMul : ContinuousSMul 𝕜 (Completion E) := by
  -- For a neighbourhood `W` of zero in the completion: a radius `δ` and a neighbourhood `N`
  -- of zero such that `a • m ∈ W` for `‖a‖ < δ` and `m ∈ N`.
  have key (W : Set (Completion E)) (hW : W ∈ 𝓝 (0 : Completion E)) :
      ∃ δ > 0, ∃ N ∈ 𝓝 (0 : Completion E), ∀ a : 𝕜, ‖a‖ < δ → ∀ m ∈ N, a • m ∈ W := by
    obtain ⟨W', ⟨hW', hW'cl⟩, hW'W⟩ := (closed_nhds_basis (0 : Completion E)).mem_iff.mp hW
    have hV : ((↑) : E → Completion E) ⁻¹' W' ∈ 𝓝 (0 : E) :=
      (continuous_coe E).continuousAt.preimage_mem_nhds (by rwa [coe_zero])
    have hsmul : Tendsto (fun p : 𝕜 × E ↦ p.1 • p.2) (𝓝 (0, 0)) (𝓝 0) := by
      have h := (continuous_smul (M := 𝕜) (X := E)).tendsto (0, 0)
      rwa [zero_smul] at h
    obtain ⟨A, hA, V₁, hV₁, hAV⟩ := mem_nhds_prod_iff.mp (hsmul hV)
    obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp hA
    refine ⟨δ, hδ, closure (((↑) : E → Completion E) '' V₁),
      hasBasis_nhds_zero_closure_image.mem_of_mem hV₁, fun a ha m hm ↦ hW'W ?_⟩
    have hc : Continuous fun m : Completion E ↦ a • m := continuous_const_smul a
    refine hW'cl.closure_subset (map_mem_closure hc hm ?_)
    rintro _ ⟨x, hx, rfl⟩
    rw [← coe_smul]
    exact hAV (show (a, x) ∈ A ×ˢ V₁ from ⟨hδA (by simpa using ha), hx⟩)
  refine ContinuousSMul.of_nhds_zero ?_ (fun m ↦ ?_) fun a ↦ ?_
  · intro W hW
    obtain ⟨δ, hδ, N, hN, h⟩ := key W hW
    refine mem_map.mpr (mem_of_superset (prod_mem_prod (Metric.ball_mem_nhds 0 hδ) hN) ?_)
    rintro ⟨a, m⟩ ⟨ha, hm⟩
    exact h a (by simpa using ha) m hm
  · intro W hW
    -- Split `m` as a point of `E` plus a small remainder.
    obtain ⟨W₁, hW₁, hW₁W⟩ : ∃ W₁ ∈ 𝓝 (0 : Completion E), ∀ u ∈ W₁, ∀ v ∈ W₁, u + v ∈ W := by
      have hadd : Tendsto (fun q : Completion E × Completion E ↦ q.1 + q.2) (𝓝 (0, 0)) (𝓝 0) := by
        have h := (continuous_add (M := Completion E)).tendsto (0, 0)
        rwa [add_zero] at h
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hadd hW)
      exact ⟨A ∩ B, inter_mem hA hB, fun u hu v hv ↦ hAB (show (u, v) ∈ A ×ˢ B from ⟨hu.1, hv.2⟩)⟩
    obtain ⟨δ, hδ, N, hN, h⟩ := key W₁ hW₁
    have hc : ContinuousAt (fun z : Completion E ↦ m - z) m := by fun_prop
    have hpre : {z : Completion E | m - z ∈ N} ∈ 𝓝 m :=
      hc.preimage_mem_nhds (by simpa using hN)
    obtain ⟨x, hx⟩ := denseRange_coe.exists_mem_open isOpen_interior
      ⟨m, mem_interior_iff_mem_nhds.mpr hpre⟩
    have hxN : m - (x : Completion E) ∈ N :=
      interior_subset (s := {z : Completion E | m - z ∈ N}) hx
    -- `a • x` tends to zero in `E`.
    have hax : Tendsto (fun a : 𝕜 ↦ ((a • x : E) : Completion E)) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun a : 𝕜 ↦ a • x) (𝓝 0) (𝓝 (0 : E)) := by
        have hcx : Continuous fun a : 𝕜 ↦ a • x := continuous_id.smul continuous_const
        have h2 := hcx.tendsto (0 : 𝕜)
        rwa [zero_smul] at h2
      have h3 := ((continuous_coe E).tendsto 0).comp h1
      rwa [coe_zero] at h3
    have hax'' : ∀ᶠ a : 𝕜 in 𝓝 0, ((a • x : E) : Completion E) ∈ W₁ := hax hW₁
    refine mem_map.mpr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : 𝕜) hδ, hax''] with a ha hax'
    have hsplit : a • m = a • (m - (x : Completion E)) + ((a • x : E) : Completion E) := by
      rw [coe_smul, ← smul_add, sub_add_cancel]
    rw [mem_preimage, hsplit]
    exact hW₁W _ (h a (by simpa using ha) _ hxN) _ hax'
  · have h := (continuous_const_smul (T := Completion E) a).tendsto 0
    rwa [smul_zero] at h

omit [ContinuousSMul 𝕜 E] in
/-- The canonical map of a topological vector space into its completion, as a continuous linear
map. -/
@[expose]
def coeCLM : E →L[𝕜] Completion E where
  toFun := (↑)
  map_add' := coe_add
  map_smul' := fun c x ↦ coe_smul c x
  cont := continuous_coe E

variable {𝕜 E}

omit [ContinuousSMul 𝕜 E] in
/-- The canonical map into the completion as a function. -/
@[simp]
theorem coeCLM_apply (x : E) : coeCLM 𝕜 E x = (x : Completion E) :=
  rfl

variable (𝕜 E)

omit [ContinuousSMul 𝕜 E] in
/-- The canonical map into the completion has dense range. -/
theorem denseRange_coeCLM : DenseRange (coeCLM 𝕜 E) :=
  denseRange_coe

omit [ContinuousSMul 𝕜 E] in
/-- The canonical map into the completion is uniformly inducing. -/
theorem isUniformInducing_coeCLM : IsUniformInducing (coeCLM 𝕜 E) :=
  isUniformInducing_coe E

end Module


section Dual

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [UniformContinuousConstSMul 𝕜 E]

/-- **The dual of the completion**: restriction to `E` is a linear equivalence between the
continuous dual of the completion of `E` and the continuous dual of `E`. -/
@[expose]
noncomputable def strongDualEquiv : StrongDual 𝕜 (Completion E) ≃ₗ[𝕜] StrongDual 𝕜 E where
  toFun ψ := ψ.comp (coeCLM 𝕜 E)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := φ.extend (coeCLM 𝕜 E)
  left_inv ψ :=
    ContinuousLinearMap.extend_unique _ (denseRange_coeCLM 𝕜 E) (isUniformInducing_coeCLM 𝕜 E)
      ψ rfl
  right_inv φ := ContinuousLinearMap.ext fun x ↦
    ContinuousLinearMap.extend_eq φ (denseRange_coeCLM 𝕜 E) (isUniformInducing_coeCLM 𝕜 E) x

variable {𝕜 E}

/-- The identification of the duals of `E` and of its completion is restriction to `E`. -/
theorem strongDualEquiv_apply (ψ : StrongDual 𝕜 (Completion E)) (x : E) :
    strongDualEquiv 𝕜 E ψ x = ψ (x : Completion E) :=
  rfl

/-- The inverse of the identification of the duals extends a functional to the completion. -/
theorem strongDualEquiv_symm_apply_coe (φ : StrongDual 𝕜 E) (x : E) :
    (strongDualEquiv 𝕜 E).symm φ (x : Completion E) = φ x :=
  ContinuousLinearMap.extend_eq φ (denseRange_coeCLM 𝕜 E) (isUniformInducing_coeCLM 𝕜 E) x

end Dual

end UniformSpace.Completion
