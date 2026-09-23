/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.BanachDisk
public import LocallyConvexSpaces.Bipolar
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Uniform approximation of linear forms and Grothendieck's completeness theorem

A linear form on a real or complex locally convex space that is continuous on a closed
convex balanced set can be uniformly approximated there by continuous linear forms on the
whole space. Separation of its graph from a point on the scalar axis gives the approximation.

Applied to the weak dual, this shows that a linear form weak-* continuous on a polar is
uniformly approximated there by evaluations at points of the original space. Mathlib's weak
representation theorem identifies the continuous approximants as evaluations. The set whose
polar is used need not be a neighbourhood, and no separation assumption is needed.

## Main statements

* `LinearMap.exists_strongDual_norm_sub_le_of_continuousOn`: approximation on a closed disk.
* `StrongDual.exists_forall_mem_polar_norm_sub_le`: approximation on any polar by evaluations.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §6.2.
  The graph-separation argument is independently formalized.
-/

public section

open Set Filter Function
open scoped Topology Pointwise

section Approximation

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- A linear form continuous on a closed convex balanced set can be approximated uniformly
there by continuous linear forms on the entire space. Boundedness of the set is unnecessary.
This independently formalizes the approximation step in Schaefer–Wolff, IV §6.2, using
separation of its graph in the product with the scalar field. -/
theorem LinearMap.exists_strongDual_norm_sub_le_of_continuousOn
    (f : E →ₗ[𝕜] 𝕜) {S : Set E} (hScl : IsClosed S) (hSc : Convex ℝ S)
    (hSb : Balanced 𝕜 S) (hf : ContinuousOn f S) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : StrongDual 𝕜 E, ∀ x ∈ S, ‖f x - g x‖ ≤ ε := by
  by_cases hSne : S.Nonempty
  · let G : Set (E × 𝕜) := {p | p.1 ∈ S ∧ f p.1 = p.2}
    let j : E →ₗ[𝕜] E × 𝕜 := LinearMap.id.prod f
    have hG : G = j '' S := by
      ext ⟨x, t⟩
      change (x ∈ S ∧ f x = t) ↔ _
      constructor
      · rintro ⟨hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, h⟩
        cases h
        exact ⟨hy, rfl⟩
    have hGcl : IsClosed G := (hScl.preimage continuous_fst).isClosed_eq
      (hf.comp continuous_fst.continuousOn (fun _ hx ↦ hx)) continuous_snd.continuousOn
    have hGc : Convex ℝ G := hG ▸ hSc.is_linear_image (j.restrictScalars ℝ).isLinear
    have hGb : Balanced 𝕜 G := hG ▸ hSb.image j
    have hGne : G.Nonempty := hG ▸ hSne.image j
    have hp : (0, (ε : 𝕜)) ∉ G := by
      rintro ⟨_, h⟩
      have hε0 : (ε : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hε.ne'
      exact hε0 (by simpa using h.symm)
    obtain ⟨φ, hφ, hφp⟩ := StrongDual.exists_mem_polar_one_lt_norm hGc hGb hGcl hGne hp
    let d : 𝕜 := φ (0, 1)
    let a : StrongDual 𝕜 E := φ.comp (ContinuousLinearMap.inl 𝕜 E 𝕜)
    have hpd : φ (0, (ε : 𝕜)) = (ε : 𝕜) * d := by
      simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using
        map_smul φ (ε : 𝕜) (0, 1)
    have hεd : 1 < ε * ‖d‖ := by
      simpa only [hpd, norm_mul, RCLike.norm_ofReal, abs_of_pos hε] using hφp
    have hdpos : 0 < ‖d‖ := by nlinarith [norm_nonneg d]
    have hd : d ≠ 0 := norm_pos_iff.mp hdpos
    refine ⟨-d⁻¹ • a, fun x hx ↦ ?_⟩
    have hval : φ (x, f x) = a x + d * f x := by
      have heq : (x, f x) = (x, 0) + f x • (0, 1) := by simp
      rw [heq, map_add, map_smul]
      change a x + f x * d = _
      ring
    have heq : f x - (-d⁻¹ • a) x = d⁻¹ * φ (x, f x) := by
      change f x - (-d⁻¹ * a x) = _
      rw [hval]
      field_simp
      ring
    rw [heq, norm_mul, norm_inv]
    calc ‖d‖⁻¹ * ‖φ (x, f x)‖ ≤ ‖d‖⁻¹ :=
          mul_le_of_le_one_right (inv_nonneg.mpr hdpos.le) (hφ _ ⟨hx, rfl⟩)
      _ ≤ ε := by
        apply (mul_le_mul_iff_left₀ hdpos).mp
        rw [inv_mul_cancel₀ hdpos.ne']
        nlinarith
  · exact ⟨0, fun x hx ↦ (hSne ⟨x, hx⟩).elim⟩

end Approximation

namespace StrongDual

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The disk hull of a polar is the polar itself. -/
theorem diskHull_polar (U : Set E) : diskHull 𝕜 (polar 𝕜 U) = polar 𝕜 U :=
  diskHull_eq_self (LinearMap.convex_polar _ _) (LinearMap.balanced_polar _ _)
    ⟨0, zero_mem_polar 𝕜 U⟩

/-- A linear functional on the dual that is weak-* continuous on a polar can be approximated
uniformly on that polar by evaluations at points of the original space. The set `U` is
arbitrary; in particular it may be a zero neighbourhood as in Grothendieck's criterion. -/
theorem exists_forall_mem_polar_norm_sub_le (U : Set E)
    (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜)
    (hf : ContinuousOn (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U))
    {ε : ℝ} (hε : 0 < ε) : ∃ a : E, ∀ φ ∈ polar 𝕜 U, ‖f φ - φ a‖ ≤ ε := by
  let : IsScalarTower ℝ 𝕜 (WeakBilin (topDualPairing 𝕜 E)) :=
    inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual 𝕜 E))
  let : LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 E)) :=
    WeakBilin.locallyConvexSpace
  let fw : WeakBilin (topDualPairing 𝕜 E) →ₗ[𝕜] 𝕜 := f
  let S : Set (WeakBilin (topDualPairing 𝕜 E)) := (topDualPairing 𝕜 E).flip.polar U
  have hScl : IsClosed S := (topDualPairing 𝕜 E).flip.polar_isClosed U
  have hSc : Convex ℝ S := (topDualPairing 𝕜 E).flip.convex_polar U
  have hSb : Balanced 𝕜 S := (topDualPairing 𝕜 E).flip.balanced_polar U
  have hfw : ContinuousOn fw S := hf
  have happrox : ∃ g : StrongDual 𝕜 (WeakBilin (topDualPairing 𝕜 E)),
      ∀ x ∈ S, ‖fw x - g x‖ ≤ ε := by
    -- Fix the weak-space structures before elaborating the polar hypotheses.
    exact @LinearMap.exists_strongDual_norm_sub_le_of_continuousOn
      𝕜 (WeakBilin (topDualPairing 𝕜 E)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance fw S hScl hSc hSb hfw
      ε hε
  obtain ⟨g, hg⟩ := happrox
  obtain ⟨a, ha⟩ := (topDualPairing 𝕜 E).dualEmbedding_surjective g
  refine ⟨a, fun φ hφ ↦ ?_⟩
  have h := hg (StrongDual.toWeakDual φ) hφ
  rw [← ha] at h
  exact h

end StrongDual
