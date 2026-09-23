/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.MackeyBounded
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Topologies with the same dual

Two locally convex vector space topologies on `E` with the same continuous linear functionals
have the same closed convex sets, by the Hahn–Banach theorem, and the same bounded sets, by
Mackey's theorem. In particular this holds for all topologies that are compatible with a given
pairing, from the weak topology to the Mackey topology.

The statements are formulated for one topology `t₁` that is an instance and a second topology
`t₂` that is an explicit argument, under the assumption that every `t₁`-continuous functional is
`t₂`-continuous (or conversely); the symmetric statements follow by exchanging the roles.

## Main statements

* `Convex.isClosed_of_forall_continuous_linearMap`: a convex `t₁`-closed set is `t₂`-closed if
  every `t₁`-continuous linear functional is `t₂`-continuous.
* `Bornology.IsVonNBounded.of_forall_continuous_linearMap`: a `t₂`-bounded set is `t₁`-bounded
  if every `t₁`-continuous linear functional is `t₂`-continuous.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §3.1, §3.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], IV §1.2, IV §2.4
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §20.7, §20.11

## Tags

compatible topology, dual pair, Mackey theorem, closed convex set
-/

public section

open Set Bornology

open scoped Topology

-- The second topology `t₂` is declared before the instance topology, so that instance
-- resolution finds the latter.
variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] {t₂ : TopologicalSpace E} [t₁ : TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- Let `E` be a locally convex space and `t₂` a second topology on `E` for which every
continuous linear functional of `E` is continuous. Then every closed convex subset of `E` is
closed for `t₂`. -/
theorem Convex.isClosed_of_forall_continuous_linearMap
    (h : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f → @Continuous E 𝕜 t₂ _ f) {s : Set E}
    (hs : Convex ℝ s) (hcl : IsClosed s) : @IsClosed E t₂ s := by
  refine (@isOpen_compl_iff E s t₂).mp
    ((@isOpen_iff_forall_mem_open E t₂ sᶜ).mpr fun x hx ↦ ?_)
  -- Separate `x` from `s` by a continuous functional; its half space is open for `t₂`.
  obtain ⟨f, u, hfx, hfs⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := 𝕜) hs hcl hx
  have hf₂ : @Continuous E 𝕜 t₂ _ f := h f.toLinearMap f.continuous
  refine ⟨{z | RCLike.re (f z) < u}, fun z hz hzs ↦ ?_, ?_, hfx⟩
  · exact (lt_asymm (hfs z hzs) hz).elim
  · exact @IsOpen.preimage E ℝ t₂ _ _ (@Continuous.comp E 𝕜 ℝ t₂ _ _ _ _
      RCLike.continuous_re hf₂) _ isOpen_Iio

/-- Let `E` be a locally convex space and `t₂` a second topology on `E` for which every
continuous linear functional of `E` is continuous. Then every `t₂`-bounded set is bounded in
`E`, by Mackey's theorem. -/
theorem Bornology.IsVonNBounded.of_forall_continuous_linearMap
    (h : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f → @Continuous E 𝕜 t₂ _ f) {S : Set E}
    (hS : @IsVonNBounded 𝕜 E _ _ _ t₂ S) : IsVonNBounded 𝕜 S := by
  rw [Bornology.isVonNBounded_iff_forall_strongDual]
  intro φ
  -- The image of a bounded set under a continuous linear functional is bounded.
  have hφ₂ : @Continuous E 𝕜 t₂ _ φ := h φ.toLinearMap φ.continuous
  have himage : IsVonNBounded 𝕜 (φ '' S) := by
    intro V hV
    have hpre : φ ⁻¹' V ∈ @nhds E t₂ 0 := by
      have ht := @Continuous.tendsto E 𝕜 t₂ _ φ hφ₂ 0
      rw [map_zero] at ht
      exact ht hV
    refine Filter.Eventually.mono (hS hpre) fun a ha ↦ ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hwx⟩ := ha hx
    have hwx' : a • w = x := hwx
    exact ⟨φ w, hw, by rw [← hwx', map_smul]⟩
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).mp himage
  exact ⟨C, fun x hx ↦ hC _ ⟨x, hx, rfl⟩⟩
