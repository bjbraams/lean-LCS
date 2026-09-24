/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Completion
public import LocallyConvexSpaces.GrothendieckApproximation

/-!
# Grothendieck's completeness theorem

Let `E` be a complete locally convex space. If `f` is a linear functional on the dual
`E'` whose restriction to the polar `U°` of every neighbourhood `U` of zero (that is, to every
equicontinuous set) is weak-* continuous, then `f` is the evaluation at a point of `E`. This is
one direction of **Grothendieck's completeness theorem**. Conversely, this representation
property implies completeness: every point of the completion defines such a form, and hence
comes from the original space. Neither direction requires Hausdorffness.

The proof uses the approximation lemma `StrongDual.exists_forall_mem_polar_norm_sub_le`: for
every neighbourhood `U` of zero there is `a U : E` with `‖f φ - φ (a U)‖ ≤ 1` on `U°`. For closed,
`ℝ`-convex, balanced neighbourhoods `V ⊆ U` the bipolar theorem gives `a V - a U ∈ 2 • U`, so the
points `a U` form a Cauchy filter along the filter of small neighbourhoods. Its limit `x`
satisfies `‖f φ - φ x‖ ≤ 3` on every `U°`, and therefore `f φ = φ x`.

## Main statements

* `StrongDual.exists_forall_eq_apply_of_completeSpace`.
* `StrongDual.completeSpace_of_forall_exists_eq_apply`.
* `StrongDual.completeSpace_iff_forall_exists_eq_apply`.

The explicit completion model, including its topology of uniform convergence on equicontinuous
sets, is developed in `LocallyConvexSpaces.GrothendieckCompletion`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §6.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §3.6
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.9

## Tags

Grothendieck completeness theorem, complete space, equicontinuous set, weak-* topology
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise Uniformity

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

namespace StrongDual

/-- The closed, `ℝ`-convex, balanced neighbourhoods of zero. -/
private def goodNhds (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [TopologicalSpace E] : Set (Set E) :=
  {U | U ∈ 𝓝 (0 : E) ∧ Convex ℝ U ∧ Balanced 𝕜 U ∧ IsClosed U}

/-- Every neighbourhood of zero contains a closed, `ℝ`-convex, balanced neighbourhood of zero. -/
private theorem exists_goodNhds_subset {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ U ∈ goodNhds 𝕜 E, U ⊆ W := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨C, ⟨hC, hCcl⟩, hCW⟩ := (closed_nhds_basis (0 : E)).mem_iff.mp hW
  obtain ⟨V, ⟨hV, hVc, hVb⟩, hVC⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hC
  exact ⟨closure V, ⟨mem_of_superset hV subset_closure, hVc.closure, hVb.closure,
    isClosed_closure⟩, (closure_minimal hVC hCcl).trans hCW⟩

/-- Two points that approximate a linear functional `f` on the dual to within one on the polar
of a closed, `ℝ`-convex, balanced neighbourhood `U` of zero differ by an element of `2 • U`. -/
private theorem sub_mem_two_smul_of_forall_norm_sub_le (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜)
    {U : Set E} (hU : U ∈ goodNhds 𝕜 E) {b c : E} (hb : ∀ φ ∈ polar 𝕜 U, ‖f φ - φ b‖ ≤ 1)
    (hc : ∀ φ ∈ polar 𝕜 U, ‖f φ - φ c‖ ≤ 1) : c - b ∈ (2 : ℝ) • U := by
  refine ⟨(2 : ℝ)⁻¹ • (c - b), ?_, smul_inv_smul₀ two_ne_zero _⟩
  refine (StrongDual.bipolar_eq_self (𝕜 := 𝕜) hU.2.1 hU.2.2.1 hU.2.2.2
    ⟨0, mem_of_mem_nhds hU.1⟩).subset fun φ hφ ↦ ?_
  have h1 := hb φ hφ
  have h2 := hc φ hφ
  change ‖φ ((2 : ℝ)⁻¹ • (c - b))‖ ≤ 1
  rw [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), map_sub]
  have h3 := norm_sub_le (f φ - φ b) (f φ - φ c)
  have he : (f φ - φ b) - (f φ - φ c) = φ c - φ b := by ring
  rw [he] at h3
  linarith

/-- The filter of small closed, `ℝ`-convex, balanced neighbourhoods of zero is nontrivial. -/
private theorem neBot_smallSets_inf_goodNhds :
    ((𝓝 (0 : E)).smallSets ⊓ 𝓟 (goodNhds 𝕜 E)).NeBot := by
  rw [(hasBasis_smallSets (𝓝 (0 : E))).inf_principal_neBot_iff]
  intro W hW
  obtain ⟨U, hU, hUW⟩ := exists_goodNhds_subset (𝕜 := 𝕜) hW
  exact ⟨U, hUW, hU⟩

omit [IsScalarTower ℝ 𝕜 E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] in
/-- The closed, `ℝ`-convex, balanced neighbourhoods of zero inside a given one form a set of the
filter of small such neighbourhoods. -/
private theorem powerset_inter_goodNhds_mem {U : Set E} (hU : U ∈ goodNhds 𝕜 E) :
    𝒫 U ∩ goodNhds 𝕜 E ∈ (𝓝 (0 : E)).smallSets ⊓ 𝓟 (goodNhds 𝕜 E) :=
  inter_mem_inf ((hasBasis_smallSets (𝓝 (0 : E))).mem_of_mem hU.1) (mem_principal_self _)

/-- Points `a U` with `a V - a U ∈ 2 • U` for closed, `ℝ`-convex, balanced neighbourhoods `V ⊆ U` of
zero form a Cauchy family along the filter of small such neighbourhoods. -/
private theorem cauchy_map_of_forall_sub_mem {a : Set E → E}
    (hdiff : ∀ U ∈ goodNhds 𝕜 E, ∀ V ∈ goodNhds 𝕜 E, V ⊆ U → a V - a U ∈ (2 : ℝ) • U) :
    Cauchy (((𝓝 (0 : E)).smallSets ⊓ 𝓟 (goodNhds 𝕜 E)).map a) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have hG := neBot_smallSets_inf_goodNhds (𝕜 := 𝕜) (E := E)
  refine cauchy_iff.mpr ⟨hG.map a, fun R hR ↦ ?_⟩
  rw [uniformity_eq_comap_nhds_zero E] at hR
  obtain ⟨W, hW, hWR⟩ := hR
  -- A good neighbourhood `U` with `4 • U ⊆ W`.
  have hW4 : (4 : ℝ)⁻¹ • W ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff (by norm_num : (4 : ℝ)⁻¹ ≠ 0)).mpr hW
  obtain ⟨U, hU, hUW⟩ := exists_goodNhds_subset (𝕜 := 𝕜) hW4
  refine ⟨a '' (𝒫 U ∩ goodNhds 𝕜 E), image_mem_map (powerset_inter_goodNhds_mem hU), ?_⟩
  rintro ⟨_, _⟩ ⟨⟨V, ⟨hVU, hV⟩, rfl⟩, ⟨V', ⟨hV'U, hV'⟩, rfl⟩⟩
  refine hWR ?_
  change a V' - a V ∈ W
  obtain ⟨u, hu, hu2⟩ := hdiff U hU V hV hVU
  obtain ⟨u', hu', hu2'⟩ := hdiff U hU V' hV' hV'U
  have hu2e : (2 : ℝ) • u = a V - a U := hu2
  have hu2e' : (2 : ℝ) • u' = a V' - a U := hu2'
  -- `a V' - a V = 4 • ((1 / 2) • u' + (1 / 2) • (-u))`.
  have hmid : (2 : ℝ)⁻¹ • u' + (2 : ℝ)⁻¹ • (-u) ∈ U :=
    hU.2.1 hu' (hU.2.2.1.neg_mem_iff.mpr hu) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨w, hw, hwe⟩ := hUW hmid
  have hwe' : (4 : ℝ)⁻¹ • w = (2 : ℝ)⁻¹ • u' + (2 : ℝ)⁻¹ • (-u) := hwe
  have hw4 : w = a V' - a V := by
    have h4 : w = (4 : ℝ) • ((4 : ℝ)⁻¹ • w) := (smul_inv_smul₀ (by norm_num) w).symm
    rw [h4, hwe', smul_add, smul_smul, smul_smul, smul_neg]
    norm_num
    rw [hu2e, hu2e']
    abel
  exact hw4 ▸ hw

/-- If the linear functional `f` on the dual is within `3` of the evaluation at `x` on the polar
of every closed, `ℝ`-convex, balanced neighbourhood of zero, then `f` is the evaluation at `x`. -/
private theorem eq_apply_of_forall_norm_sub_le (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜) {x : E}
    (h3 : ∀ U ∈ goodNhds 𝕜 E, ∀ φ ∈ polar 𝕜 U, ‖f φ - φ x‖ ≤ 3) (φ : StrongDual 𝕜 E) :
    f φ = φ x := by
  -- Every functional lies in the polar of a good neighbourhood; then rescale.
  have hφnhds : {y : E | ‖φ y‖ ≤ 1} ∈ 𝓝 (0 : E) := by
    have hc : ContinuousAt (fun y ↦ ‖φ y‖) 0 := (continuous_norm.comp φ.continuous).continuousAt
    exact hc.preimage_mem_nhds (Iic_mem_nhds (by simp))
  obtain ⟨U, hU, hUφ⟩ := exists_goodNhds_subset (𝕜 := 𝕜) hφnhds
  by_contra hne
  have hpos : 0 < ‖f φ - φ x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- Apply the estimate to `δ • U` and `δ⁻¹ • φ`, with `3 * δ < ‖f φ - φ x‖`.
  let δ : ℝ := ‖f φ - φ x‖ / 4
  have hδ : 0 < δ := by positivity
  have hδU : (δ : 𝕜) • U ∈ goodNhds 𝕜 E := by
    have hδne : (δ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
    refine ⟨(set_smul_mem_nhds_zero_iff hδne).mpr hU.1, ?_, hU.2.2.1.smul _,
      hU.2.2.2.smul_of_ne_zero hδne⟩
    have hlin : IsLinearMap ℝ (fun y : E ↦ (δ : 𝕜) • y) :=
      ⟨smul_add _, fun c y ↦ smul_comm _ c y⟩
    rw [← image_smul]
    exact hU.2.1.is_linear_image hlin
  have hφδ : ((δ : 𝕜)⁻¹ • φ) ∈ polar 𝕜 ((δ : 𝕜) • U) := by
    rintro _ ⟨u, hu, rfl⟩
    change ‖((δ : 𝕜)⁻¹ • φ) ((δ : 𝕜) • u)‖ ≤ 1
    have hδne : (δ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
    have hval : ((δ : 𝕜)⁻¹ • φ) ((δ : 𝕜) • u) = φ u := by
      change (δ : 𝕜)⁻¹ • φ ((δ : 𝕜) • u) = φ u
      rw [map_smul, smul_smul, inv_mul_cancel₀ hδne, one_smul]
    rw [hval]
    exact hUφ hu
  have h := h3 _ hδU _ hφδ
  have hval : f ((δ : 𝕜)⁻¹ • φ) - ((δ : 𝕜)⁻¹ • φ) x = (δ : 𝕜)⁻¹ * (f φ - φ x) := by
    change f ((δ : 𝕜)⁻¹ • φ) - (δ : 𝕜)⁻¹ • φ x = _
    rw [map_smul, smul_eq_mul, smul_eq_mul, mul_sub]
  rw [hval, norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hδ, inv_mul_le_iff₀ hδ] at h
  have : ‖f φ - φ x‖ ≤ 3 * (‖f φ - φ x‖ / 4) := by
    have h' : δ * 3 = 3 * (‖f φ - φ x‖ / 4) := by simp only [δ]; ring
    linarith
  linarith

/-- **Grothendieck's completeness theorem**, main half: on the dual of a complete
locally convex space, a linear functional whose restrictions to the polars of the neighbourhoods
of zero are weak-* continuous is the evaluation at a point of the space. -/
theorem exists_forall_eq_apply_of_completeSpace [CompleteSpace E]
    (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜)
    (hf : ∀ U ∈ 𝓝 (0 : E), ContinuousOn (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ))
      (WeakDual.polar 𝕜 U)) :
    ∃ x : E, ∀ φ : StrongDual 𝕜 E, f φ = φ x := by
  classical
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  -- Approximants `a U` with `‖f φ - φ (a U)‖ ≤ 1` on the polar of `U`.
  have hex (U : Set E) : ∃ a : E, U ∈ 𝓝 (0 : E) → ∀ φ ∈ polar 𝕜 U, ‖f φ - φ a‖ ≤ 1 := by
    by_cases hU : U ∈ 𝓝 (0 : E)
    · obtain ⟨a, ha⟩ := exists_forall_mem_polar_norm_sub_le U f (hf U hU) one_pos
      exact ⟨a, fun _ ↦ ha⟩
    · exact ⟨0, fun h ↦ absurd h hU⟩
  choose a ha using hex
  -- For good neighbourhoods `V ⊆ U` the difference `a V - a U` lies in `2 • U`.
  have hdiff : ∀ U ∈ goodNhds 𝕜 E, ∀ V ∈ goodNhds 𝕜 E, V ⊆ U → a V - a U ∈ (2 : ℝ) • U :=
    fun U hU V hV hVU ↦ sub_mem_two_smul_of_forall_norm_sub_le f hU (ha U hU.1)
      fun φ hφ ↦ ha V hV.1 φ (LinearMap.polar_antitone _ hVU hφ)
  -- The approximants along small good neighbourhoods form a Cauchy filter; let `x` be a limit.
  let F : Filter E := ((𝓝 (0 : E)).smallSets ⊓ 𝓟 (goodNhds 𝕜 E)).map a
  have hcauchy : Cauchy F := cauchy_map_of_forall_sub_mem hdiff
  have hF : F.NeBot := hcauchy.1
  obtain ⟨x, hx⟩ := CompleteSpace.complete hcauchy
  -- On the polar of a good neighbourhood `U` the functional `f` is within `3` of `x`.
  refine ⟨x, eq_apply_of_forall_norm_sub_le f fun U hU φ hφ ↦ ?_⟩
  -- `x` lies in the closed set `a U + 2 • U`.
  have hclosed : IsClosed {y : E | y - a U ∈ (2 : ℝ) • U} :=
    (hU.2.2.2.smul_of_ne_zero (two_ne_zero : (2 : ℝ) ≠ 0)).preimage
      (continuous_id.sub continuous_const)
  have hmem : a '' (𝒫 U ∩ goodNhds 𝕜 E) ⊆ {y : E | y - a U ∈ (2 : ℝ) • U} := by
    rintro _ ⟨V, ⟨hVU, hV⟩, rfl⟩
    exact hdiff U hU V hV hVU
  have hxcl : x ∈ {y : E | y - a U ∈ (2 : ℝ) • U} := by
    refine hclosed.closure_subset_iff.mpr hmem ?_
    rw [mem_closure_iff_clusterPt]
    exact hF.mono (le_inf hx
      (le_principal_iff.mpr (image_mem_map (powerset_inter_goodNhds_mem hU))))
  obtain ⟨u, hu, hue⟩ := hxcl
  have hue' : (2 : ℝ) • u = x - a U := hue
  have h1 := ha U hU.1 φ hφ
  have h2 : ‖φ (x - a U)‖ ≤ 2 := by
    rw [← hue', ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : ‖φ u‖ ≤ 1 := hφ u hu
    linarith
  have hsplit : f φ - φ x = (f φ - φ (a U)) - φ (x - a U) := by
    rw [map_sub]
    ring
  rw [hsplit]
  have := norm_sub_le (f φ - φ (a U)) (φ (x - a U))
  linarith

/-- **Grothendieck's completeness criterion**, converse: if every linear form on the dual
that is weak-* continuous on each zero-neighbourhood polar is evaluation at a point, then the
space is complete. Separation is not needed for this direction. This is
Schaefer–Wolff, IV §6.2, using extension of functionals to the completion. -/
theorem completeSpace_of_forall_exists_eq_apply
    (h : ∀ f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜,
      (∀ U ∈ 𝓝 (0 : E), ContinuousOn
        (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U)) →
      ∃ x : E, ∀ φ : StrongDual 𝕜 E, f φ = φ x) : CompleteSpace E := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : UniformContinuousConstSMul 𝕜 E :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 E
  let : UniformContinuousConstSMul ℝ E :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ E
  suffices hs : Function.Surjective (UniformSpace.Completion.coeCLM 𝕜 E) from
    ((UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 E).completeSpace_congr hs).mpr
      inferInstance
  intro z
  let e := UniformSpace.Completion.strongDualEquiv 𝕜 E
  let f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜 :=
    { toFun := fun φ ↦ e.symm φ z
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  obtain ⟨x, hx⟩ := h f fun U hU ↦
    UniformSpace.Completion.continuousOn_extend_eval_polar z hU
  refine ⟨x, ?_⟩
  by_contra hne
  obtain ⟨ψ, hψ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hne
  have he : ψ z = ψ (x : UniformSpace.Completion E) := by
    simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, e,
      UniformSpace.Completion.strongDualEquiv_apply] using hx (e ψ)
  exact (ne_of_lt hψ) (congrArg RCLike.re he.symm)

/-- A locally convex space is complete if and only if every linear form on its dual
that is weak-* continuous on each zero-neighbourhood polar is evaluation at a point.
This is the equicontinuous-set form of **Grothendieck's completeness criterion**. -/
theorem completeSpace_iff_forall_exists_eq_apply :
    CompleteSpace E ↔ ∀ f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜,
      (∀ U ∈ 𝓝 (0 : E), ContinuousOn
        (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U)) →
      ∃ x : E, ∀ φ : StrongDual 𝕜 E, f φ = φ x :=
  ⟨fun _ ↦ exists_forall_eq_apply_of_completeSpace, completeSpace_of_forall_exists_eq_apply⟩

end StrongDual
