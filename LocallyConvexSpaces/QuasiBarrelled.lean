/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.BarrelledDual
public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.MackeyBounded
public import LocallyConvexSpaces.Reflexive
public import LocallyConvexSpaces.StrongDualBounded
public import Mathlib.Analysis.LocallyConvex.Montel

/-!
# Quasi-barrelled spaces and the characterization of reflexive spaces

A topological vector space is *quasi-barrelled* (or *infrabarrelled*) if every lower semicontinuous
seminorm that is bounded on the bounded sets is continuous. This follows Mathlib's seminorm
definition of `BarrelledSpace`. For real or complex spaces it is equivalent to the classical
condition that every bornivorous barrel is a neighbourhood of zero. Barrelled spaces and
bornological spaces are quasi-barrelled. Dually, a locally convex space is quasi-barrelled if and
only if every strongly bounded subset of its dual is equicontinuous, and if and only if the
canonical map into the bidual is continuous.

A locally convex space is reflexive if and only if it is semi-reflexive and
quasi-barrelled, and if and only if it is semi-reflexive and barrelled. Montel spaces are
semi-reflexive, and barrelled Montel spaces are reflexive. The strong dual of a semi-reflexive
space is barrelled, and the strong dual of a reflexive space is reflexive, including with the
non-Hausdorff convention used here.

## Main definitions

* `QuasiBarrelledSpace 𝕜 E`: every lower semicontinuous seminorm that is bounded on the
  bounded sets is continuous.

## Main statements

* `QuasiBarrelledSpace.mem_nhds_zero`, `QuasiBarrelledSpace.of_forall_mem_nhds_zero`,
  `quasiBarrelledSpace_iff_forall_mem_nhds_zero`: the characterization by bornivorous barrels.
* `BarrelledSpace.toQuasiBarrelledSpace`, `BornologicalSpace.toQuasiBarrelledSpace`.
* `StrongDual.isBarrel_polar_of_isVonNBounded`,
  `StrongDual.isBornivorous_polar_of_isVonNBounded`: the polar in `E` of a strongly bounded
  subset of the dual is a bornivorous barrel.
* `QuasiBarrelledSpace.equicontinuous_of_isVonNBounded`,
  `QuasiBarrelledSpace.of_forall_equicontinuous`, `quasiBarrelledSpace_iff_forall_equicontinuous`:
  a locally convex space is quasi-barrelled if and only if every strongly bounded subset of its
  dual is equicontinuous.
* `StrongDual.exists_nhds_preimage_inclusionInDoubleDual_subset`: the canonical map of a locally
  convex space into its bidual is open onto its image.
* `StrongDual.continuous_inclusionInDoubleDual_of_forall_equicontinuous`,
  `QuasiBarrelledSpace.continuous_inclusionInDoubleDual`,
  `QuasiBarrelledSpace.of_continuous_inclusionInDoubleDual`: a locally convex space is
  quasi-barrelled if and only if its canonical map into the bidual is continuous.
* `SemiReflexiveSpace.isVonNBounded_of_forall_isVonNBounded`: in the dual of a semi-reflexive
  space pointwise bounded sets are strongly bounded.
* `BarrelledSpace.of_semiReflexiveSpace_of_quasiBarrelledSpace`.
* `reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace`,
  `reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace`.
* `SemiReflexiveSpace.barrelledSpace_strongDual`, `ReflexiveSpace.strongDual`.
* `MontelSpace.semiReflexiveSpace`, `MontelSpace.reflexiveSpace`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.5–5.8
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §4.1, IV §2.3, IV §2.5
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §23.4–23.5, §27.2

## Tags

quasi-barrelled, infrabarrelled, reflexive, semi-reflexive, Montel space
-/

public section

open Set Filter Bornology Function

open scoped Topology Pointwise

section Defs

variable (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] [TopologicalSpace E]

/-- A topological vector space is **quasi-barrelled** if every lower semicontinuous seminorm
that is bounded on the von Neumann bounded sets is continuous. This mirrors Mathlib's seminorm
definition of `BarrelledSpace`. For real or complex spaces it is equivalent to the classical
condition that every bornivorous barrel is a neighbourhood of zero; see
`quasiBarrelledSpace_iff_forall_mem_nhds_zero`. -/
class QuasiBarrelledSpace : Prop where
  /-- In a quasi-barrelled space every lower semicontinuous seminorm that is bounded on the
  bounded sets is continuous. -/
  continuous_of_lowerSemicontinuous_of_bddAbove : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p →
    (∀ s : Set E, IsVonNBounded 𝕜 s → BddAbove (p '' s)) → Continuous p

/-- A barrelled space is quasi-barrelled. -/
instance (priority := 100) BarrelledSpace.toQuasiBarrelledSpace [BarrelledSpace 𝕜 E] :
    QuasiBarrelledSpace 𝕜 E :=
  ⟨fun p hp _ ↦ p.continuous_of_lowerSemicontinuous hp⟩

/-- A bornological space is quasi-barrelled. -/
instance (priority := 100) BornologicalSpace.toQuasiBarrelledSpace [BornologicalSpace 𝕜 E] :
    QuasiBarrelledSpace 𝕜 E :=
  ⟨fun p _ hp ↦ BornologicalSpace.continuous_of_bddAbove p hp⟩

end Defs

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- In a real or complex quasi-barrelled space every bornivorous barrel is a neighbourhood of
zero. -/
theorem QuasiBarrelledSpace.mem_nhds_zero [QuasiBarrelledSpace 𝕜 E] (T : Set E)
    (hT : IsBarrel 𝕜 T) (hTb : IsBornivorous 𝕜 T) : T ∈ 𝓝 (0 : E) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have hpc : Continuous hT.gaugeSeminorm :=
    QuasiBarrelledSpace.continuous_of_lowerSemicontinuous_of_bddAbove _
      hT.lowerSemicontinuous_gaugeSeminorm fun _ ht ↦
        hT.gaugeSeminorm.bddAbove_image_of_isBornivorous hTb hT.closedBall_gaugeSeminorm.ge ht
  rw [← hT.closedBall_gaugeSeminorm]
  exact mem_of_superset ((hT.gaugeSeminorm.continuous_iff one_pos).mp hpc)
    (hT.gaugeSeminorm.ball_subset_closedBall 0 1)

/-- A real or complex topological vector space in which every bornivorous barrel is a
neighbourhood of zero is quasi-barrelled. -/
theorem QuasiBarrelledSpace.of_forall_mem_nhds_zero
    (h : ∀ T : Set E, IsBarrel 𝕜 T → IsBornivorous 𝕜 T → T ∈ 𝓝 (0 : E)) :
    QuasiBarrelledSpace 𝕜 E :=
  ⟨fun p hl hp ↦ Seminorm.continuous' (r := 1) (h _ (p.isBarrel_closedBall hl one_pos)
    ((p.isBornivorous_ball hp one_pos).mono (p.ball_subset_closedBall 0 1)))⟩

/-- A real or complex topological vector space is quasi-barrelled if and only if every
bornivorous barrel is a neighbourhood of zero. -/
theorem quasiBarrelledSpace_iff_forall_mem_nhds_zero :
    QuasiBarrelledSpace 𝕜 E ↔
      ∀ T : Set E, IsBarrel 𝕜 T → IsBornivorous 𝕜 T → T ∈ 𝓝 (0 : E) :=
  ⟨fun _ ↦ QuasiBarrelledSpace.mem_nhds_zero, QuasiBarrelledSpace.of_forall_mem_nhds_zero⟩

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] in
/-- The set of points at which all functionals of a strongly bounded set `H` are bounded by one
is bornivorous. -/
theorem StrongDual.isBornivorous_polar_of_isVonNBounded {H : Set (StrongDual 𝕜 E)}
    (hH : IsVonNBounded 𝕜 H) : IsBornivorous 𝕜 ((topDualPairing 𝕜 E).polar H) := by
  intro B hB
  -- The polar of `B` is a strong neighbourhood of zero, so it absorbs `H`.
  obtain ⟨R, hR⟩ := absorbs_iff_norm.mp
    (hH (StrongDual.hasBasis_nhds_zero_polar.mem_of_mem hB))
  refine absorbs_iff_norm.mpr ⟨max R 1, fun a ha x hx ↦ ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    linarith [le_max_right R 1]
  refine ⟨a⁻¹ • x, fun φ hφ ↦ ?_, by simp only; rw [smul_inv_smul₀ ha0]⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hR a ((le_max_left R 1).trans ha) hφ
  have hψφ' : a • ψ = φ := hψφ
  have hφx : φ (a⁻¹ • x) = ψ x := by
    rw [← hψφ']
    change a • ψ (a⁻¹ • x) = ψ x
    rw [map_smul, smul_eq_mul, smul_eq_mul, mul_inv_cancel_left₀ ha0]
  change ‖φ (a⁻¹ • x)‖ ≤ 1
  rw [hφx]
  exact hψ x hx

omit [IsTopologicalAddGroup E] in
/-- The set of points at which all functionals of a strongly bounded set `H` are bounded by one
is a barrel. -/
theorem StrongDual.isBarrel_polar_of_isVonNBounded {H : Set (StrongDual 𝕜 E)}
    (hH : IsVonNBounded 𝕜 H) : IsBarrel 𝕜 ((topDualPairing 𝕜 E).polar H) := by
  refine ⟨?_, LinearMap.convex_polar _ _, LinearMap.balanced_polar _ _,
    (StrongDual.isBornivorous_polar_of_isVonNBounded hH).absorbent⟩
  have h : (topDualPairing 𝕜 E).polar H = ⋂ φ ∈ H, {x : E | ‖φ x‖ ≤ 1} := by
    ext x
    simp only [mem_iInter]
    rfl
  rw [h]
  exact isClosed_biInter fun φ _ ↦ isClosed_le (continuous_norm.comp φ.continuous)
    continuous_const

/-- In the dual of a quasi-barrelled space every strongly bounded set is equicontinuous. -/
theorem QuasiBarrelledSpace.equicontinuous_of_isVonNBounded [QuasiBarrelledSpace 𝕜 E]
    {H : Set (StrongDual 𝕜 E)} (hH : IsVonNBounded 𝕜 H) :
    Equicontinuous ((↑) : H → E → 𝕜) := by
  have hT := QuasiBarrelledSpace.mem_nhds_zero _ (StrongDual.isBarrel_polar_of_isVonNBounded hH)
    (StrongDual.isBornivorous_polar_of_isVonNBounded hH)
  have hsub : H ⊆ StrongDual.polar 𝕜 ((topDualPairing 𝕜 E).polar H) :=
    fun φ hφ x hx ↦ hx φ hφ
  exact (StrongDual.equicontinuous_polar hT).comp (inclusion hsub)

variable [LocallyConvexSpace ℝ E]

/-- A locally convex space in whose dual every strongly bounded set is equicontinuous is
quasi-barrelled. -/
theorem QuasiBarrelledSpace.of_forall_equicontinuous
    (h : ∀ H : Set (StrongDual 𝕜 E), IsVonNBounded 𝕜 H → Equicontinuous ((↑) : H → E → 𝕜)) :
    QuasiBarrelledSpace 𝕜 E := by
  refine QuasiBarrelledSpace.of_forall_mem_nhds_zero fun T hT hTb ↦ ?_
  obtain ⟨U, hU, hTU⟩ := StrongDual.exists_mem_nhds_subset_polar
    (h _ (StrongDual.isVonNBounded_polar_of_isBornivorous hTb))
  refine mem_of_superset hU fun x hx ↦ ?_
  rw [← StrongDual.bipolar_eq_self (𝕜 := 𝕜) hT.convex hT.balanced hT.isClosed hT.nonempty]
  exact fun φ hφ ↦ hTU hφ x hx

/-- A locally convex space is quasi-barrelled if and only if every strongly bounded subset of
its dual is equicontinuous. -/
theorem quasiBarrelledSpace_iff_forall_equicontinuous :
    QuasiBarrelledSpace 𝕜 E ↔
      ∀ H : Set (StrongDual 𝕜 E), IsVonNBounded 𝕜 H → Equicontinuous ((↑) : H → E → 𝕜) :=
  ⟨fun _ _ hH ↦ QuasiBarrelledSpace.equicontinuous_of_isVonNBounded hH,
    QuasiBarrelledSpace.of_forall_equicontinuous⟩

section Bidual

/-- The canonical map of a locally convex space into its bidual is open onto its image: every
neighbourhood of zero contains the preimage of a neighbourhood of zero of the bidual. -/
theorem StrongDual.exists_nhds_preimage_inclusionInDoubleDual_subset {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) : ∃ W ∈ 𝓝 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)),
      StrongDual.inclusionInDoubleDual 𝕜 E ⁻¹' W ⊆ U := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  -- A closed, convex, balanced neighbourhood of zero inside `U`.
  obtain ⟨C, ⟨hC, hCcl⟩, hCU⟩ := (closed_nhds_basis (0 : E)).mem_iff.mp hU
  obtain ⟨V, ⟨hV, hVc, hVb⟩, hVC⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hC
  have hU' : closure V ∈ 𝓝 (0 : E) := mem_of_superset hV subset_closure
  refine ⟨StrongDual.polar 𝕜 (StrongDual.polar 𝕜 (closure V)),
    StrongDual.hasBasis_nhds_zero_polar.mem_of_mem
      (StrongDual.isVonNBounded_polar_of_mem_nhds hU'), fun x hx ↦ ?_⟩
  refine hCU (closure_minimal hVC hCcl ?_)
  change x ∈ closure V
  rw [← StrongDual.bipolar_eq_self (𝕜 := 𝕜) hVc.closure hVb.closure isClosed_closure
    ⟨0, subset_closure (mem_of_mem_nhds hV)⟩]
  exact fun φ hφ ↦ hx φ hφ

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] in
/-- The canonical map into the bidual is continuous if every strongly bounded subset of the dual
is equicontinuous. -/
theorem StrongDual.continuous_inclusionInDoubleDual_of_forall_equicontinuous
    (h : ∀ H : Set (StrongDual 𝕜 E), IsVonNBounded 𝕜 H → Equicontinuous ((↑) : H → E → 𝕜)) :
    Continuous (StrongDual.inclusionInDoubleDual 𝕜 E) := by
  let J : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) := StrongDual.inclusionInDoubleDual 𝕜 E
  refine continuous_iff_le_induced.mpr (IsTopologicalAddGroup.le_of_nhds_zero_le inferInstance
    (isTopologicalAddGroup_induced J) ?_)
  rw [nhds_induced, map_zero, ← Filter.map_le_iff_le_comap]
  intro W hW
  obtain ⟨H, hH, hHW⟩ := StrongDual.hasBasis_nhds_zero_polar.mem_iff.mp hW
  obtain ⟨U, hU, hHU⟩ := StrongDual.exists_mem_nhds_subset_polar (h H hH)
  exact mem_map.mpr (mem_of_superset hU fun x hx ↦ hHW fun φ hφ ↦ hHU hφ x hx)

omit [LocallyConvexSpace ℝ E] in
/-- The canonical map of a quasi-barrelled space into its bidual is continuous. -/
theorem QuasiBarrelledSpace.continuous_inclusionInDoubleDual [QuasiBarrelledSpace 𝕜 E] :
    Continuous (StrongDual.inclusionInDoubleDual 𝕜 E) :=
  StrongDual.continuous_inclusionInDoubleDual_of_forall_equicontinuous fun _ hH ↦
    QuasiBarrelledSpace.equicontinuous_of_isVonNBounded hH

/-- A locally convex space whose canonical map into the bidual is continuous is
quasi-barrelled. -/
theorem QuasiBarrelledSpace.of_continuous_inclusionInDoubleDual
    (h : Continuous (StrongDual.inclusionInDoubleDual 𝕜 E)) : QuasiBarrelledSpace 𝕜 E := by
  refine QuasiBarrelledSpace.of_forall_equicontinuous fun H hH ↦ ?_
  -- The polar of `H` in the bidual pulls back to a neighbourhood of zero of `E`.
  have hW : StrongDual.polar 𝕜 H ∈ 𝓝 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    StrongDual.hasBasis_nhds_zero_polar.mem_of_mem hH
  have hU : StrongDual.inclusionInDoubleDual 𝕜 E ⁻¹' StrongDual.polar 𝕜 H ∈ 𝓝 (0 : E) :=
    h.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  have hsub :
      H ⊆ StrongDual.polar 𝕜 (StrongDual.inclusionInDoubleDual 𝕜 E ⁻¹' StrongDual.polar 𝕜 H) :=
    fun φ hφ x hx ↦ hx φ hφ
  exact (StrongDual.equicontinuous_polar hU).comp (inclusion hsub)

/-- A locally convex space is **reflexive if and only if it is semi-reflexive and
quasi-barrelled**. -/
theorem reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace :
    ReflexiveSpace 𝕜 E ↔ SemiReflexiveSpace 𝕜 E ∧ QuasiBarrelledSpace 𝕜 E := by
  constructor
  · intro h
    exact ⟨h.toSemiReflexiveSpace,
      QuasiBarrelledSpace.of_continuous_inclusionInDoubleDual
        h.isInducing_inclusionInDoubleDual.continuous⟩
  · rintro ⟨hs, hq⟩
    let J : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) := StrongDual.inclusionInDoubleDual 𝕜 E
    refine { hs with isInducing_inclusionInDoubleDual := ⟨le_antisymm ?_ ?_⟩ }
    · exact continuous_iff_le_induced.mp
        (QuasiBarrelledSpace.continuous_inclusionInDoubleDual (𝕜 := 𝕜) (E := E))
    · refine IsTopologicalAddGroup.le_of_nhds_zero_le
        (isTopologicalAddGroup_induced J) inferInstance
        fun U hU ↦ ?_
      obtain ⟨W, hW, hWU⟩ :=
        StrongDual.exists_nhds_preimage_inclusionInDoubleDual_subset (𝕜 := 𝕜) hU
      rw [nhds_induced, map_zero]
      exact mem_of_superset (preimage_mem_comap hW) hWU

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
/-- In the dual of a semi-reflexive locally convex space every pointwise bounded set is strongly
bounded, by Mackey's theorem. -/
theorem SemiReflexiveSpace.isVonNBounded_of_forall_isVonNBounded [SemiReflexiveSpace 𝕜 E]
    {H : Set (StrongDual 𝕜 E)}
    (hH : ∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜 E ↦ φ x) '' H)) : IsVonNBounded 𝕜 H := by
  refine (Bornology.isVonNBounded_iff_forall_strongDual (𝕜 := 𝕜)
    (E := StrongDual 𝕜 E)).mpr fun ψ ↦ ?_
  obtain ⟨x, rfl⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := E) ψ
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).mp (hH x)
  exact ⟨C, fun φ hφ ↦ hC _ ⟨φ, hφ, rfl⟩⟩

/-- A semi-reflexive, quasi-barrelled locally convex space is barrelled. -/
theorem BarrelledSpace.of_semiReflexiveSpace_of_quasiBarrelledSpace [SemiReflexiveSpace 𝕜 E]
    [QuasiBarrelledSpace 𝕜 E] : BarrelledSpace 𝕜 E :=
  BarrelledSpace.of_forall_equicontinuous fun _ hH ↦
    QuasiBarrelledSpace.equicontinuous_of_isVonNBounded
      (SemiReflexiveSpace.isVonNBounded_of_forall_isVonNBounded hH)

/-- A locally convex space is **reflexive if and only if it is semi-reflexive and barrelled**. -/
theorem reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace :
    ReflexiveSpace 𝕜 E ↔ SemiReflexiveSpace 𝕜 E ∧ BarrelledSpace 𝕜 E := by
  rw [reflexiveSpace_iff_semiReflexiveSpace_and_quasiBarrelledSpace]
  exact ⟨fun ⟨_, _⟩ ↦ ⟨inferInstance, BarrelledSpace.of_semiReflexiveSpace_of_quasiBarrelledSpace⟩,
    fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- The strong dual of a semi-reflexive locally convex space is barrelled.
This is Schaefer–Wolff, IV §5.5, implication (a) ⇒ (c): a pointwise
bounded family in the bidual is represented by a bounded set in the original space. -/
theorem SemiReflexiveSpace.barrelledSpace_strongDual [SemiReflexiveSpace 𝕜 E] :
    BarrelledSpace 𝕜 (StrongDual 𝕜 E) := by
  refine BarrelledSpace.of_forall_equicontinuous fun H hH ↦ ?_
  let B : Set E := StrongDual.inclusionInDoubleDual 𝕜 E ⁻¹' H
  have hB : IsVonNBounded 𝕜 B := by
    refine (Bornology.isVonNBounded_iff_forall_strongDual (𝕜 := 𝕜)).mpr fun φ ↦ ?_
    obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' 𝕜).mp (hH φ)
    exact ⟨C, fun x hx ↦ hC _ ⟨StrongDual.inclusionInDoubleDual 𝕜 E x, hx, rfl⟩⟩
  have hU : StrongDual.polar 𝕜 B ∈ 𝓝 (0 : StrongDual 𝕜 E) :=
    StrongDual.hasBasis_nhds_zero_polar.mem_of_mem hB
  have hsub : H ⊆ StrongDual.polar 𝕜 (StrongDual.polar 𝕜 B) := by
    intro ψ hψ
    obtain ⟨x, rfl⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := E) ψ
    exact fun φ hφ ↦ hφ x hψ
  exact (StrongDual.equicontinuous_polar hU).comp (inclusion hsub)

/-- The strong dual of a reflexive locally convex space is reflexive, including under the
non-Hausdorff convention used here. This is Schaefer–Wolff, IV §5.6,
Corollary 1, using semi-reflexivity and barrelledness of the strong dual. -/
theorem ReflexiveSpace.strongDual [ReflexiveSpace 𝕜 E] : ReflexiveSpace 𝕜 (StrongDual 𝕜 E) := by
  apply (reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace (𝕜 := 𝕜)
    (E := StrongDual 𝕜 E)).mpr
  exact ⟨SemiReflexiveSpace.strongDual_of_continuous_inclusionInDoubleDual 𝕜 E
    (ReflexiveSpace.continuous_inclusionInDoubleDual 𝕜 E),
    SemiReflexiveSpace.barrelledSpace_strongDual⟩

end Bidual

section Montel

/-- In a Montel space, that is a space in which closed bounded sets are compact, every bounded
set lies in a weakly compact, convex, balanced set; hence a locally convex Montel space is
semi-reflexive. -/
theorem MontelSpace.semiReflexiveSpace [T2Space E] [MontelSpace 𝕜 E] : SemiReflexiveSpace 𝕜 E := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  refine SemiReflexiveSpace.of_forall_isVonNBounded 𝕜 E fun S hS ↦ ?_
  -- The closed convex balanced hull of `S` is bounded and closed, hence compact.
  let K : Set E := closure (convexHull ℝ (balancedHull 𝕜 S))
  have hKb : IsVonNBounded 𝕜 K := hS.balancedHull.convexHull.closure
  have hKc : IsCompact K :=
    MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure hKb
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hKbal : Balanced 𝕜 K := (balancedHull.balanced S).convexHull_real.closure
  refine ⟨toWeakSpace 𝕜 E '' K, ⟨?_, ?_, ?_⟩, image_mono ?_⟩
  · exact hKc.image (toWeakSpaceCLM 𝕜 E).continuous
  · exact Convex.is_linear_image (𝕜 := ℝ) (E := E) (F := WeakSpace 𝕜 E) hKconv
      ((toWeakSpace 𝕜 E).toLinearMap.restrictScalars ℝ).isLinear
  · exact Balanced.image (E := E) (F := WeakSpace 𝕜 E) hKbal (toWeakSpace 𝕜 E).toLinearMap
  · exact (subset_balancedHull 𝕜).trans ((subset_convexHull ℝ _).trans subset_closure)

/-- A barrelled locally convex Montel space is reflexive. -/
theorem MontelSpace.reflexiveSpace [T2Space E] [MontelSpace 𝕜 E] [BarrelledSpace 𝕜 E] :
    ReflexiveSpace 𝕜 E :=
  reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace.mpr
    ⟨MontelSpace.semiReflexiveSpace, inferInstance⟩

end Montel
