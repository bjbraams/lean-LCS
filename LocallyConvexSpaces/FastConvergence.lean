/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.UltrabornologicalCompactDisk

/-!
# Fast convergence and ultrabornological spaces

A sequence `x` in a locally convex space `E` is **fast convergent to zero** (De Wilde) if there
is a compact disk `K` of `E` such that `x` tends to zero in the gauge-seminormed space `E_K`
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7). Equivalently, `x n ∈ c n • K`
for a compact disk `K` and numbers `c n > 0` that tend to zero; this is the form used in the
proofs. By §35.7.(4) and the remark after it, the compact disks may be replaced by Banach disks,
and in a Fréchet space every sequence that tends to zero is fast convergent to zero.

The main results are the characterization of ultrabornological spaces by fast convergent
sequences, §35.7.(3): a Hausdorff locally convex space is ultrabornological if and only if
every convex balanced set that absorbs the fast convergent null sequences is a neighbourhood of
zero; and §35.7.(6): a linear map from an ultrabornological space into a locally convex space is
continuous if it maps fast convergent null sequences to bounded sequences.

## Main definitions

* `Bornology.IsFastNullSeq 𝕜 x`, `Bornology.IsFastConvergent 𝕜 x x₀`.

## Main statements

* `Bornology.isFastNullSeq_iff_exists_smul`
* `Bornology.IsBanachDisk.isFastNullSeq_of_tendsto_zero`,
  `Bornology.isFastNullSeq_iff_exists_isBanachDisk`: the remark after §35.7.(4).
* `Bornology.isFastNullSeq_of_tendsto_zero`, `Bornology.IsFastNullSeq.exists_tendsto_atTop_smul`:
  §35.7.(4).
* `UltrabornologicalSpace.mem_nhds_zero_of_forall_absorbs_isFastNullSeq`,
  `UltrabornologicalSpace.of_forall_absorbs_isFastNullSeq`: §35.7.(3).
* `LinearMap.continuous_of_forall_isVonNBounded_range_isFastNullSeq`: §35.7.(5) c) and (6) b).
* `Bornology.IsFastNullSeq.map`: §35.7.(6) a).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.7

## Tags

fast convergence, ultrabornological space, Banach disk, compact disk
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

universe u v

variable (𝕜 : Type v) {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- A sequence `x` is **fast convergent to zero** if there is a compact disk `K` such that `x`
tends to zero in the gauge-seminormed space `E_K` spanned by `K`. -/
@[expose]
def Bornology.IsFastNullSeq [TopologicalSpace E] (x : ℕ → E) : Prop :=
  ∃ K ∈ compactDisks 𝕜 E, ∃ y : ℕ → DiskSpace 𝕜 K,
    (∀ n, DiskSpace.incl 𝕜 K (y n) = x n) ∧ Tendsto y atTop (𝓝 0)

/-- A sequence `x` is **fast convergent** to `x₀` if `x - x₀` is fast convergent to zero. -/
@[expose]
def Bornology.IsFastConvergent [TopologicalSpace E] (x : ℕ → E) (x₀ : E) : Prop :=
  IsFastNullSeq 𝕜 fun n ↦ x n - x₀

variable {𝕜}

section Basic

variable [TopologicalSpace E]

/-- A sequence is fast convergent to zero if and only if `x n ∈ c n • K` for a compact disk `K`
and positive numbers `c n` that tend to zero. -/
theorem Bornology.isFastNullSeq_iff_exists_smul {x : ℕ → E} :
    IsFastNullSeq 𝕜 x ↔ ∃ K ∈ compactDisks 𝕜 E, ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
      Tendsto c atTop (𝓝 0) ∧ ∀ n, x n ∈ c n • K := by
  constructor
  · rintro ⟨K, hK, y, hyx, hy⟩
    have hhull : diskHull 𝕜 K = K := diskHull_eq_self hK.2.1 hK.2.2.1 hK.2.2.2
    have hc (n : ℕ) : 0 < ‖y n‖ + 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨K, hK, fun n ↦ ‖y n‖ + 1 / ((n : ℝ) + 1), hc, ?_, fun n ↦ ?_⟩
    · have h := hy.norm.add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h
    · have h := DiskSpace.incl_mem_smul_diskHull (hc n)
        (lt_add_of_pos_right ‖y n‖ (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
      rwa [hhull, hyx] at h
  · rintro ⟨K, hK, c, hc, hc0, hx⟩
    have hspan (n : ℕ) : x n ∈ Submodule.span 𝕜 K := by
      obtain ⟨k, hk, hkx⟩ := hx n
      have hkx' : c n • k = x n := hkx
      rw [← hkx']
      exact Submodule.smul_of_tower_mem _ (c n) (Submodule.subset_span hk)
    choose y hy using fun n ↦ DiskSpace.exists_incl_eq (𝕜 := 𝕜) (hspan n)
    refine ⟨K, hK, y, hy, squeeze_zero_norm (fun n ↦ ?_) hc0⟩
    refine DiskSpace.norm_le_of_incl_mem_smul_diskHull (hc n).le ?_
    rw [hy]
    exact smul_set_mono (subset_diskHull K) (hx n)

/-- The multiples of a vector by the scalars of norm at most one form a compact disk. -/
theorem Bornology.image_toSpanSingleton_closedBall_mem_compactDisks [ContinuousSMul 𝕜 E] (v : E) :
    LinearMap.toSpanSingleton 𝕜 E v '' Metric.closedBall (0 : 𝕜) 1 ∈ compactDisks 𝕜 E := by
  refine ⟨(isCompact_closedBall (0 : 𝕜) 1).image ?_,
    (LinearMap.toSpanSingleton 𝕜 E v).convex_image_closedBall,
    (LinearMap.toSpanSingleton 𝕜 E v).balanced_image_closedBall,
    ⟨_, 0, Metric.mem_closedBall_self zero_le_one, rfl⟩⟩
  have h : Continuous fun a : 𝕜 ↦ a • v := continuous_id.smul continuous_const
  exact h

/-- The sequence `v, 0, 0, …` is fast convergent to zero. -/
theorem Bornology.isFastNullSeq_single [ContinuousSMul 𝕜 E] (v : E) :
    IsFastNullSeq 𝕜 fun n : ℕ ↦ if n = 0 then v else 0 := by
  refine isFastNullSeq_iff_exists_smul.mpr ⟨_, image_toSpanSingleton_closedBall_mem_compactDisks v,
    fun n ↦ 1 / ((n : ℝ) + 1), fun n ↦ by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    refine ⟨v, ⟨1, by simp, by simp⟩, ?_⟩
    simp
  · refine ⟨0, ⟨0, Metric.mem_closedBall_self zero_le_one, by simp⟩, ?_⟩
    simp [hn]

end Basic

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A sequence that is fast convergent to zero tends to zero. -/
theorem Bornology.IsFastNullSeq.tendsto_zero {x : ℕ → E} (hx : IsFastNullSeq 𝕜 x) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨K, hK, y, hyx, hy⟩ := hx
  have h := ((DiskSpace.continuous_incl (hK.1.isVonNBounded 𝕜)).tendsto 0).comp hy
  rw [map_zero] at h
  exact h.congr hyx

/-- A sequence that tends to zero in the Banach space `E_B` of a Banach disk `B` is fast
convergent to zero, Köthe II §35.7, the remark after (4). -/
theorem Bornology.IsBanachDisk.isFastNullSeq_of_tendsto_zero {B : Set E} (hB : IsBanachDisk 𝕜 B)
    {y : ℕ → DiskSpace 𝕜 B} (hy : Tendsto y atTop (𝓝 0)) :
    IsFastNullSeq 𝕜 fun n ↦ DiskSpace.incl 𝕜 B (y n) := by
  obtain ⟨ρ, hρ1, hρ, hz⟩ := exists_tendsto_atTop_tendsto_smul_zero hy
  obtain ⟨K, hK, hzK⟩ := hB.exists_mem_compactDisks_of_tendsto_zero hz
  have hρpos (n : ℕ) : 0 < ρ n := lt_of_lt_of_le one_pos (hρ1 n)
  refine isFastNullSeq_iff_exists_smul.mpr ⟨K, hK, fun n ↦ (ρ n)⁻¹,
    fun n ↦ inv_pos.mpr (hρpos n), tendsto_inv_atTop_zero.comp hρ, fun n ↦ ?_⟩
  refine ⟨_, hzK n, ?_⟩
  change (ρ n)⁻¹ • DiskSpace.incl 𝕜 B (ρ n • y n) = DiskSpace.incl 𝕜 B (y n)
  rw [LinearMap.map_smul_of_tower, inv_smul_smul₀ (hρpos n).ne']

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] in
/-- If `x` is fast convergent to zero then there are `ρ n → ∞` such that `ρ n • x n` is fast
convergent to zero, Köthe II §35.7.(4). -/
theorem Bornology.IsFastNullSeq.exists_tendsto_atTop_smul {x : ℕ → E} (hx : IsFastNullSeq 𝕜 x) :
    ∃ ρ : ℕ → ℝ, (∀ n, 1 ≤ ρ n) ∧ Tendsto ρ atTop atTop ∧
      IsFastNullSeq 𝕜 fun n ↦ ρ n • x n := by
  obtain ⟨K, hK, y, hyx, hy⟩ := hx
  obtain ⟨ρ, hρ1, hρ, hz⟩ := exists_tendsto_atTop_tendsto_smul_zero hy
  exact ⟨ρ, hρ1, hρ, K, hK, fun n ↦ ρ n • y n,
    fun n ↦ by rw [LinearMap.map_smul_of_tower, hyx], hz⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] in
/-- The image of a fast convergent null sequence under a continuous linear map is a fast
convergent null sequence, Köthe II §35.7.(6) a). -/
theorem Bornology.IsFastNullSeq.map {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] {x : ℕ → E} (hx : IsFastNullSeq 𝕜 x)
    (A : E →L[𝕜] F) : IsFastNullSeq 𝕜 fun n ↦ A (x n) := by
  obtain ⟨K, hK, c, hc, hc0, hxK⟩ := isFastNullSeq_iff_exists_smul.mp hx
  refine isFastNullSeq_iff_exists_smul.mpr ⟨A '' K, ⟨hK.1.image A.continuous,
    hK.2.1.is_linear_image (A.toLinearMap.restrictScalars ℝ).isLinear,
    hK.2.2.1.image A.toLinearMap, hK.2.2.2.image A⟩, c, hc, hc0, fun n ↦ ?_⟩
  obtain ⟨k, hk, hkx⟩ := hxK n
  have hkx' : c n • k = x n := hkx
  exact ⟨A k, ⟨k, hk, rfl⟩, by rw [← hkx']; exact (A.map_smul_of_tower (c n) k).symm⟩

end Topology

section Frechet

variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- A sequence is fast convergent to zero if and only if it tends to zero in the Banach space
`E_B` of some Banach disk `B`, Köthe II §35.7, the remark after (4). -/
theorem Bornology.isFastNullSeq_iff_exists_isBanachDisk [T2Space E] {x : ℕ → E} :
    IsFastNullSeq 𝕜 x ↔ ∃ B : Set E, IsBanachDisk 𝕜 B ∧ ∃ y : ℕ → DiskSpace 𝕜 B,
      (∀ n, DiskSpace.incl 𝕜 B (y n) = x n) ∧ Tendsto y atTop (𝓝 0) := by
  constructor
  · rintro ⟨K, hK, y, hyx, hy⟩
    exact ⟨K, IsBanachDisk.of_isCompact hK.1 hK.2.1 hK.2.2.1 hK.2.2.2, y, hyx, hy⟩
  · rintro ⟨B, hB, y, hyx, hy⟩
    have h := hB.isFastNullSeq_of_tendsto_zero hy
    rwa [funext hyx] at h

/-- **In a Fréchet space every sequence that tends to zero is fast convergent to zero**,
Köthe II §35.7.(4). -/
theorem Bornology.isFastNullSeq_of_tendsto_zero [CompleteSpace E] [FirstCountableTopology E]
    {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) : IsFastNullSeq 𝕜 x := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨ρ, hρ1, hρ, hz⟩ := exists_tendsto_atTop_tendsto_smul_zero hx
  obtain ⟨K, hzK, hKc, hKconv, hKbal, hK0⟩ :=
    (hz.isCompact_insert_range).exists_isCompact_convex_balanced_superset (𝕜 := 𝕜)
  have hρpos (n : ℕ) : 0 < ρ n := lt_of_lt_of_le one_pos (hρ1 n)
  refine isFastNullSeq_iff_exists_smul.mpr ⟨K, ⟨hKc, hKconv, hKbal, ⟨0, hK0⟩⟩,
    fun n ↦ (ρ n)⁻¹, fun n ↦ inv_pos.mpr (hρpos n), tendsto_inv_atTop_zero.comp hρ, fun n ↦ ?_⟩
  exact ⟨ρ n • x n, hzK (mem_insert_of_mem _ (mem_range_self n)),
    inv_smul_smul₀ (hρpos n).ne' (x n)⟩

end Frechet

section Ultrabornological

/-- **In an ultrabornological space a convex balanced set that absorbs the fast convergent null
sequences is a neighbourhood of zero**, Köthe II §35.7.(3). -/
theorem UltrabornologicalSpace.mem_nhds_zero_of_forall_absorbs_isFastNullSeq
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    [UltrabornologicalSpace 𝕜 E] {M : Set E} (hc : Convex ℝ M)
    (hb : Balanced 𝕜 M) (h : ∀ x : ℕ → E, IsFastNullSeq 𝕜 x → Absorbs 𝕜 M (range x)) :
    M ∈ 𝓝 (0 : E) := by
  have heq := UltrabornologicalSpace.eq_locallyConvexFinalTopology_compactDisks (𝕜 := 𝕜) (E := E)
  let g := fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
  have habs : Absorbent 𝕜 M := fun v ↦
    (h _ (isFastNullSeq_single v)).mono_right (singleton_subset_iff.mpr ⟨0, by simp⟩)
  have hM := locallyConvexFinalTopology.mem_nhds_zero g hc hb habs fun K ↦ ?_
  · rwa [← heq] at hM
  refine mem_nhds_zero_of_forall_absorbs_range (𝕜 := 𝕜) fun y hy ↦ ?_
  have hfast : IsFastNullSeq 𝕜 fun n ↦ DiskSpace.incl 𝕜 K.1 (y n) :=
    ⟨K.1, K.2, y, fun _ ↦ rfl, hy⟩
  have habs' := h _ hfast
  rw [show (range fun n ↦ DiskSpace.incl 𝕜 K.1 (y n)) = DiskSpace.incl 𝕜 K.1 '' range y from
    range_comp _ _] at habs'
  exact habs'.preimage_linearMap

/-- **A Hausdorff locally convex space in which every convex balanced set that absorbs the fast
convergent null sequences is a neighbourhood of zero is ultrabornological**,
Köthe II §35.7.(3). -/
theorem UltrabornologicalSpace.of_forall_absorbs_isFastNullSeq [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    (h : ∀ M : Set E, Convex ℝ M → Balanced 𝕜 M →
      (∀ x : ℕ → E, IsFastNullSeq 𝕜 x → Absorbs 𝕜 M (range x)) → M ∈ 𝓝 (0 : E)) :
    UltrabornologicalSpace 𝕜 E := by
  let g := fun K : compactDisks 𝕜 E ↦ DiskSpace.incl 𝕜 K.1
  refine UltrabornologicalSpace.of_eq_locallyConvexFinalTopology_compactDisks
    (le_antisymm ?_ ((locallyConvexFinalTopology.le_iff g).mpr fun K ↦
      DiskSpace.continuous_incl (K.2.1.isVonNBounded 𝕜)))
  refine IsTopologicalAddGroup.le_of_nhds_zero_le inferInstance
    (locallyConvexFinalTopology.isTopologicalAddGroup g) fun U hU ↦ ?_
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ :=
    (@nhds_zero_hasBasis_convex_balanced 𝕜 E _ _ _ _ _ (locallyConvexFinalTopology g)
      (locallyConvexFinalTopology.continuousSMul g)
      (locallyConvexFinalTopology.locallyConvexSpace g)).mem_iff.mp hU
  refine mem_of_superset (h W hWc hWb ?_) hWU
  rintro x ⟨K, hK, y, hyx, hy⟩
  -- The trace of `W` on `E_K` is a neighbourhood of zero, so it absorbs the bounded set `y`.
  have hpre : DiskSpace.incl 𝕜 K ⁻¹' W ∈ 𝓝 (0 : DiskSpace 𝕜 K) :=
    locallyConvexFinalTopology.preimage_mem_nhds_zero g ⟨K, hK⟩ hW
  have h1 : Absorbs 𝕜 (DiskSpace.incl 𝕜 K ⁻¹' W) (range y) := hy.isVonNBounded_range 𝕜 hpre
  have h2 := (h1.image_linearMap (DiskSpace.incl 𝕜 K)).mono_left (image_preimage_subset _ W)
  rwa [← range_comp, show DiskSpace.incl 𝕜 K ∘ y = x from funext hyx] at h2

/-- **A linear map from an ultrabornological space into a locally convex space that maps fast
convergent null sequences to bounded sequences is continuous**, Köthe II §35.7.(6) b); for
linear functionals this is §35.7.(5) c). -/
theorem LinearMap.continuous_of_forall_isVonNBounded_range_isFastNullSeq [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    [UltrabornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] (A : E →ₗ[𝕜] F)
    (hA : ∀ x : ℕ → E, IsFastNullSeq 𝕜 x → IsVonNBounded 𝕜 (Set.range fun n ↦ A (x n))) :
    Continuous A := by
  refine continuous_of_continuousAt_zero A ?_
  rw [ContinuousAt, map_zero]
  intro V hV
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWV⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  refine mem_of_superset ?_ (preimage_mono hWV)
  refine UltrabornologicalSpace.mem_nhds_zero_of_forall_absorbs_isFastNullSeq
    (hWc.is_linear_preimage (A.restrictScalars ℝ).isLinear) (hWb.preimage A) fun x hx ↦ ?_
  have h1 : Absorbs 𝕜 W (A '' Set.range x) := by
    rw [← Set.range_comp]
    exact hA x hx hW
  exact h1.preimage_linearMap

end Ultrabornological
