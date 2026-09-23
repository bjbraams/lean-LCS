/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.BanachDisk
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import MathlibExtras.Analysis.SpecificLimits
public import WebbedSpaces.BoundedSets
public import WebbedSpaces.Frechet
public import WebbedSpaces.Hereditary

/-!
# Criteria for completing and strict webs

Two criteria from [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.1:

* (1) a web is completing if along every strand the points of its sets, suitably scaled, lie in
  a Banach disk;
* (2) a completing web whose sets are convex, balanced and sequentially closed is strict.

As an application, a locally convex space that is the union of a sequence of Banach disks is
strictly webbed; this covers sequentially complete (DF)-spaces, Köthe II §35.4.(12).

## Main statements

* Imported from `TopologicalGroups.Series`: `tendsto_sum_range_add_of_tendsto_sum_range`: the tails
  of a convergent
  series converge.
* `IsCompletingWeb.isStrictWeb_of_isSeqClosed`: criterion (2).
* `IsWeb.isCompletingWeb_of_isBanachDisk`: criterion (1).
* `StrictlyWebbedSpace.of_iUnion_isBanachDisk`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.1.(1), (2), §35.4.(12)

## Tags

web, completing web, strict web, Banach disk
-/

public section

open Set Filter PiNat Bornology

open scoped Topology Pointwise

section Strict

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

omit [IsScalarTower ℝ 𝕜 E] in
/-- **Köthe II §35.1.(2)**: a completing web whose sets are convex, balanced and sequentially
closed is strict. -/
theorem IsCompletingWeb.isStrictWeb_of_isSeqClosed {C : List ℕ → Set E}
    (hC : IsCompletingWeb C) (hconv : ∀ l, Convex ℝ (C l)) (hbal : ∀ l, Balanced 𝕜 (C l))
    (hcl : ∀ l, IsSeqClosed (C l)) : IsStrictWeb 𝕜 C where
  toIsWeb := hC.toIsWeb
  convex := hconv
  balanced := hbal
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := hC.exists_radius σ
    refine ⟨fun k ↦ min (ρ k) ((1 / 2) ^ (k + 1)), fun k ↦ lt_min (hρ k) (by positivity),
      fun x c hx hc k₀ ↦ ?_⟩
    obtain ⟨s, hs⟩ := h x c hx fun k ↦ ⟨(hc k).1, (hc k).2.trans (min_le_left _ _)⟩
    have htail := tendsto_sum_range_add_of_tendsto_sum_range (a := fun k ↦ c k • x k) hs k₀
    refine ⟨_, hcl _ (fun N ↦ ?_) htail, htail⟩
    -- The partial sums of the tail lie in the convex set `C (res σ (k₀ + 1))`.
    have h0 : (0 : E) ∈ C (res σ (k₀ + 1)) := (hbal _).zero_mem ⟨x k₀, hx k₀⟩
    refine (hconv _).sum_smul_mem h0 (fun k _ ↦ (hc (k₀ + k)).1) ?_ fun k _ ↦
      hC.toIsWeb.res_antitone σ (by omega : k₀ + 1 ≤ k₀ + k + 1) (hx (k₀ + k))
    calc ∑ k ∈ Finset.range N, c (k₀ + k)
        ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) :=
          Finset.sum_le_sum fun k _ ↦ ((hc (k₀ + k)).2.trans (min_le_right _ _)).trans
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
      _ ≤ 1 := sum_half_pow_succ_le_one N

end Strict

section BanachDisk

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A series `∑ γ k • z k` with `z k` in a Banach disk `M` and `0 ≤ γ k ≤ (1 / 2) ^ (k + 1)`
converges. -/
theorem IsBanachDisk.exists_tendsto_sum {M : Set E} (hM : IsBanachDisk 𝕜 M) {z : ℕ → E}
    (hz : ∀ k, z k ∈ M) {γ : ℕ → ℝ} (hγ : ∀ k, 0 ≤ γ k ∧ γ k ≤ (1 / 2 : ℝ) ^ (k + 1)) :
    ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, γ k • z k) atTop (𝓝 s) := by
  have := hM.completeSpace
  -- Lift the points to the Banach space `E_M`, where the series converges absolutely.
  choose z' hz' using fun k ↦
    DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span (hz k))
  have hnorm (k : ℕ) : ‖γ k • z' k‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    have h1 : ‖z' k‖ ≤ 1 := DiskSpace.norm_le_one_of_mem_unitDisk (by
      change DiskSpace.incl 𝕜 M (z' k) ∈ diskHull 𝕜 M
      rw [hz']
      exact subset_diskHull M (hz k))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hγ k).1]
    calc γ k * ‖z' k‖ ≤ (1 / 2 : ℝ) ^ (k + 1) * 1 :=
          mul_le_mul (hγ k).2 h1 (norm_nonneg _) (by positivity)
      _ = (1 / 2 : ℝ) ^ (k + 1) := mul_one _
  have hgeom : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  obtain ⟨s', hs'⟩ := Summable.of_norm_bounded hgeom hnorm
  refine ⟨DiskSpace.incl 𝕜 M s', ?_⟩
  have hcont : Continuous (DiskSpace.incl 𝕜 M) := DiskSpace.continuous_incl hM.isVonNBounded
  refine ((hcont.tendsto s').comp hs'.tendsto_sum_nat).congr fun N ↦ ?_
  rw [Function.comp_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [LinearMap.map_smul_of_tower, hz']

/-- **Köthe II §35.1.(1)**: a web is completing if along every strand `σ` there are scalars
`μ k > 0` such that every sequence `μ k • x k`, with `x k` in the sets of the strand, lies in a
Banach disk. -/
theorem IsWeb.isCompletingWeb_of_isBanachDisk {C : List ℕ → Set E} (hC : IsWeb C)
    (h : ∀ σ : ℕ → ℕ, ∃ μ : ℕ → ℝ, (∀ k, 0 < μ k) ∧ ∀ x : ℕ → E,
      (∀ k, x k ∈ C (res σ (k + 1))) → ∃ M : Set E, IsBanachDisk 𝕜 M ∧ ∀ k, μ k • x k ∈ M) :
    IsCompletingWeb C where
  toIsWeb := hC
  exists_radius σ := by
    obtain ⟨μ, hμ, hM⟩ := h σ
    refine ⟨fun k ↦ (1 / 2 : ℝ) ^ (k + 1) * μ k, fun k ↦ mul_pos (by positivity) (hμ k),
      fun x c hx hc ↦ ?_⟩
    obtain ⟨M, hMdisk, hxM⟩ := hM x hx
    obtain ⟨s, hs⟩ := hMdisk.exists_tendsto_sum hxM (γ := fun k ↦ c k / μ k) fun k ↦
      ⟨div_nonneg (hc k).1 (hμ k).le, (div_le_iff₀ (hμ k)).mpr (hc k).2⟩
    refine ⟨s, hs.congr fun N ↦ Finset.sum_congr rfl fun k _ ↦ ?_⟩
    rw [smul_smul, div_mul_cancel₀ _ (hμ k).ne']

/-- A locally convex space that is the union of a sequence of Banach disks is strictly webbed.
In particular a sequentially complete (DF)-space is strictly webbed, Köthe II §35.4.(12). -/
theorem StrictlyWebbedSpace.of_iUnion_isBanachDisk {K : ℕ → Set E} (hK : ⋃ n, K n = univ)
    (h : ∀ n, IsBanachDisk 𝕜 (K n)) : StrictlyWebbedSpace 𝕜 E := by
  have : ∀ n, CompleteSpace (DiskSpace 𝕜 (K n)) := fun n ↦ (h n).completeSpace
  refine StrictlyWebbedSpace.of_iUnion_range (fun n ↦ DiskSpace.incl 𝕜 (K n))
    (fun n ↦ (DiskSpace.continuous_incl (h n).isVonNBounded).seqContinuous) ?_
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hK ▸ mem_univ y)
  obtain ⟨y', hy'⟩ := DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span hn)
  exact mem_iUnion.mpr ⟨n, y', hy'⟩

end BanachDisk
