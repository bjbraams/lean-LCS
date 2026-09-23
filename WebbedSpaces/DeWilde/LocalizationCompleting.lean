/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import MathlibExtras.Analysis.SpecificLimits
public import WebbedSpaces.Criteria
public import WebbedSpaces.DeWilde.Localization

/-!
# The localization theorem for completing webs

For a completing web `C` of convex balanced sets, which need not be strict, the localization
theorem holds with the closures of the sets of the web
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6.(4)): for a linear map `A` with
sequentially closed graph from a first-countable Baire topological vector space `E`, or with
closed graph from a Baire topological vector space `E`, into a space with such a web there is a
strand `σ` such that every `A ⁻¹' closure (C (res σ k))` is a neighbourhood of zero in `E`.

Köthe leaves the proof to the reader. Here it follows from the cores of the localization
theorems in `WebbedSpaces.DeWilde.Localization`: with radii `c k ≤ 2⁻ᵏ⁻¹` the partial sums
of a series `∑ c (k₀ + j) • X (k₀ + j)` with `X k ∈ C (res σ (k + 1))` lie in the convex set
`C (res σ (k₀ + 1))`, so the sum lies in its closure.

## Main statements

* `IsCompletingWeb.exists_radius_forall_tendsto_mem_closure`
* `LinearMap.exists_forall_preimage_closure_res_mem_nhds_zero`: §35.6.(4) a).
* `LinearMap.exists_forall_preimage_closure_res_mem_nhds_zero_of_isClosed`: §35.6.(4) b).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6.(4)

## Tags

localization theorem, De Wilde, webbed space, completing web
-/

public section

open Set Filter PiNat

open scoped Topology Pointwise

section Series

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

/-- Along a strand `σ` of a completing web of convex symmetric sets there are radii `c k > 0`
such that for `X k ∈ C (res σ (k + 1))` every tail `∑ c (k₀ + j) • X (k₀ + j)` converges to a
point of the closure of `C (res σ (k₀ + 1))`. -/
theorem IsCompletingWeb.exists_radius_forall_tendsto_mem_closure {C : List ℕ → Set F}
    (hC : IsCompletingWeb C) (hconv : ∀ l, Convex ℝ (C l)) (hsymm : ∀ l, ∀ y ∈ C l, -y ∈ C l)
    (σ : ℕ → ℕ) :
    ∃ c : ℕ → ℝ, (∀ k, 0 < c k) ∧ ∀ X : ℕ → F, (∀ k, X k ∈ C (res σ (k + 1))) →
      ∀ k₀, ∃ y ∈ closure (C (res σ (k₀ + 1))),
        Tendsto (fun N ↦ ∑ j ∈ Finset.range N, c (k₀ + j) • X (k₀ + j)) atTop (𝓝 y) := by
  obtain ⟨ρ, hρ, hconvg⟩ := hC.exists_radius σ
  let c : ℕ → ℝ := fun k ↦ min (ρ k) ((1 / 2 : ℝ) ^ (k + 1))
  have hc (k : ℕ) : 0 < c k := lt_min (hρ k) (by positivity)
  refine ⟨c, hc, fun X hX k₀ ↦ ?_⟩
  obtain ⟨s, hs⟩ := hconvg X c hX fun k ↦ ⟨(hc k).le, min_le_left _ _⟩
  have htail := tendsto_sum_range_add_of_tendsto_sum_range hs k₀
  refine ⟨_, mem_closure_of_tendsto htail (Eventually.of_forall fun N ↦ ?_), htail⟩
  -- The partial sums lie in the convex set `C (res σ (k₀ + 1))`, which contains zero.
  have h0 : (0 : F) ∈ C (res σ (k₀ + 1)) := by
    have h := (hconv _) (hX k₀) (hsymm _ _ (hX k₀)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rwa [smul_neg, add_neg_cancel] at h
  refine (hconv _).sum_smul_mem h0 (fun j _ ↦ (hc _).le) ?_ fun j _ ↦
    hC.toIsWeb.res_antitone σ (by omega : k₀ + 1 ≤ k₀ + j + 1) (hX (k₀ + j))
  refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) (sum_half_pow_succ_le_one N)
  exact (min_le_right _ _).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))

end Series

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [BaireSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

/-- **The localization theorem for a completing web**: for a linear map `A` with sequentially
closed graph from a first-countable Baire topological vector space into a space with a
completing web `C` of convex balanced sets there is a strand `σ` such that every
`A ⁻¹' closure (C (res σ k))` is a neighbourhood of zero, Köthe II §35.6.(4) a). -/
theorem LinearMap.exists_forall_preimage_closure_res_mem_nhds_zero [FirstCountableTopology E]
    {C : List ℕ → Set F} (hC : IsCompletingWeb C) (hconv : ∀ l, Convex ℝ (C l))
    (hbal : ∀ l, Balanced 𝕜 (C l)) (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) :
    ∃ σ : ℕ → ℕ, ∀ k, A ⁻¹' closure (C (res σ k)) ∈ 𝓝 (0 : E) := by
  have : Nonempty E := ⟨0⟩
  have hsymm : ∀ l, ∀ y ∈ C l, -y ∈ C l := fun l _ hy ↦ (hbal l).neg_mem_iff.mpr hy
  obtain ⟨σ, hσ⟩ := hC.toIsWeb.exists_forall_not_isMeagre_preimage A
  obtain ⟨c, hc, H⟩ := hC.exists_radius_forall_tendsto_mem_closure hconv hsymm σ
  refine ⟨σ, fun k ↦ ?_⟩
  cases k with
  | zero =>
    rw [res_zero, hC.nil, closure_univ, preimage_univ]
    exact univ_mem
  | succ k₀ =>
    exact A.preimage_mem_nhds_zero_of_isSeqClosed_graph_of_strand hconv hsymm hA hσ hc
      (D := fun k ↦ closure (C (res σ (k + 1)))) H k₀

/-- **The localization theorem for a completing web and a closed graph**: for a linear map `A`
with closed graph from a Baire topological vector space into a space with a completing web `C`
of convex balanced sets there is a strand `σ` such that every `A ⁻¹' closure (C (res σ k))` is a
neighbourhood of zero, Köthe II §35.6.(4) b). -/
theorem LinearMap.exists_forall_preimage_closure_res_mem_nhds_zero_of_isClosed
    {C : List ℕ → Set F} (hC : IsCompletingWeb C) (hconv : ∀ l, Convex ℝ (C l))
    (hbal : ∀ l, Balanced 𝕜 (C l)) (A : E →ₗ[𝕜] F) (hA : IsClosed (A.graph : Set (E × F))) :
    ∃ σ : ℕ → ℕ, ∀ k, A ⁻¹' closure (C (res σ k)) ∈ 𝓝 (0 : E) := by
  have : Nonempty E := ⟨0⟩
  have hsymm : ∀ l, ∀ y ∈ C l, -y ∈ C l := fun l _ hy ↦ (hbal l).neg_mem_iff.mpr hy
  obtain ⟨σ, hσ⟩ := hC.toIsWeb.exists_forall_not_isMeagre_preimage A
  obtain ⟨c, hc, H⟩ := hC.exists_radius_forall_tendsto_mem_closure hconv hsymm σ
  refine ⟨σ, fun k ↦ ?_⟩
  cases k with
  | zero =>
    rw [res_zero, hC.nil, closure_univ, preimage_univ]
    exact univ_mem
  | succ k₀ =>
    exact A.preimage_mem_nhds_zero_of_isClosed_graph_of_strand hC.toIsWeb hconv hsymm hA hσ hc
      (D := fun k ↦ closure (C (res σ (k + 1)))) H k₀
