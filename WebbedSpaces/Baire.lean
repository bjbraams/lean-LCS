/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import TopologicalGroups.Basic
public import WebbedSpaces.DeWilde.Localization

/-!
# A strictly webbed Baire space is a Fréchet space

Let `E` be a Hausdorff topological vector space that is strictly webbed and a Baire space. The
localization theorem, applied to the identity map of `E`, gives a strand `σ` of a strict web `C`
all of whose sets `C (res σ k)` are neighbourhoods of zero. By Köthe II §35.1.(3) the multiples
`ρ k • C (res σ (k + 1))` then form a countable basis of neighbourhoods of zero, so `E` is
first-countable, and the strictness of the web makes every Cauchy sequence converge, so `E` is
complete ([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6.(3)).

For a space that is only webbed, the closures `S k` of the sets of a strand without meagre sets
have interior points, so that the sets `ρ k • (S k - S k)` form a countable basis of
neighbourhoods of zero: a webbed Baire space is first-countable, and metrizable when it is
Hausdorff (§35.6.(5)).

Consequently a product of Banach spaces with uncountably many nontrivial factors, which is a
Baire space but is not metrizable, is not webbed.

## Main statements

* `StrictlyWebbedSpace.exists_hasBasis_nhds_zero_of_baireSpace`
* `StrictlyWebbedSpace.firstCountableTopology_of_baireSpace`
* `StrictlyWebbedSpace.completeSpace_of_baireSpace`
* `WebbedSpace.firstCountableTopology_of_baireSpace`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6.(3), (5)

## Tags

webbed space, Baire space, Fréchet space
-/

public section

open Set Filter PiNat

open scoped Topology Pointwise Uniformity

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E]

namespace StrictlyWebbedSpace

/-- In a Hausdorff strictly webbed Baire space there are a family of balanced sets `C`, a sequence
`σ` and real coefficients `ρ` such that the sets `ρ k • C (res σ (k + 1))` form a basis of
neighbourhoods of zero and the series `∑ ρ k • x k` with `x k ∈ C (res σ (k + 1))` converge. -/
theorem exists_hasBasis_nhds_zero_of_baireSpace [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] [BaireSpace E] [StrictlyWebbedSpace 𝕜 E] :
    ∃ (C : List ℕ → Set E) (σ : ℕ → ℕ) (ρ : ℕ → ℝ), (∀ l, Balanced 𝕜 (C l)) ∧
      (𝓝 (0 : E)).HasBasis (fun _ : ℕ ↦ True) (fun k ↦ ρ k • C (res σ (k + 1))) ∧
      ∀ x : ℕ → E, (∀ k, x k ∈ C (res σ (k + 1))) →
        ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, ρ k • x k) atTop (𝓝 s) := by
  obtain ⟨C, hC⟩ := StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := E)
  -- The identity map has a closed graph.
  have hid : IsClosed ((LinearMap.id : E →ₗ[𝕜] E).graph : Set (E × E)) :=
    (ContinuousLinearMap.id 𝕜 E).isClosed_graph
  obtain ⟨σ, hσ⟩ :=
    (LinearMap.id : E →ₗ[𝕜] E).exists_forall_preimage_res_mem_nhds_zero_of_isClosed hC hid
  obtain ⟨ρ, hρ, hstrict⟩ := hC.exists_radius σ
  have hseries (x : ℕ → E) (hx : ∀ k, x k ∈ C (res σ (k + 1))) :
      ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, ρ k • x k) atTop (𝓝 s) := by
    obtain ⟨s, -, hs⟩ := hstrict x ρ hx (fun k ↦ ⟨(hρ k).le, le_rfl⟩) 0
    exact ⟨s, by simpa using hs⟩
  refine ⟨C, σ, ρ, hC.balanced, ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨k, _, hk⟩ ↦ ?_⟩⟩, hseries⟩
  · obtain ⟨K, hK⟩ := hC.toIsWeb.exists_forall_smul_subset_of_tendsto hseries hU
    exact ⟨K, trivial, hK K le_rfl⟩
  · have h := hσ (k + 1)
    rw [LinearMap.id_coe, preimage_id] at h
    exact mem_of_superset ((set_smul_mem_nhds_zero_iff (hρ k).ne').mpr h) hk

/-- A Hausdorff strictly webbed Baire space is first-countable. -/
theorem firstCountableTopology_of_baireSpace [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [BaireSpace E]
    [StrictlyWebbedSpace 𝕜 E] : FirstCountableTopology E := by
  obtain ⟨C, σ, ρ, -, hbasis, -⟩ := exists_hasBasis_nhds_zero_of_baireSpace (𝕜 := 𝕜) (E := E)
  exact IsTopologicalAddGroup.firstCountableTopology_of_isCountablyGenerated_nhds_zero
    hbasis.isCountablyGenerated

/-- **A Hausdorff strictly webbed Baire space is complete**; together with
`firstCountableTopology_of_baireSpace` it is a Fréchet space if it is locally convex,
Köthe II §35.6.(3). -/
theorem completeSpace_of_baireSpace [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [BaireSpace E] [StrictlyWebbedSpace 𝕜 E] : CompleteSpace E := by
  obtain ⟨C, σ, ρ, hbal, hbasis, hseries⟩ :=
    exists_hasBasis_nhds_zero_of_baireSpace (𝕜 := 𝕜) (E := E)
  have : (𝓝 (0 : E)).IsCountablyGenerated := hbasis.isCountablyGenerated
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- A subsequence with increments in the sets of the basis.
  have hV (k : ℕ) : {p : E × E | p.2 - p.1 ∈ ρ k • C (res σ (k + 1))} ∈ 𝓤 E := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact preimage_mem_comap (hbasis.mem_of_mem trivial)
  obtain ⟨φ, hφ, hφV⟩ := hu.subseq_mem hV
  -- The increments are `ρ k • y k` with `y k` in the sets of the strand.
  have hy (k : ℕ) : ∃ y ∈ C (res σ (k + 1)), ρ k • y = u (φ (k + 1)) - u (φ k) := by
    obtain ⟨y, hy, hye⟩ := hφV k
    have hye' : ρ k • y = u (φ k) - u (φ (k + 1)) := hye
    exact ⟨-y, (hbal _).neg_mem_iff.mpr hy, by rw [smul_neg, hye', neg_sub]⟩
  choose y hyC hye using hy
  obtain ⟨s, hs⟩ := hseries y hyC
  -- The partial sums telescope.
  have hsum (N : ℕ) : ∑ k ∈ Finset.range N, ρ k • y k = u (φ N) - u (φ 0) := by
    simp_rw [hye]
    exact Finset.sum_range_sub (fun k ↦ u (φ k)) N
  have hlim : Tendsto (u ∘ φ) atTop (𝓝 (s + u (φ 0))) := by
    refine (hs.add_const (u (φ 0))).congr fun N ↦ ?_
    rw [hsum, sub_add_cancel]
    rfl
  exact ⟨_, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hlim⟩

end StrictlyWebbedSpace

section Webbed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [BaireSpace E] [WebbedSpace E]

/-- **A webbed Baire space is first-countable**, so it is metrizable if it is Hausdorff,
Köthe II §35.6.(5). Along a strand `σ` of a completing web `C` with no meagre set, the sets
`ρ k • (S k - S k)` with `S k` the closure of `C (res σ (k + 1))` form a basis of neighbourhoods
of zero. -/
theorem WebbedSpace.firstCountableTopology_of_baireSpace : FirstCountableTopology E := by
  have : Nonempty E := ⟨0⟩
  obtain ⟨C, hC⟩ := WebbedSpace.exists_isCompletingWeb (E := E)
  obtain ⟨σ, hσ⟩ := exists_forall_not_isMeagre_res (T := C)
    (by rw [hC.nil]; exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty)
    fun l ↦ (hC.iUnion_cons l).ge
  obtain ⟨ρ, hρ, -, hsmall⟩ := hC.exists_forall_smul_subset σ
  let S : ℕ → Set E := fun k ↦ closure (C (res σ (k + 1)))
  let B : ℕ → Set E := fun k ↦ (fun p : E × E ↦ ρ k • (p.1 - p.2)) '' S k ×ˢ S k
  -- The closure of a non-meagre set has an interior point `y`, and `S k - y ⊆ S k - S k`.
  have hB (k : ℕ) : B k ∈ 𝓝 (0 : E) := by
    have hne : (interior (S k)).Nonempty := by
      by_contra h
      exact hσ (k + 1) (IsNowhereDense.isMeagre (not_nonempty_iff_eq_empty.mp h))
    obtain ⟨y, hy⟩ := hne
    have hSy : S k ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hy
    have hc : ContinuousAt (fun v : E ↦ v + y) 0 := by fun_prop
    have hV : (fun v : E ↦ v + y) ⁻¹' S k ∈ 𝓝 (0 : E) :=
      hc.preimage_mem_nhds (by simpa using hSy)
    have hsub : ρ k • ((fun v : E ↦ v + y) ⁻¹' S k) ⊆ B k := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨(v + y, y), ⟨hv, mem_of_mem_nhds hSy⟩, by simp⟩
    exact mem_of_superset ((set_smul_mem_nhds_zero_iff (hρ k).ne').mpr hV) hsub
  refine IsTopologicalAddGroup.firstCountableTopology_of_isCountablyGenerated_nhds_zero ?_
  refine Filter.HasBasis.isCountablyGenerated (p := fun _ : ℕ ↦ True) (s := B)
    ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨k, _, hk⟩ ↦ mem_of_superset (hB k) hk⟩⟩
  -- A closed neighbourhood `U'` of zero with `U' - U' ⊆ U`.
  have hsubc : Tendsto (fun p : E × E ↦ p.1 - p.2) (𝓝 ((0 : E), (0 : E))) (𝓝 0) := by
    have h := (continuous_sub (G := E)).tendsto ((0 : E), (0 : E))
    rwa [sub_zero] at h
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := mem_nhds_prod_iff.mp (hsubc hU)
  obtain ⟨U', ⟨hU', hU'cl⟩, hU'sub⟩ :=
    (closed_nhds_basis (0 : E)).mem_iff.mp (inter_mem hV₁ hV₂)
  obtain ⟨K, hK⟩ := hsmall U' hU'
  refine ⟨K, trivial, ?_⟩
  have hcl : ρ K • S K ⊆ U' := by
    rintro _ ⟨a, ha, rfl⟩
    exact hU'cl.closure_subset_iff.mpr (hK K le_rfl)
      (map_mem_closure (continuous_const_smul (ρ K)) ha fun w hw ↦ smul_mem_smul_set hw)
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  have h1 : ρ K • a ∈ V₁ := (hU'sub (hcl (smul_mem_smul_set ha))).1
  have h2 : ρ K • b ∈ V₂ := (hU'sub (hcl (smul_mem_smul_set hb))).2
  have h := hV12 (show (ρ K • a, ρ K • b) ∈ V₁ ×ˢ V₂ from ⟨h1, h2⟩)
  simpa [smul_sub] using h

end Webbed
