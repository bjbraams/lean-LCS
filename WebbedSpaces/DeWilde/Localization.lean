/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.BanachDisk
public import WebbedSpaces.DeWilde.ClosedGraph
public import WebbedSpaces.Hereditary

/-!
# De Wilde's localization theorem

Let `A` be a linear map with sequentially closed graph from a first-countable Baire topological
vector space `E`, for instance a Fréchet space, into a space `F` with a strict web `C`. Then
there is a strand `σ` of the web such that every `A ⁻¹' C (res σ k)` is a neighbourhood of zero
in `E` ([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6.(1) a)). Hence the image of
a bounded set is absorbed by every set of the strand.

An application is Grothendieck's factorization theorem: if `F` is the union of countably many
images `f n (X n)` of strictly webbed spaces under sequentially continuous linear maps, in
particular if `F` is an LF space, then `A` maps `E` into one of the `f n (X n)`; and if `f n` is
injective and `X n` is locally convex, then `A` factors through a continuous linear map
`E → X n`.

## Main statements

* `LinearMap.exists_forall_preimage_res_mem_nhds_zero`: the localization theorem.
* `LinearMap.exists_forall_image_subset_smul_res`: the images of bounded sets.
* `LinearMap.exists_range_le_range_of_isSeqClosed_graph`,
  `LinearMap.exists_continuousLinearMap_comp_eq_of_isSeqClosed_graph`: Grothendieck's
  factorization theorem.
* `LinearMap.exists_forall_image_banachDisk_subset_smul_res`,
  `IsStrictWeb.exists_forall_banachDisk_subset_smul_res`: the localization theorem for Banach
  disks, §35.6.(2).
* `LinearMap.exists_forall_preimage_res_mem_nhds_zero_of_isClosed`: the localization theorem for
  a map with closed graph on a Baire space, without countability assumptions, §35.6.(1) b).
* `LinearPMap.exists_forall_image_preimage_res_mem_nhds_zero_of_isClosed`: the same for a map
  that is defined on a non-meagre subspace.
* `LinearMap.preimage_mem_nhds_zero_of_isSeqClosed_graph_of_strand`,
  `LinearMap.preimage_mem_nhds_zero_of_isClosed_graph_of_strand`: the cores of the proofs, which
  also serve for completing webs in `WebbedSpaces.DeWilde.LocalizationCompleting`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.6, and §19.5.(4) for
  Grothendieck's theorem

## Tags

localization theorem, De Wilde, webbed space, Grothendieck factorization theorem, LF space
-/

public section

open Set Filter PiNat Function

open scoped Topology Pointwise

section Core

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- If the preimage under a linear map of a convex symmetric set is not meagre, then the closure
of every positive multiple of the preimage is a neighbourhood of zero. -/
private theorem LinearMap.closure_smul_preimage_mem_nhds_zero [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (A : E →ₗ[𝕜] F) {S : Set F} (hconv : Convex ℝ S)
    (hsymm : ∀ y ∈ S, -y ∈ S) (hS : ¬IsMeagre (A ⁻¹' S)) {c : ℝ} (hc : 0 < c) :
    closure (c • (A ⁻¹' S)) ∈ 𝓝 (0 : E) := by
  have hcl := closure_mem_nhds_zero_of_not_isMeagre
    (hconv.is_linear_preimage (A.restrictScalars ℝ).isLinear)
    (fun x hx ↦ by
      rw [mem_preimage, map_neg]
      exact hsymm _ hx) hS
  have hsc := (set_smul_mem_nhds_zero_iff hc.ne').mpr hcl
  refine mem_of_superset hsc ?_
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_closure (continuous_const_smul c) hx fun w hw ↦ ⟨w, hw, rfl⟩

/-- The step that the two cores of the localization theorems have in common. Let `σ` be a strand
such that no `A ⁻¹' C (res σ k)` is meagre, and let the series `∑ c (k₀ + j) • X (k₀ + j)`
converge to a point of `D k₀` for all `X k ∈ C (res σ (k + 1))`. Then for points
`x j ∈ c (k₀ + j) • A ⁻¹' C (res σ (k₀ + j + 1))` the images under `A` of the partial sums of
`∑ x j` converge to a point of `D k₀`. -/
private theorem LinearMap.exists_tendsto_map_sum_of_strand [TopologicalSpace F]
    {C : List ℕ → Set F} (A : E →ₗ[𝕜] F) {σ : ℕ → ℕ}
    (hσ : ∀ k, ¬IsMeagre (A ⁻¹' C (res σ k))) {c : ℕ → ℝ} {D : ℕ → Set F}
    (H : ∀ X : ℕ → F, (∀ k, X k ∈ C (res σ (k + 1))) → ∀ k₀, ∃ y ∈ D k₀,
      Tendsto (fun N ↦ ∑ j ∈ Finset.range N, c (k₀ + j) • X (k₀ + j)) atTop (𝓝 y)) (k₀ : ℕ)
    {x : ℕ → E} (hx : ∀ j, x j ∈ c (k₀ + j) • (A ⁻¹' C (res σ (k₀ + j + 1)))) :
    ∃ y ∈ D k₀, Tendsto (fun N ↦ A (∑ j ∈ Finset.range N, x j)) atTop (𝓝 y) := by
  -- Every set of the strand is nonempty.
  have hne (k : ℕ) : (C (res σ (k + 1))).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    refine hσ (k + 1) ?_
    rw [hcon, preimage_empty]
    exact IsMeagre.empty
  have hw (j : ℕ) : ∃ w, A w ∈ C (res σ (k₀ + j + 1)) ∧ c (k₀ + j) • w = x j := by
    obtain ⟨w, hw, hwx⟩ := hx j
    exact ⟨w, hw, hwx⟩
  choose w hwC hwx using hw
  -- A sequence along the whole strand that agrees with `A (w j)` from index `k₀` on.
  obtain ⟨X, hX, hXk₀⟩ := Set.exists_seq_forall_mem_forall_add_eq
    (S := fun k ↦ C (res σ (k + 1))) (k₀ := k₀) (fun k _ ↦ hne k) (Y := fun j ↦ A (w j)) hwC
  obtain ⟨y, hyD, hy⟩ := H X hX k₀
  refine ⟨y, hyD, hy.congr fun N ↦ ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hXk₀, ← hwx j, A.map_smul_of_tower]

end Core

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [BaireSpace E] [FirstCountableTopology E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]

omit [BaireSpace E] in
/-- The core of the localization theorems for a sequentially closed graph. Let `A` be a linear
map with sequentially closed graph from a first-countable topological vector space, let `σ` be a
strand of a family `C` of convex symmetric sets such that no `A ⁻¹' C (res σ k)` is meagre, and
let `c k > 0` be radii and `D k₀` sets such that for `X k ∈ C (res σ (k + 1))` the series
`∑ c (k₀ + j) • X (k₀ + j)` converges to a point of `D k₀`. Then every `A ⁻¹' D k₀` is a
neighbourhood of zero. -/
theorem LinearMap.preimage_mem_nhds_zero_of_isSeqClosed_graph_of_strand {C : List ℕ → Set F}
    (hconv : ∀ l, Convex ℝ (C l)) (hsymm : ∀ l, ∀ y ∈ C l, -y ∈ C l) (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) {σ : ℕ → ℕ}
    (hσ : ∀ k, ¬IsMeagre (A ⁻¹' C (res σ k))) {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) {D : ℕ → Set F}
    (H : ∀ X : ℕ → F, (∀ k, X k ∈ C (res σ (k + 1))) → ∀ k₀, ∃ y ∈ D k₀,
      Tendsto (fun N ↦ ∑ j ∈ Finset.range N, c (k₀ + j) • X (k₀ + j)) atTop (𝓝 y)) (k₀ : ℕ) :
    A ⁻¹' D k₀ ∈ 𝓝 (0 : E) := by
  -- The sets `M k = c k • A ⁻¹' C (res σ (k + 1))` have closures that are neighbourhoods of `0`.
  let M : ℕ → Set E := fun k ↦ c k • (A ⁻¹' C (res σ (k + 1)))
  have hM (k : ℕ) : closure (M k) ∈ 𝓝 (0 : E) :=
    A.closure_smul_preimage_mem_nhds_zero (hconv _) (hsymm _) (hσ (k + 1)) (hc k)
  -- It suffices to show that the closure of `M k₀` lies in the preimage.
  refine mem_of_superset (hM k₀) fun x₀ hx₀ ↦ ?_
  obtain ⟨x, hxM, hxsum⟩ := exists_seq_mem_tendsto_sum_of_mem_closure
    (S := fun j ↦ M (k₀ + j)) (fun j ↦ hM (k₀ + j)) hx₀
  -- The images of the partial sums converge to a point of `D k₀`.
  obtain ⟨y₀, hy₀D, hy₀⟩ := A.exists_tendsto_map_sum_of_strand hσ H k₀ hxM
  have hgraph : (x₀, y₀) ∈ (A.graph : Set (E × F)) :=
    hA (fun N ↦ (LinearMap.mem_graph_iff _ _).mpr rfl) (hxsum.prodMk_nhds hy₀)
  rw [mem_preimage, ← (LinearMap.mem_graph_iff _ _).mp hgraph]
  exact hy₀D

/-- **De Wilde's localization theorem**: for a linear map `A` with sequentially closed graph from
a first-countable Baire topological vector space into a space with a strict web `C` there is a
strand `σ` such that every `A ⁻¹' C (res σ k)` is a neighbourhood of zero,
Köthe II §35.6.(1) a). -/
theorem LinearMap.exists_forall_preimage_res_mem_nhds_zero {C : List ℕ → Set F}
    (hC : IsStrictWeb 𝕜 C) (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F))) :
    ∃ σ : ℕ → ℕ, ∀ k, A ⁻¹' C (res σ k) ∈ 𝓝 (0 : E) := by
  have : Nonempty E := ⟨0⟩
  obtain ⟨σ, hσ⟩ := hC.toIsWeb.exists_forall_not_isMeagre_preimage A
  obtain ⟨ρ, hρ, hstrict⟩ := hC.exists_radius σ
  refine ⟨σ, fun k ↦ ?_⟩
  cases k with
  | zero =>
    rw [res_zero, hC.nil, preimage_univ]
    exact univ_mem
  | succ k₀ =>
    exact A.preimage_mem_nhds_zero_of_isSeqClosed_graph_of_strand hC.convex
      (fun l _ hy ↦ (hC.balanced l).neg_mem_iff.mpr hy) hA hσ hρ
      (D := fun k ↦ C (res σ (k + 1)))
      (fun X hX k₁ ↦ hstrict X ρ hX (fun k ↦ ⟨(hρ k).le, le_rfl⟩) k₁) k₀

/-- Under the hypotheses of the localization theorem the image of a bounded set is absorbed by
every set of the strand, Köthe II §35.6.(1) a). -/
theorem LinearMap.exists_forall_image_subset_smul_res {C : List ℕ → Set F}
    (hC : IsStrictWeb 𝕜 C) (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F))) :
    ∃ σ : ℕ → ℕ, ∀ B : Set E, Bornology.IsVonNBounded ℝ B →
      ∀ k, ∃ a : ℝ, 0 < a ∧ A '' B ⊆ a • C (res σ k) := by
  obtain ⟨σ, hσ⟩ := A.exists_forall_preimage_res_mem_nhds_zero hC hA
  refine ⟨σ, fun B hB k ↦ ?_⟩
  obtain ⟨R, hR⟩ := absorbs_iff_norm.mp (hB (hσ k))
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right R 1), ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hnorm : R ≤ ‖max R 1‖ := by
    rw [Real.norm_eq_abs]
    exact (le_max_left R 1).trans (le_abs_self _)
  obtain ⟨u, hu, hub⟩ := hR (max R 1) hnorm hb
  have hub' : max R 1 • u = b := hub
  exact ⟨A u, hu, by rw [← hub', A.map_smul_of_tower]⟩

section Closed

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [BaireSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

omit [BaireSpace E] in
/-- The core of the localization theorems for a closed graph: the statement of
`LinearMap.preimage_mem_nhds_zero_of_isSeqClosed_graph_of_strand` for a linear map with closed
graph, without a countability assumption on the domain. -/
theorem LinearMap.preimage_mem_nhds_zero_of_isClosed_graph_of_strand {C : List ℕ → Set F}
    (hC : IsWeb C) (hconv : ∀ l, Convex ℝ (C l)) (hsymm : ∀ l, ∀ y ∈ C l, -y ∈ C l)
    (A : E →ₗ[𝕜] F) (hA : IsClosed (A.graph : Set (E × F))) {σ : ℕ → ℕ}
    (hσ : ∀ k, ¬IsMeagre (A ⁻¹' C (res σ k))) {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) {D : ℕ → Set F}
    (H : ∀ X : ℕ → F, (∀ k, X k ∈ C (res σ (k + 1))) → ∀ k₀, ∃ y ∈ D k₀,
      Tendsto (fun N ↦ ∑ j ∈ Finset.range N, c (k₀ + j) • X (k₀ + j)) atTop (𝓝 y)) (k₀ : ℕ) :
    A ⁻¹' D k₀ ∈ 𝓝 (0 : E) := by
  -- The sets `c k • C (res σ (k + 1))` shrink to zero, Köthe II §35.1.(3).
  have hsmall {W : Set F} (hW : W ∈ 𝓝 (0 : F)) :
      ∃ K, ∀ k, K ≤ k → c k • C (res σ (k + 1)) ⊆ W :=
    hC.exists_forall_smul_subset_of_tendsto (fun x hx ↦ by
      obtain ⟨s, -, hs⟩ := H x hx 0
      exact ⟨s, by simpa using hs⟩) hW
  let M : ℕ → Set E := fun k ↦ c k • (A ⁻¹' C (res σ (k + 1)))
  have hM (k : ℕ) : closure (M k) ∈ 𝓝 (0 : E) :=
    A.closure_smul_preimage_mem_nhds_zero (hconv _) (hsymm _) (hσ (k + 1)) (hc k)
  refine mem_of_superset (hM k₀) fun x₀ hx₀ ↦ ?_
  -- Successive approximation without convergence: the remainders stay in the closures.
  obtain ⟨x, hxM, hrem⟩ := exists_seq_mem_sub_sum_mem_closure
    (S := fun j ↦ M (k₀ + j)) (B := fun _ ↦ univ) (fun j ↦ hM (k₀ + j))
    (fun _ ↦ univ_mem) hx₀
  -- The images of the partial sums converge to a point of `D k₀`.
  obtain ⟨y₀, hy₀D, hy₀⟩ := A.exists_tendsto_map_sum_of_strand hσ H k₀ hxM
  -- The point `(x₀, y₀)` lies in the closure of the graph.
  have hgraph : (x₀, y₀) ∈ (A.graph : Set (E × F)) := by
    rw [← hA.closure_eq, mem_closure_iff_nhds]
    intro O hO
    obtain ⟨O₁, hO₁, O₂, hO₂, hO12⟩ := mem_nhds_prod_iff.mp hO
    have hadd : Tendsto (fun p : F × F ↦ p.1 + p.2) (𝓝 (y₀, 0)) (𝓝 y₀) := by
      have h := (continuous_add (M := F)).tendsto (y₀, 0)
      rwa [add_zero] at h
    obtain ⟨W₁, hW₁, W₂, hW₂, hW12⟩ := mem_nhds_prod_iff.mp (hadd hO₂)
    obtain ⟨K, hK⟩ := hsmall hW₂
    have hev : ∀ᶠ N in atTop, A (∑ j ∈ Finset.range N, x j) ∈ W₁ := hy₀.eventually hW₁
    obtain ⟨n, hnK, hnW⟩ : ∃ n, K ≤ n ∧ A (∑ j ∈ Finset.range (n + 1), x j) ∈ W₁ := by
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
      exact ⟨max K N₀, le_max_left _ _, hN₀ _ (by omega)⟩
    -- Approximate the remainder by a point `t` of `M (k₀ + (n + 1))`.
    let sn := ∑ j ∈ Finset.range (n + 1), x j
    have hcont : ContinuousAt (fun t : E ↦ sn + t) (x₀ - sn) := by fun_prop
    have hpre : (fun t : E ↦ sn + t) ⁻¹' O₁ ∈ 𝓝 (x₀ - sn) :=
      hcont.preimage_mem_nhds (by simpa using hO₁)
    obtain ⟨t, ht, htM⟩ := mem_closure_iff_nhds.mp (hrem n).1 _ hpre
    obtain ⟨v, hv, hvt⟩ := htM
    have hvt' : c (k₀ + (n + 1)) • v = t := hvt
    have hAt : A t ∈ W₂ := by
      rw [← hvt', A.map_smul_of_tower]
      exact hK (k₀ + (n + 1)) (by omega) (smul_mem_smul_set hv)
    refine ⟨(sn + t, A sn + A t), hO12 ⟨ht, hW12 (show (A sn, A t) ∈ W₁ ×ˢ W₂ from
      ⟨hnW, hAt⟩)⟩, ?_⟩
    exact (LinearMap.mem_graph_iff _ _).mpr (map_add A sn t).symm
  rw [mem_preimage, ← (LinearMap.mem_graph_iff _ _).mp hgraph]
  exact hy₀D

/-- **De Wilde's localization theorem for a closed graph**: for a linear map `A` with closed graph
from a Baire topological vector space into a space with a strict web `C` there is a strand `σ`
such that every `A ⁻¹' C (res σ k)` is a neighbourhood of zero, Köthe II §35.6.(1) b). No
countability assumption is made on the domain. -/
theorem LinearMap.exists_forall_preimage_res_mem_nhds_zero_of_isClosed {C : List ℕ → Set F}
    (hC : IsStrictWeb 𝕜 C) (A : E →ₗ[𝕜] F) (hA : IsClosed (A.graph : Set (E × F))) :
    ∃ σ : ℕ → ℕ, ∀ k, A ⁻¹' C (res σ k) ∈ 𝓝 (0 : E) := by
  have : Nonempty E := ⟨0⟩
  obtain ⟨σ, hσ⟩ := hC.toIsWeb.exists_forall_not_isMeagre_preimage A
  obtain ⟨ρ, hρ, hstrict⟩ := hC.exists_radius σ
  refine ⟨σ, fun k ↦ ?_⟩
  cases k with
  | zero =>
    rw [res_zero, hC.nil, preimage_univ]
    exact univ_mem
  | succ k₀ =>
    exact A.preimage_mem_nhds_zero_of_isClosed_graph_of_strand hC.toIsWeb hC.convex
      (fun l _ hy ↦ (hC.balanced l).neg_mem_iff.mpr hy) hA hσ hρ
      (D := fun k ↦ C (res σ (k + 1)))
      (fun X hX k₁ ↦ hstrict X ρ hX (fun k ↦ ⟨(hρ k).le, le_rfl⟩) k₁) k₀

/-- The localization theorem for a partially defined linear map with closed graph whose domain
is not meagre: the map is defined everywhere (`LinearPMap.domain_eq_top_of_isClosed_graph`) and
there is a strand `σ` of the strict web `C` such that every `A ⁻¹' C (res σ k)` is a
neighbourhood of zero, Köthe II §35.6.(1) b). -/
theorem LinearPMap.exists_forall_image_preimage_res_mem_nhds_zero_of_isClosed
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] {C : List ℕ → Set F} (hC : IsStrictWeb 𝕜 C)
    (A : E →ₗ.[𝕜] F) (hA : IsClosed (A.graph : Set (E × F)))
    (hne : ¬IsMeagre (A.domain : Set E)) :
    ∃ σ : ℕ → ℕ, ∀ k, ((↑) : A.domain → E) '' (A ⁻¹' C (res σ k)) ∈ 𝓝 (0 : E) := by
  have : WebbedSpace F := ⟨C, hC.toIsCompletingWeb⟩
  have htop := A.domain_eq_top_of_isClosed_graph hA hne
  -- The map as a map defined everywhere.
  let e : E ≃ₗ[𝕜] A.domain := (LinearEquiv.ofTop A.domain htop).symm
  let A' : E →ₗ[𝕜] F := A.toFun ∘ₗ e.toLinearMap
  have hgraph : (A'.graph : Set (E × F)) = A.graph := by
    ext q
    rw [SetLike.mem_coe, LinearMap.mem_graph_iff, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · intro h
      exact ⟨e q.1, rfl, h.symm⟩
    · rintro ⟨x, hx, hxq⟩
      have hex : e q.1 = x := Subtype.ext hx.symm
      rw [← hxq, ← hex]
      rfl
  obtain ⟨σ, hσ⟩ := A'.exists_forall_preimage_res_mem_nhds_zero_of_isClosed hC (hgraph ▸ hA)
  exact ⟨σ, fun k ↦ mem_of_superset (hσ k) fun x hx ↦ ⟨e x, hx, rfl⟩⟩

end Closed

section BanachDisk

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]

/-- **The localization theorem for Banach disks**: let `A` be a linear map with sequentially
closed graph from a locally convex space `E` into a space with a strict web `C`. For every Banach
disk `B` in `E` there is a strand `σ` such that every set `C (res σ k)` absorbs `A '' B`,
Köthe II §35.6.(2) a). -/
theorem LinearMap.exists_forall_image_banachDisk_subset_smul_res {C : List ℕ → Set F}
    (hC : IsStrictWeb 𝕜 C) (A : E →ₗ[𝕜] F) (hA : IsSeqClosed (A.graph : Set (E × F)))
    {B : Set E} (hB : Bornology.IsBanachDisk 𝕜 B) :
    ∃ σ : ℕ → ℕ, ∀ k, ∃ a : ℝ, 0 < a ∧ A '' B ⊆ a • C (res σ k) := by
  have := hB.completeSpace
  -- The restriction of `A` to the Banach space `E_B` has a sequentially closed graph.
  let A' : DiskSpace 𝕜 B →ₗ[𝕜] F := A ∘ₗ DiskSpace.incl 𝕜 B
  have hcont : Continuous (DiskSpace.incl 𝕜 B) := DiskSpace.continuous_incl hB.isVonNBounded
  have hA' : IsSeqClosed (A'.graph : Set (DiskSpace 𝕜 B × F)) := by
    intro u q hu hq
    have h1 : Tendsto (fun n ↦ (DiskSpace.incl 𝕜 B (u n).1, (u n).2)) atTop
        (𝓝 (DiskSpace.incl 𝕜 B q.1, q.2)) :=
      ((hcont.tendsto q.1).comp ((continuous_fst.tendsto q).comp hq)).prodMk_nhds
        ((continuous_snd.tendsto q).comp hq)
    have h2 : (DiskSpace.incl 𝕜 B q.1, q.2) ∈ (A.graph : Set (E × F)) :=
      hA (fun n ↦ (LinearMap.mem_graph_iff _ _).mpr
        ((LinearMap.mem_graph_iff _ _).mp (hu n))) h1
    exact (LinearMap.mem_graph_iff _ _).mpr ((LinearMap.mem_graph_iff _ _).mp h2)
  obtain ⟨σ, hσ⟩ := A'.exists_forall_image_subset_smul_res hC hA'
  refine ⟨σ, fun k ↦ ?_⟩
  -- The unit disk of `E_B` is bounded and is mapped onto a set that contains `B`.
  have hbdd : Bornology.IsVonNBounded ℝ (DiskSpace.unitDisk 𝕜 B) :=
    (NormedSpace.isVonNBounded_closedBall ℝ (DiskSpace 𝕜 B) 1).subset fun ξ hξ ↦ by
      rw [mem_closedBall_zero_iff]
      exact DiskSpace.norm_le_one_of_mem_unitDisk hξ
  obtain ⟨a, ha, hsub⟩ := hσ _ hbdd k
  refine ⟨a, ha, Subset.trans ?_ hsub⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨ξ, hξ⟩ := DiskSpace.exists_incl_eq (𝕜 := 𝕜) (Submodule.subset_span hb)
  exact ⟨ξ, by
    change DiskSpace.incl 𝕜 B ξ ∈ diskHull 𝕜 B
    rw [hξ]
    exact subset_diskHull B hb, by
    change A (DiskSpace.incl 𝕜 B ξ) = A b
    rw [hξ]⟩

/-- Every Banach disk of a locally convex space with a strict web `C` is absorbed by all the sets
of some strand of the web, Köthe II §35.6.(2) b). -/
theorem IsStrictWeb.exists_forall_banachDisk_subset_smul_res {C : List ℕ → Set E}
    (hC : IsStrictWeb 𝕜 C) [T2Space E] {B : Set E} (hB : Bornology.IsBanachDisk 𝕜 B) :
    ∃ σ : ℕ → ℕ, ∀ k, ∃ a : ℝ, 0 < a ∧ B ⊆ a • C (res σ k) := by
  have hid : IsSeqClosed ((LinearMap.id : E →ₗ[𝕜] E).graph : Set (E × E)) :=
    (ContinuousLinearMap.id 𝕜 E).isClosed_graph.isSeqClosed
  obtain ⟨σ, hσ⟩ := (LinearMap.id : E →ₗ[𝕜] E).exists_forall_image_banachDisk_subset_smul_res
    hC hid hB
  exact ⟨σ, fun k ↦ by simpa using hσ k⟩

end BanachDisk

section Grothendieck

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module 𝕜 (X n)]
  [∀ n, Module ℝ (X n)] [∀ n, IsScalarTower ℝ 𝕜 (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, StrictlyWebbedSpace 𝕜 (X n)] [ContinuousAdd F]

/-- **Grothendieck's factorization theorem**, first part: let `F` be the union of the ranges of
sequentially continuous linear maps `f n` defined on strictly webbed spaces `X n`, for instance
an LF space with its steps. A linear map with sequentially closed graph from a first-countable
Baire topological vector space into `F` maps into the range of one of the `f n`. -/
theorem LinearMap.exists_range_le_range_of_isSeqClosed_graph (f : ∀ n, X n →ₗ[𝕜] F)
    (hf : ∀ n, SeqContinuous (f n)) (hsurj : ⋃ n, Set.range (f n) = univ) (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) :
    ∃ n, LinearMap.range A ≤ LinearMap.range (f n) := by
  choose C hC using fun n ↦ StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := X n)
  obtain ⟨σ, hσ⟩ := A.exists_forall_preimage_res_mem_nhds_zero
    (WebConstruction.isStrictWeb_webUnionImage hf hsurj hC) hA
  refine ⟨σ 0, ?_⟩
  -- The preimage of the range of `f (σ 0)` is a subspace and a neighbourhood of zero.
  have h1 := hσ 1
  rw [WebConstruction.webUnionImage_res_succ] at h1
  have htop : ((LinearMap.range (f (σ 0))).comap A).restrictScalars ℝ = ⊤ :=
    (((LinearMap.range (f (σ 0))).comap A).restrictScalars ℝ).eq_top_of_nonempty_interior'
      ⟨0, mem_interior_iff_mem_nhds.mpr (mem_of_superset h1 fun x hx ↦ by
        obtain ⟨v, -, hv⟩ := hx
        exact ⟨v, hv⟩)⟩
  have htop' : (LinearMap.range (f (σ 0))).comap A = ⊤ :=
    (Submodule.restrictScalars_eq_top_iff ℝ 𝕜 E).mp htop
  rintro _ ⟨x, rfl⟩
  exact (htop' ▸ Submodule.mem_top : x ∈ (LinearMap.range (f (σ 0))).comap A)

/-- **Grothendieck's factorization theorem**: let `F` be the union of the ranges of injective
sequentially continuous linear maps `f n` defined on strictly webbed locally convex spaces
`X n`, for instance an LF space with its steps. A linear map `A` with sequentially closed graph
from a first-countable Baire topological vector space into `F` factors through one of the
`f n`, with a continuous factor. -/
theorem LinearMap.exists_continuousLinearMap_comp_eq_of_isSeqClosed_graph
    [∀ n, IsTopologicalAddGroup (X n)] [∀ n, ContinuousSMul 𝕜 (X n)]
    [∀ n, LocallyConvexSpace ℝ (X n)] (f : ∀ n, X n →ₗ[𝕜] F) (hf : ∀ n, SeqContinuous (f n))
    (hinj : ∀ n, Injective (f n)) (hsurj : ⋃ n, Set.range (f n) = univ) (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) :
    ∃ (n : ℕ) (A' : E →L[𝕜] X n), ∀ x, f n (A' x) = A x := by
  obtain ⟨n, hn⟩ := A.exists_range_le_range_of_isSeqClosed_graph f hf hsurj hA
  let e := LinearEquiv.ofInjective (f n) (hinj n)
  let A' : E →ₗ[𝕜] X n :=
    e.symm.toLinearMap ∘ₗ A.codRestrict (LinearMap.range (f n)) fun x ↦ hn ⟨x, rfl⟩
  have hA' (x : E) : f n (A' x) = A x := by
    have h := e.apply_symm_apply (A.codRestrict (LinearMap.range (f n)) (fun x ↦ hn ⟨x, rfl⟩) x)
    exact congrArg Subtype.val h
  -- The factor has a sequentially closed graph, because `f n` is injective.
  have hgraph : IsSeqClosed (A'.graph : Set (E × X n)) := by
    intro u p hu hp
    have hfst : Tendsto (fun j ↦ (u j).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
    have hsnd : Tendsto (fun j ↦ (u j).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
    have h1 : Tendsto (fun j ↦ ((u j).1, f n (u j).2)) atTop (𝓝 (p.1, f n p.2)) :=
      hfst.prodMk_nhds (hf n hsnd)
    have h2 : (p.1, f n p.2) ∈ (A.graph : Set (E × F)) :=
      hA (fun j ↦ (LinearMap.mem_graph_iff _ _).mpr (by
        rw [(LinearMap.mem_graph_iff _ _).mp (hu j), hA'])) h1
    refine (LinearMap.mem_graph_iff _ _).mpr (hinj n ?_)
    rw [hA', ← (LinearMap.mem_graph_iff _ _).mp h2]
  have : WebbedSpace (X n) := StrictlyWebbedSpace.toWebbedSpace (𝕜 := 𝕜)
  exact ⟨n, ⟨A', A'.continuous_of_isSeqClosed_graph_of_baireSpace hgraph⟩, hA'⟩

end Grothendieck
