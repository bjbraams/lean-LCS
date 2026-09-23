/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences
public import WebbedSpaces.Basic

/-!
# Hereditary properties of webbed spaces: subspaces, images, countable unions

Following [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4, we prove that the
classes of webbed and of strictly webbed spaces are stable under

* passing to a sequentially closed subspace, §35.4.(1), and more generally to a space with an
  inducing linear map, with sequentially closed range, into a space of the class;
* passing to a space that is the union of countably many images of spaces of the class under
  sequentially continuous linear maps.

The second statement contains Köthe's §35.4.(2) (images), (3) (quotients), (4) (coarser
topologies), (8) (inductive limits of sequences) and, together with countable products, (9)
(countable locally convex hulls). No topology on the union is prescribed: all that is used is
that the maps are sequentially continuous.

The explicit web constructions and their calculation lemmas live in the `WebConstruction`
namespace.

## Main definitions

* `WebConstruction.webUnionImage f C`: for linear maps `f n : E n → F` and webs `C n` on `E n`, the
  web on `F` whose first index selects `n` and whose further indices select an image under `f n` of
  a set of the web `C n`.

## Main statements

* `IsCompletingWeb.preimage_of_isInducing`, `IsStrictWeb.preimage_of_isInducing`: the preimage
  of a web under an inducing linear map with sequentially closed range.
* `WebbedSpace.of_isInducing`, `StrictlyWebbedSpace.of_isInducing`.
* `WebConstruction.isCompletingWeb_webUnionImage`, `WebConstruction.isStrictWeb_webUnionImage`.
* `WebbedSpace.of_isSeqClosed`, `StrictlyWebbedSpace.of_isSeqClosed`.
* `WebbedSpace.of_iUnion_range`, `StrictlyWebbedSpace.of_iUnion_range`.
* `WebbedSpace.of_surjective`, `StrictlyWebbedSpace.of_surjective`.
* Instances for quotients.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4

## Tags

web, webbed space, hereditary properties
-/

public section

open Set Filter PiNat Function

open scoped Topology

section Inducing

variable {𝕜 E H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [AddCommGroup H] [Module 𝕜 H] [Module ℝ H]
  [IsScalarTower ℝ 𝕜 H] [TopologicalSpace H] {C : List ℕ → Set E}

omit [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [Module 𝕜 H]
  [Module ℝ H] [IsScalarTower ℝ 𝕜 H] [TopologicalSpace H] [AddCommGroup E] [AddCommGroup H] in
/-- The preimage of a web under any map is a web. -/
theorem IsWeb.preimage (hC : IsWeb C) (Φ : H → E) : IsWeb fun l ↦ Φ ⁻¹' C l where
  nil := by rw [hC.nil, preimage_univ]
  iUnion_cons l := by rw [← preimage_iUnion, hC.iUnion_cons]

omit [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [Module 𝕜 H] [IsScalarTower ℝ 𝕜 H] in
/-- Convergence of a series in the domain of an inducing linear map with sequentially closed
range, from convergence of its image. -/
private theorem exists_tendsto_of_isInducing {Φ : H →ₗ[ℝ] E} (hΦ : Topology.IsInducing Φ)
    (hr : IsSeqClosed (range Φ)) (y : ℕ → H) {s : E}
    (hs : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, Φ (y k)) atTop (𝓝 s)) :
    ∃ t : H, Φ t = s ∧ Tendsto (fun N ↦ ∑ k ∈ Finset.range N, y k) atTop (𝓝 t) := by
  have hsum (N : ℕ) : Φ (∑ k ∈ Finset.range N, y k) = ∑ k ∈ Finset.range N, Φ (y k) :=
    map_sum Φ y _
  obtain ⟨t, rfl⟩ : s ∈ range Φ := hr (fun N ↦ ⟨_, hsum N⟩) hs
  refine ⟨t, rfl, ?_⟩
  rw [hΦ.tendsto_nhds_iff]
  exact hs.congr fun N ↦ (hsum N).symm

omit [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [Module 𝕜 H] [IsScalarTower ℝ 𝕜 H] in
/-- The preimage of a completing web under an inducing linear map with sequentially closed
range is a completing web. -/
theorem IsCompletingWeb.preimage_of_isInducing (hC : IsCompletingWeb C) {Φ : H →ₗ[ℝ] E}
    (hΦ : Topology.IsInducing Φ) (hr : IsSeqClosed (range Φ)) :
    IsCompletingWeb fun l ↦ Φ ⁻¹' C l where
  toIsWeb := hC.toIsWeb.preimage Φ
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := hC.exists_radius σ
    refine ⟨ρ, hρ, fun x c hx hc ↦ ?_⟩
    obtain ⟨s, hs⟩ := h (fun k ↦ Φ (x k)) c hx hc
    obtain ⟨t, -, ht⟩ := exists_tendsto_of_isInducing hΦ hr (fun k ↦ c k • x k)
      (hs.congr fun N ↦ Finset.sum_congr rfl fun k _ ↦ (map_smul Φ (c k) (x k)).symm)
    exact ⟨t, ht⟩

/-- The preimage of a strict web under an inducing linear map with sequentially closed range
is a strict web. -/
theorem IsStrictWeb.preimage_of_isInducing (hC : IsStrictWeb 𝕜 C) {Φ : H →ₗ[𝕜] E}
    (hΦ : Topology.IsInducing Φ) (hr : IsSeqClosed (range Φ)) :
    IsStrictWeb 𝕜 fun l ↦ Φ ⁻¹' C l where
  toIsWeb := hC.toIsWeb.preimage Φ
  convex l := (hC.convex l).is_linear_preimage (Φ.restrictScalars ℝ).isLinear
  balanced l := (hC.balanced l).preimage Φ
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := hC.exists_radius σ
    refine ⟨ρ, hρ, fun x c hx hc k₀ ↦ ?_⟩
    obtain ⟨s, hsC, hs⟩ := h (fun k ↦ Φ (x k)) c hx hc k₀
    obtain ⟨t, hts, ht⟩ := exists_tendsto_of_isInducing (Φ := Φ.restrictScalars ℝ) hΦ hr
      (fun k ↦ c (k₀ + k) • x (k₀ + k))
      (hs.congr fun N ↦ Finset.sum_congr rfl fun k _ ↦
        (Φ.map_smul_of_tower (c (k₀ + k)) (x (k₀ + k))).symm)
    have hts' : Φ t = s := hts
    exact ⟨t, by rw [mem_preimage, hts']; exact hsC, ht⟩

/-- A space that is mapped by an inducing linear map, with sequentially closed range, into a
webbed space is webbed. This contains the statement about sequentially closed subspaces and,
with countable products, the statement about countable projective limits,
Köthe II §35.4.(1), (7). -/
theorem WebbedSpace.of_isInducing [WebbedSpace E] (Φ : H →ₗ[ℝ] E)
    (hΦ : Topology.IsInducing Φ) (hr : IsSeqClosed (range Φ)) : WebbedSpace H := by
  obtain ⟨C, hC⟩ := WebbedSpace.exists_isCompletingWeb (E := E)
  exact ⟨_, hC.preimage_of_isInducing hΦ hr⟩

/-- A space that is mapped by an inducing linear map, with sequentially closed range, into a
strictly webbed space is strictly webbed, Köthe II §35.4.(1), (7). -/
theorem StrictlyWebbedSpace.of_isInducing [StrictlyWebbedSpace 𝕜 E] (Φ : H →ₗ[𝕜] E)
    (hΦ : Topology.IsInducing Φ) (hr : IsSeqClosed (range Φ)) : StrictlyWebbedSpace 𝕜 H := by
  obtain ⟨C, hC⟩ := StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := E)
  exact ⟨_, hC.preimage_of_isInducing hΦ hr⟩

end Inducing

section Subspace

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] (H : Submodule 𝕜 E)

/-- A sequentially closed subspace of a webbed space is webbed, Köthe II §35.4.(1). -/
theorem WebbedSpace.of_isSeqClosed [WebbedSpace E] (hH : IsSeqClosed (H : Set E)) :
    WebbedSpace H :=
  WebbedSpace.of_isInducing (H.subtype.restrictScalars ℝ) Topology.IsInducing.subtypeVal
    (by simpa using hH)

/-- A sequentially closed subspace of a strictly webbed space is strictly webbed,
Köthe II §35.4.(1). -/
theorem StrictlyWebbedSpace.of_isSeqClosed [StrictlyWebbedSpace 𝕜 E]
    (hH : IsSeqClosed (H : Set E)) : StrictlyWebbedSpace 𝕜 H :=
  StrictlyWebbedSpace.of_isInducing H.subtype Topology.IsInducing.subtypeVal
    (by simpa using hH)

end Subspace

section UnionImageDef

variable {E : ℕ → Type*} {F : Type*}

/-- For maps `f n : E n → F` and webs `C n` on `E n`, the family of subsets of `F` whose first
index `n` selects the map `f n` and whose further indices select the image under `f n` of a
set of the web `C n`. As the newest index of a web is at the head of the list, the first index
is the last entry of the list. -/
@[expose]
def WebConstruction.webUnionImage (f : ∀ n, E n → F) (C : ∀ n, List ℕ → Set (E n))
    (l : List ℕ) : Set F :=
  match l.reverse with
  | [] => univ
  | n :: l' => f n '' C n l'.reverse

/-- The root of `WebConstruction.webUnionImage` is the whole space. -/
@[simp]
theorem WebConstruction.webUnionImage_nil (f : ∀ n, E n → F) (C : ∀ n, List ℕ → Set (E n)) :
    WebConstruction.webUnionImage f C [] = univ :=
  rfl

/-- The set of `WebConstruction.webUnionImage` for a list with first index `n`. -/
@[simp]
theorem WebConstruction.webUnionImage_append_singleton (f : ∀ n, E n → F)
    (C : ∀ n, List ℕ → Set (E n)) (l : List ℕ) (n : ℕ) :
    WebConstruction.webUnionImage f C (l ++ [n]) = f n '' C n l := by
  simp [WebConstruction.webUnionImage]

/-- The sets of `WebConstruction.webUnionImage` along a strand `σ`: the first index `σ 0` selects
the map; the remaining indices form a strand of the web `C (σ 0)`. -/
theorem WebConstruction.webUnionImage_res_succ (f : ∀ n, E n → F) (C : ∀ n, List ℕ → Set (E n))
    (σ : ℕ → ℕ) (k : ℕ) :
    WebConstruction.webUnionImage f C (res σ (k + 1)) =
      f (σ 0) '' C (σ 0) (res (fun i ↦ σ (i + 1)) k) := by
  rw [res_succ_eq_res_append, WebConstruction.webUnionImage_append_singleton]

/-- If the ranges of the maps `f n` cover `F` and every `C n` is a web, then
`WebConstruction.webUnionImage f C` is a web. -/
theorem WebConstruction.isWeb_webUnionImage {f : ∀ n, E n → F} {C : ∀ n, List ℕ → Set (E n)}
    (hf : ⋃ n, range (f n) = univ) (hC : ∀ n, IsWeb (C n)) :
    IsWeb (WebConstruction.webUnionImage f C) where
  nil := rfl
  iUnion_cons l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · rw [WebConstruction.webUnionImage_nil, ← hf]
      refine iUnion_congr fun n ↦ ?_
      have h := WebConstruction.webUnionImage_append_singleton f C [] n
      rw [List.nil_append] at h
      rw [h, (hC n).nil, image_univ]
    · simp only [List.concat_eq_append]
      have h (n : ℕ) :
          WebConstruction.webUnionImage f C (n :: (L ++ [b])) = f b '' C b (n :: L) := by
        rw [← List.cons_append, WebConstruction.webUnionImage_append_singleton]
      simp_rw [h]
      rw [WebConstruction.webUnionImage_append_singleton, ← image_iUnion, (hC b).iUnion_cons]

end UnionImageDef

section UnionImage

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
  [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]

/-- The series argument for `WebConstruction.webUnionImage`: from convergence of the tails of
`∑ c k • w k` with indices `1 + k` in the domain of a sequentially continuous linear map `g` to
convergence of the tails of `∑ c k • g (w k)`. -/
private theorem tendsto_sum_smul_map {G : Type*} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] {g : G →ₗ[ℝ] F} (hg : SeqContinuous g) (w : ℕ → G) (c : ℕ → ℝ)
    (m : ℕ) {s : G}
    (hs : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, c (1 + (m + i)) • w (1 + (m + i))) atTop
      (𝓝 s)) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, c (m + 1 + i) • g (w (m + 1 + i))) atTop
      (𝓝 (g s)) := by
  refine (hg hs).congr fun N ↦ ?_
  rw [Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, show 1 + (m + i) = m + 1 + i by omega]

variable [ContinuousAdd F]

/-- If `F` is the union of the ranges of sequentially continuous linear maps `f n : E n → F`
and every `C n` is a completing web on `E n`, then `WebConstruction.webUnionImage f C` is a
completing web on `F`. -/
theorem WebConstruction.isCompletingWeb_webUnionImage {f : ∀ n, E n →ₗ[ℝ] F}
    {C : ∀ n, List ℕ → Set (E n)}
    (hf : ∀ n, SeqContinuous (f n)) (hsurj : ⋃ n, range (f n) = univ)
    (hC : ∀ n, IsCompletingWeb (C n)) :
    IsCompletingWeb (WebConstruction.webUnionImage (fun n ↦ ⇑(f n)) C) where
  toIsWeb := WebConstruction.isWeb_webUnionImage hsurj fun n ↦ (hC n).toIsWeb
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := (hC (σ 0)).exists_radius fun i ↦ σ (i + 1)
    refine ⟨fun k ↦ Nat.casesOn k 1 ρ, fun k ↦ ?_, fun x c hx hc ↦ ?_⟩
    · cases k with
      | zero => exact one_pos
      | succ k => exact hρ k
    -- Lift the terms `x (1 + i)` to `E (σ 0)`.
    have hw (i : ℕ) : ∃ w ∈ C (σ 0) (res (fun i ↦ σ (i + 1)) (i + 1)), f (σ 0) w = x (1 + i) := by
      have h1 := hx (1 + i)
      rw [WebConstruction.webUnionImage_res_succ, Nat.add_comm 1 i] at h1
      rw [Nat.add_comm 1 i]
      exact h1
    choose w hwC hwx using hw
    obtain ⟨s, hs⟩ := h w (fun i ↦ c (1 + i)) hwC fun i ↦ by
      have := hc (1 + i)
      rw [Nat.add_comm 1 i] at this ⊢
      exact this
    have h2 : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, c (1 + i) • x (1 + i)) atTop
        (𝓝 (f (σ 0) s)) := by
      refine ((hf (σ 0)) hs).congr fun N ↦ ?_
      rw [Function.comp_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hwx]
    exact ⟨_, tendsto_sum_range_of_tendsto_sum_range_add (a := fun k ↦ c k • x k) h2⟩

/-- If `F` is the union of the ranges of sequentially continuous linear maps `f n : E n → F`
and every `C n` is a strict web on `E n`, then `WebConstruction.webUnionImage f C` is a strict web
on `F`. -/
theorem WebConstruction.isStrictWeb_webUnionImage {f : ∀ n, E n →ₗ[𝕜] F} {C : ∀ n, List ℕ → Set (E
    n)}
    (hf : ∀ n, SeqContinuous (f n)) (hsurj : ⋃ n, range (f n) = univ)
    (hC : ∀ n, IsStrictWeb 𝕜 (C n)) :
    IsStrictWeb 𝕜 (WebConstruction.webUnionImage (fun n ↦ ⇑(f n)) C) where
  toIsWeb := WebConstruction.isWeb_webUnionImage hsurj fun n ↦ (hC n).toIsWeb
  convex l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact convex_univ
    · rw [List.concat_eq_append, WebConstruction.webUnionImage_append_singleton]
      exact ((hC b).convex L).is_linear_image ((f b).restrictScalars ℝ).isLinear
  balanced l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact balanced_univ
    · rw [List.concat_eq_append, WebConstruction.webUnionImage_append_singleton]
      exact ((hC b).balanced L).image (f b)
  exists_radius σ := by
    obtain ⟨ρ, hρ, h⟩ := (hC (σ 0)).exists_radius fun i ↦ σ (i + 1)
    refine ⟨fun k ↦ Nat.casesOn k 1 ρ, fun k ↦ ?_, fun x c hx hc k₀ ↦ ?_⟩
    · cases k with
      | zero => exact one_pos
      | succ k => exact hρ k
    -- Lift all terms to `E (σ 0)`.
    have hw (i : ℕ) : ∃ w ∈ C (σ 0) (res (fun i ↦ σ (i + 1)) (i + 1)), f (σ 0) w = x (1 + i) := by
      have h1 := hx (1 + i)
      rw [WebConstruction.webUnionImage_res_succ, Nat.add_comm 1 i] at h1
      rw [Nat.add_comm 1 i]
      exact h1
    choose w hwC hwx using hw
    have hc' (i : ℕ) : 0 ≤ c (1 + i) ∧ c (1 + i) ≤ ρ i := by
      have := hc (1 + i)
      rw [Nat.add_comm 1 i] at this ⊢
      exact this
    have hfℝ : SeqContinuous ((f (σ 0)).restrictScalars ℝ) := hf (σ 0)
    have key (m : ℕ) : ∃ s ∈ C (σ 0) (res (fun i ↦ σ (i + 1)) (m + 1)),
        Tendsto (fun N ↦ ∑ i ∈ Finset.range N, c (m + 1 + i) • x (m + 1 + i)) atTop
          (𝓝 (f (σ 0) s)) := by
      obtain ⟨s, hsC, hs⟩ := h w (fun i ↦ c (1 + i)) hwC hc' m
      refine ⟨s, hsC, ?_⟩
      have h3 := tendsto_sum_smul_map hfℝ (fun k ↦ Nat.casesOn k 0 w) c m (s := s) (by
        refine hs.congr fun N ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Nat.add_comm 1 (m + i)])
      refine h3.congr fun N ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      have : m + 1 + i = 1 + (m + i) := by omega
      rw [this, ← hwx (m + i), Nat.add_comm 1 (m + i)]
      rfl
    cases k₀ with
    | zero =>
      -- The whole series: its sum lies in the range of `f (σ 0)`.
      obtain ⟨s, -, hs⟩ := key 0
      obtain ⟨w₀, -, hw₀⟩ : x 0 ∈ f (σ 0) '' C (σ 0) (res (fun i ↦ σ (i + 1)) 0) := by
        have h1 := hx 0
        rwa [WebConstruction.webUnionImage_res_succ] at h1
      have h4 := tendsto_sum_range_of_tendsto_sum_range_add (a := fun k ↦ c k • x k) (m := 1)
        (by simpa [Nat.add_comm] using hs)
      refine ⟨f (σ 0) (c 0 • w₀ + s), ?_, ?_⟩
      · rw [WebConstruction.webUnionImage_res_succ, res_zero, ((hC (σ 0)).nil), image_univ]
        exact mem_range_self _
      · simp only [zero_add]
        have h5 : f (σ 0) (c 0 • w₀ + s) = ∑ k ∈ Finset.range 1, c k • x k + f (σ 0) s := by
          rw [map_add, (f (σ 0)).map_smul_of_tower, hw₀, Finset.sum_range_one]
        rw [h5]
        exact h4
    | succ m =>
      obtain ⟨s, hsC, hs⟩ := key m
      refine ⟨f (σ 0) s, ?_, hs⟩
      rw [WebConstruction.webUnionImage_res_succ]
      exact mem_image_of_mem _ hsC

end UnionImage

section Classes

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Countable ι] {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F]

/-- A space that is the union of countably many images of webbed spaces under sequentially
continuous linear maps is webbed. This contains Köthe II §35.4.(2), (3), (4) and (8); in
particular the inductive limit of a sequence of webbed spaces is webbed. -/
theorem WebbedSpace.of_iUnion_range [∀ i, WebbedSpace (E i)] (f : ∀ i, E i →ₗ[ℝ] F)
    (hf : ∀ i, SeqContinuous (f i)) (hsurj : ⋃ i, range (f i) = univ) : WebbedSpace F := by
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := mem_iUnion.mp (hsurj ▸ mem_univ (0 : F))
    exact ⟨i⟩
  obtain ⟨g, hg⟩ := exists_surjective_nat ι
  choose C hC using fun i ↦ WebbedSpace.exists_isCompletingWeb (E := E i)
  refine ⟨_, WebConstruction.isCompletingWeb_webUnionImage (E := fun n ↦ E (g n))
    (f := fun n ↦ f (g n))
    (C := fun n ↦ C (g n)) (fun n ↦ hf _) ?_ (fun n ↦ hC _)⟩
  rw [← hsurj]
  exact hg.iUnion_comp fun i ↦ range (f i)

/-- A space that is the union of countably many images of strictly webbed spaces under
sequentially continuous linear maps is strictly webbed. -/
theorem StrictlyWebbedSpace.of_iUnion_range [∀ i, StrictlyWebbedSpace 𝕜 (E i)]
    (f : ∀ i, E i →ₗ[𝕜] F) (hf : ∀ i, SeqContinuous (f i))
    (hsurj : ⋃ i, range (f i) = univ) : StrictlyWebbedSpace 𝕜 F := by
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := mem_iUnion.mp (hsurj ▸ mem_univ (0 : F))
    exact ⟨i⟩
  obtain ⟨g, hg⟩ := exists_surjective_nat ι
  choose C hC using fun i ↦ StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := E i)
  refine ⟨_, WebConstruction.isStrictWeb_webUnionImage (E := fun n ↦ E (g n)) (f := fun n ↦ f (g n))
    (C := fun n ↦ C (g n)) (fun n ↦ hf _) ?_ (fun n ↦ hC _)⟩
  rw [← hsurj]
  exact hg.iUnion_comp fun i ↦ range (f i)

end Classes

section Image

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F]

/-- The image of a webbed space under a sequentially continuous linear map is webbed,
Köthe II §35.4.(2). -/
theorem WebbedSpace.of_surjective [WebbedSpace E] (A : E →ₗ[ℝ] F) (hA : SeqContinuous A)
    (hsurj : Surjective A) : WebbedSpace F :=
  WebbedSpace.of_iUnion_range (ι := Unit) (fun _ ↦ A) (fun _ ↦ hA) (by
    rw [iUnion_const, hsurj.range_eq])

/-- The image of a strictly webbed space under a sequentially continuous linear map is strictly
webbed, Köthe II §35.4.(2). -/
theorem StrictlyWebbedSpace.of_surjective [StrictlyWebbedSpace 𝕜 E] (A : E →ₗ[𝕜] F)
    (hA : SeqContinuous A) (hsurj : Surjective A) : StrictlyWebbedSpace 𝕜 F :=
  StrictlyWebbedSpace.of_iUnion_range (ι := Unit) (fun _ ↦ A) (fun _ ↦ hA) (by
    rw [iUnion_const, hsurj.range_eq])

variable [IsTopologicalAddGroup E] (N : Submodule 𝕜 E)

/-- A quotient of a webbed space is webbed, Köthe II §35.4.(3). -/
instance Submodule.Quotient.instWebbedSpace [WebbedSpace E] : WebbedSpace (E ⧸ N) :=
  WebbedSpace.of_surjective (N.mkQ.restrictScalars ℝ) N.continuous_mkQ.seqContinuous
    N.mkQ_surjective

/-- A quotient of a strictly webbed space is strictly webbed, Köthe II §35.4.(3). -/
instance Submodule.Quotient.instStrictlyWebbedSpace [StrictlyWebbedSpace 𝕜 E] :
    StrictlyWebbedSpace 𝕜 (E ⧸ N) :=
  StrictlyWebbedSpace.of_surjective N.mkQ N.continuous_mkQ.seqContinuous N.mkQ_surjective

end Image
