/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Encodable.Basic
public import WebbedSpaces.Hereditary

/-!
# Countable products of webbed spaces

The product of countably many webbed spaces is webbed, and the product of countably many
strictly webbed spaces is strictly webbed,
[G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(6).

Let `C j` be a web on `E j`, for `j` in an encodable type `ι`. The web on `∀ j, E j` constrains
at depth `k` the coordinates `j` with `encode j < k`, the coordinate `j` by a set of depth
`k - encode j` of `C j`. One index `n` of the product web encodes indices for all coordinate
webs at once: `WebConstruction.webPiIndex n m` is the index used by the coordinate `j` with `encode
j = m`.

The explicit web constructions and their calculation lemmas live in the `WebConstruction`
namespace.

## Main definitions

* `WebConstruction.webPiIndex`: decoding of one natural number into a sequence of natural numbers.
* `WebConstruction.webPi C`: the product web.
* `WebConstruction.webProd C₁ C₂`: the product of two webs; one index encodes a pair of indices of
  `C₁` and `C₂`.

## Main statements

* `WebConstruction.isWeb_webPi`, `WebConstruction.isCompletingWeb_webPi`,
  `WebConstruction.isStrictWeb_webPi`: the product web is a web, and it
  is completing, respectively strict, if the webs of the factors are.
* `WebConstruction.isWeb_webProd`, `WebConstruction.isCompletingWeb_webProd`,
  `WebConstruction.isStrictWeb_webProd`: the same for `WebConstruction.webProd`.
* `Pi.instWebbedSpace`, `Pi.instStrictlyWebbedSpace`: countable products of webbed and of strictly
  webbed spaces.
* `WebbedSpace.of_isInducing_pi`, `StrictlyWebbedSpace.of_isInducing_pi`: countable projective
  limits, §35.4.(7).
* `Prod.instWebbedSpace`, `Prod.instStrictlyWebbedSpace`: binary products.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(6)

## Tags

web, webbed space, product
-/

public section

open Set Filter PiNat Function Encodable

open scoped Topology

/-- The `m`-th entry of the sequence of natural numbers encoded by `n` through iterated
unpairing. -/
@[expose]
def WebConstruction.webPiIndex : ℕ → ℕ → ℕ
  | n, 0 => (Nat.unpair n).1
  | n, m + 1 => WebConstruction.webPiIndex (Nat.unpair n).2 m

/-- Every finite sequence of natural numbers is encoded by some natural number. -/
theorem WebConstruction.exists_webPiIndex_eq (a : ℕ → ℕ) (k : ℕ) :
    ∃ n, ∀ m < k, WebConstruction.webPiIndex n m = a m := by
  induction k generalizing a with
  | zero => exact ⟨0, fun m hm ↦ absurd hm (Nat.not_lt_zero m)⟩
  | succ k ih =>
    obtain ⟨n', hn'⟩ := ih fun m ↦ a (m + 1)
    refine ⟨Nat.pair (a 0) n', fun m hm ↦ ?_⟩
    cases m with
    | zero => simp [WebConstruction.webPiIndex]
    | succ m =>
      rw [WebConstruction.webPiIndex, Nat.unpair_pair]
      exact hn' m (Nat.lt_of_succ_lt_succ hm)

section Lists

/-- The list of indices for the coordinate at position `m` that is encoded in a list `l` of
indices of the product web: the newest `l.length - m` entries are used. -/
@[expose]
def WebConstruction.webPiList (l : List ℕ) (m : ℕ) : List ℕ :=
  (l.take (l.length - m)).map (WebConstruction.webPiIndex · m)

/-- Adding an index to a list adds the decoded index to the list of a coordinate that is already
constrained. -/
theorem WebConstruction.webPiList_cons_of_le {l : List ℕ} {m : ℕ} (n : ℕ) (hm : m ≤ l.length) :
    WebConstruction.webPiList (n :: l) m =
      WebConstruction.webPiIndex n m :: WebConstruction.webPiList l m := by
  rw [WebConstruction.webPiList, WebConstruction.webPiList, List.length_cons, Nat.succ_sub hm,
    List.take_succ_cons,
    List.map_cons]

/-- A coordinate at a position beyond the length of the list is not constrained. -/
theorem WebConstruction.webPiList_eq_nil_of_length_le {l : List ℕ} {m : ℕ} (hm : l.length ≤ m) :
    WebConstruction.webPiList l m = [] := by
  rw [WebConstruction.webPiList, Nat.sub_eq_zero_of_le hm, List.take_zero, List.map_nil]

/-- Compatibility name for `WebConstruction.webPiList_eq_nil_of_length_le`. -/
alias WebConstruction.webPiList_of_length_le := WebConstruction.webPiList_eq_nil_of_length_le

/-- The strand of the coordinate at position `m` determined by a strand `σ` of the product
web. -/
@[expose]
def WebConstruction.webPiStrand (σ : ℕ → ℕ) (m : ℕ) : ℕ → ℕ :=
  fun i ↦ WebConstruction.webPiIndex (σ (m + i)) m

/-- The list of a coordinate along a strand of the product web is a restriction of the strand
of that coordinate. -/
theorem WebConstruction.webPiList_res_add (σ : ℕ → ℕ) (m i : ℕ) :
    WebConstruction.webPiList (res σ (m + i)) m = res (WebConstruction.webPiStrand σ m) i := by
  induction i with
  | zero => exact WebConstruction.webPiList_eq_nil_of_length_le (by simp)
  | succ i ih =>
    have h : res σ (m + (i + 1)) = σ (m + i) :: res σ (m + i) := rfl
    rw [h, WebConstruction.webPiList_cons_of_le _ (by simp), ih, res_succ]
    rfl

/-- The list of a coordinate along a strand of the product web, at any depth. -/
theorem WebConstruction.webPiList_res (σ : ℕ → ℕ) (m k : ℕ) :
    WebConstruction.webPiList (res σ k) m = res (WebConstruction.webPiStrand σ m) (k - m) := by
  rcases le_total m k with h | h
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [WebConstruction.webPiList_res_add, Nat.add_sub_cancel_left]
  · rw [WebConstruction.webPiList_eq_nil_of_length_le (by simpa using h), Nat.sub_eq_zero_of_le h, res_zero]

end Lists

section Product

variable {ι : Type*} [Encodable ι] {E : ι → Type*}

/-- The **product web**: at depth `k` it constrains the coordinates `j` with `encode j < k`,
the coordinate `j` by a set of depth `k - encode j` of the web `C j`. -/
@[expose]
def WebConstruction.webPi (C : ∀ j, List ℕ → Set (E j)) (l : List ℕ) : Set (∀ j, E j) :=
  {x | ∀ j, x j ∈ C j (WebConstruction.webPiList l (encode j))}

/-- Membership of the sets of the product web. -/
theorem WebConstruction.mem_webPi {C : ∀ j, List ℕ → Set (E j)} {l : List ℕ} {x : ∀ j, E j} :
    x ∈ WebConstruction.webPi C l ↔ ∀ j, x j ∈ C j (WebConstruction.webPiList l (encode j)) :=
  Iff.rfl

/-- Membership of the sets along a strand of the product web. -/
theorem WebConstruction.mem_webPi_res {C : ∀ j, List ℕ → Set (E j)} {σ : ℕ → ℕ} {k : ℕ} {x : ∀ j, E j} :
    x ∈ WebConstruction.webPi C (res σ k) ↔
      ∀ j, x j ∈ C j (res (WebConstruction.webPiStrand σ (encode j)) (k - encode j)) := by
  simp_rw [WebConstruction.mem_webPi, WebConstruction.webPiList_res]

/-- The product of webs is a web. -/
theorem WebConstruction.isWeb_webPi {C : ∀ j, List ℕ → Set (E j)} (hC : ∀ j, IsWeb (C j)) :
    IsWeb (WebConstruction.webPi C) where
  nil := by
    ext x
    simp only [WebConstruction.mem_webPi, mem_univ, iff_true]
    intro j
    rw [WebConstruction.webPiList_eq_nil_of_length_le (by simp), (hC j).nil]
    exact mem_univ _
  iUnion_cons l := by
    refine Subset.antisymm (iUnion_subset fun n x hx ↦ ?_) fun x hx ↦ ?_
    · intro j
      rcases le_or_gt (encode j) l.length with hj | hj
      · have h := hx j
        rw [WebConstruction.webPiList_cons_of_le n hj] at h
        exact (hC j).cons_subset _ _ h
      · have h := hx j
        rw [WebConstruction.webPiList_eq_nil_of_length_le (by simpa using hj)] at h
        rwa [WebConstruction.webPiList_eq_nil_of_length_le hj.le]
    · -- Choose an index for every coordinate and encode the relevant ones.
      choose b hb using fun j ↦ (hC j).exists_mem_cons (hx j)
      let a : ℕ → ℕ := fun m ↦ (decode (α := ι) m).elim 0 b
      have ha (j : ι) : a (encode j) = b j := by simp [a]
      obtain ⟨n, hn⟩ := WebConstruction.exists_webPiIndex_eq a (l.length + 1)
      refine mem_iUnion.mpr ⟨n, fun j ↦ ?_⟩
      rcases le_or_gt (encode j) l.length with hj | hj
      · rw [WebConstruction.webPiList_cons_of_le n hj, hn _ (Nat.lt_succ_of_le hj), ha]
        exact hb j
      · rw [WebConstruction.webPiList_eq_nil_of_length_le (by simpa using hj)]
        have h := hx j
        rwa [WebConstruction.webPiList_eq_nil_of_length_le hj.le] at h

variable {𝕜 : Type*} [RCLike 𝕜] [∀ j, AddCommGroup (E j)] [∀ j, Module 𝕜 (E j)]
  [∀ j, Module ℝ (E j)] [∀ j, IsScalarTower ℝ 𝕜 (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, ContinuousAdd (E j)]

/-- The radii of the product web along a strand, from radii `r j` of the coordinate webs. -/
private noncomputable def WebConstruction.webPiRadius (r : ι → ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one fun m ↦
    (decode (α := ι) m).elim 1 fun j ↦ r j (k - m)

/-- The radii of the product web are positive. -/
private theorem WebConstruction.webPiRadius_pos {r : ι → ℕ → ℝ} (hr : ∀ j k, 0 < r j k) (k : ℕ) :
    0 < WebConstruction.webPiRadius r k := by
  rw [WebConstruction.webPiRadius, Finset.lt_inf'_iff]
  intro m _
  rcases decode (α := ι) m with _ | j
  · exact one_pos
  · exact hr j _

/-- The radii of the product web are bounded by the radii of each coordinate web. -/
private theorem WebConstruction.webPiRadius_le (r : ι → ℕ → ℝ) (j : ι) (i : ℕ) :
    WebConstruction.webPiRadius r (encode j + i) ≤ r j i := by
  refine (Finset.inf'_le _
    (Finset.mem_range.mpr (by omega : encode j < encode j + i + 1))).trans ?_
  simp

omit [∀ j, AddCommGroup (E j)] [∀ j, Module 𝕜 (E j)] [∀ j, Module ℝ (E j)]
  [∀ j, IsScalarTower ℝ 𝕜 (E j)] [∀ j, TopologicalSpace (E j)] [∀ j, ContinuousAdd (E j)] in
/-- The terms with index at least `encode j` of a sequence in the sets of a strand of the
product web have their `j`-th coordinates in the sets of a strand of the web `C j`. -/
private theorem apply_mem_res {C : ∀ j, List ℕ → Set (E j)} {σ : ℕ → ℕ} {x : ℕ → ∀ j, E j}
    (hx : ∀ k, x k ∈ WebConstruction.webPi C (res σ (k + 1))) (j : ι) (i : ℕ) :
    x (encode j + i) j ∈ C j (res (WebConstruction.webPiStrand σ (encode j)) (i + 1)) := by
  have h := WebConstruction.mem_webPi_res.mp (hx (encode j + i)) j
  rwa [show encode j + i + 1 - encode j = i + 1 by omega] at h

omit [∀ j, Module 𝕜 (E j)] [∀ j, IsScalarTower ℝ 𝕜 (E j)] in
/-- The product of countably many completing webs is a completing web,
Köthe II §35.4.(6). -/
theorem WebConstruction.isCompletingWeb_webPi {C : ∀ j, List ℕ → Set (E j)}
    (hC : ∀ j, IsCompletingWeb (C j)) :
    IsCompletingWeb (WebConstruction.webPi C) where
  toIsWeb := WebConstruction.isWeb_webPi fun j ↦ (hC j).toIsWeb
  exists_radius σ := by
    choose r hr h using fun j ↦ (hC j).exists_radius (WebConstruction.webPiStrand σ (encode j))
    refine ⟨WebConstruction.webPiRadius r, WebConstruction.webPiRadius_pos hr, fun x c hx hc ↦ ?_⟩
    have hj (j : ι) : ∃ s : E j,
        Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c k • x k j) atTop (𝓝 s) := by
      obtain ⟨s, hs⟩ := h j (fun i ↦ x (encode j + i) j) (fun i ↦ c (encode j + i))
        (apply_mem_res hx j) fun i ↦
          ⟨(hc _).1, (hc _).2.trans (WebConstruction.webPiRadius_le r j i)⟩
      exact ⟨_, tendsto_sum_range_of_tendsto_sum_range_add (a := fun k ↦ c k • x k j) hs⟩
    choose s hs using hj
    exact ⟨s, tendsto_sum_pi (y := fun k ↦ c k • x k) hs⟩

omit [∀ j, IsScalarTower ℝ 𝕜 (E j)] in
/-- The product of countably many strict webs is a strict web, Köthe II §35.4.(6). -/
theorem WebConstruction.isStrictWeb_webPi {C : ∀ j, List ℕ → Set (E j)} (hC : ∀ j, IsStrictWeb 𝕜 (C j)) :
    IsStrictWeb 𝕜 (WebConstruction.webPi C) where
  toIsWeb := WebConstruction.isWeb_webPi fun j ↦ (hC j).toIsWeb
  convex l := fun x hx y hy a b ha hb hab j ↦ (hC j).convex _ (hx j) (hy j) ha hb hab
  balanced l := by
    rintro a ha _ ⟨x, hx, rfl⟩ j
    exact (hC j).balanced _ a ha (smul_mem_smul_set (hx j))
  exists_radius σ := by
    choose r hr h using fun j ↦ (hC j).exists_radius (WebConstruction.webPiStrand σ (encode j))
    refine ⟨WebConstruction.webPiRadius r, WebConstruction.webPiRadius_pos hr, fun x c hx hc k₀ ↦ ?_⟩
    have hj (j : ι) : ∃ s ∈ C j (res (WebConstruction.webPiStrand σ (encode j)) (k₀ + 1 - encode j)),
        Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c (k₀ + k) • x (k₀ + k) j) atTop (𝓝 s) := by
      have h' := h j (fun i ↦ x (encode j + i) j) (fun i ↦ c (encode j + i))
        (apply_mem_res hx j) fun i ↦
          ⟨(hc _).1, (hc _).2.trans (WebConstruction.webPiRadius_le r j i)⟩
      rcases le_or_gt (encode j) k₀ with hle | hlt
      · -- The tail from `k₀` is the tail from `k₀ - encode j` of the coordinate series.
        obtain ⟨s, hsC, hs⟩ := h' (k₀ - encode j)
        refine ⟨s, ?_, ?_⟩
        · rwa [show k₀ + 1 - encode j = k₀ - encode j + 1 by omega]
        · refine hs.congr fun N ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [show encode j + (k₀ - encode j + i) = k₀ + i by omega]
      · -- Finitely many terms precede the coordinate series; no constraint on the sum.
        obtain ⟨s, -, hs⟩ := h' 0
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlt.le
        have hs' : Tendsto (fun N ↦ ∑ i ∈ Finset.range N,
            c (k₀ + (m + i)) • x (k₀ + (m + i)) j) atTop (𝓝 s) := by
          refine hs.congr fun N ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [show encode j + (0 + i) = k₀ + (m + i) by omega]
        refine ⟨_, ?_, tendsto_sum_range_of_tendsto_sum_range_add
          (a := fun k ↦ c (k₀ + k) • x (k₀ + k) j) hs'⟩
        rw [show k₀ + 1 - encode j = 0 by omega, res_zero, (hC j).nil]
        exact mem_univ _
    choose s hsC hs using hj
    refine ⟨s, WebConstruction.mem_webPi_res.mpr hsC,
      tendsto_sum_pi (y := fun k ↦ c (k₀ + k) • x (k₀ + k)) hs⟩

end Product

section Instances

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Countable ι] {E : ι → Type*}
  [∀ j, AddCommGroup (E j)] [∀ j, Module 𝕜 (E j)] [∀ j, Module ℝ (E j)]
  [∀ j, IsScalarTower ℝ 𝕜 (E j)] [∀ j, TopologicalSpace (E j)] [∀ j, ContinuousAdd (E j)]

/-- The product of countably many webbed spaces is webbed, Köthe II §35.4.(6). -/
instance Pi.instWebbedSpace [∀ j, WebbedSpace (E j)] : WebbedSpace (∀ j, E j) := by
  have := Encodable.ofCountable ι
  choose C hC using fun j ↦ WebbedSpace.exists_isCompletingWeb (E := E j)
  exact ⟨WebConstruction.webPi C, WebConstruction.isCompletingWeb_webPi hC⟩

/-- The product of countably many strictly webbed spaces is strictly webbed,
Köthe II §35.4.(6). -/
instance Pi.instStrictlyWebbedSpace [∀ j, StrictlyWebbedSpace 𝕜 (E j)] :
    StrictlyWebbedSpace 𝕜 (∀ j, E j) := by
  have := Encodable.ofCountable ι
  choose C hC using fun j ↦ StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := E j)
  exact ⟨WebConstruction.webPi C, WebConstruction.isStrictWeb_webPi hC⟩

variable {H : Type*} [AddCommGroup H] [Module 𝕜 H] [Module ℝ H] [IsScalarTower ℝ 𝕜 H]
  [TopologicalSpace H]

/-- A countable projective limit of webbed spaces is webbed, Köthe II §35.4.(7): if the
topology of `H` is induced by countably many linear maps `g j` into webbed spaces and the range
of `x ↦ (g j x)` is sequentially closed in the product, then `H` is webbed. -/
theorem WebbedSpace.of_isInducing_pi [∀ j, WebbedSpace (E j)] (g : ∀ j, H →ₗ[ℝ] E j)
    (hg : Topology.IsInducing fun x j ↦ g j x) (hr : IsSeqClosed (range fun x j ↦ g j x)) :
    WebbedSpace H :=
  WebbedSpace.of_isInducing (LinearMap.pi g) hg hr

/-- A countable projective limit of strictly webbed spaces is strictly webbed,
Köthe II §35.4.(7). -/
theorem StrictlyWebbedSpace.of_isInducing_pi [∀ j, StrictlyWebbedSpace 𝕜 (E j)]
    (g : ∀ j, H →ₗ[𝕜] E j) (hg : Topology.IsInducing fun x j ↦ g j x)
    (hr : IsSeqClosed (range fun x j ↦ g j x)) : StrictlyWebbedSpace 𝕜 H :=
  StrictlyWebbedSpace.of_isInducing (LinearMap.pi g) hg hr

end Instances

section Prod

variable {E F : Type*}

/-- The **product of two webs**: an index `n` encodes the pair `Nat.unpair n` of indices of the
two webs. -/
@[expose]
def WebConstruction.webProd (C₁ : List ℕ → Set E) (C₂ : List ℕ → Set F) (l : List ℕ) : Set (E × F) :=
  C₁ (l.map fun n ↦ (Nat.unpair n).1) ×ˢ C₂ (l.map fun n ↦ (Nat.unpair n).2)

/-- The sets of the product of two webs along a strand. -/
theorem WebConstruction.webProd_res (C₁ : List ℕ → Set E) (C₂ : List ℕ → Set F) (σ : ℕ → ℕ) (k : ℕ) :
    WebConstruction.webProd C₁ C₂ (res σ k) =
      C₁ (res (fun i ↦ (Nat.unpair (σ i)).1) k) ×ˢ C₂ (res (fun i ↦ (Nat.unpair (σ i)).2) k) := by
  rw [WebConstruction.webProd, res_comp (fun n ↦ (Nat.unpair n).1) σ k,
    res_comp (fun n ↦ (Nat.unpair n).2) σ k]

/-- The product of two webs is a web. -/
theorem WebConstruction.isWeb_webProd {C₁ : List ℕ → Set E} {C₂ : List ℕ → Set F} (h₁ : IsWeb C₁)
    (h₂ : IsWeb C₂) : IsWeb (WebConstruction.webProd C₁ C₂) where
  nil := by rw [WebConstruction.webProd, List.map_nil, List.map_nil, h₁.nil, h₂.nil, univ_prod_univ]
  iUnion_cons l := by
    refine Subset.antisymm (iUnion_subset fun n x hx ↦ ?_) fun x hx ↦ ?_
    · exact ⟨h₁.cons_subset _ _ hx.1, h₂.cons_subset _ _ hx.2⟩
    · obtain ⟨n₁, hn₁⟩ := h₁.exists_mem_cons hx.1
      obtain ⟨n₂, hn₂⟩ := h₂.exists_mem_cons hx.2
      refine mem_iUnion.mpr ⟨Nat.pair n₁ n₂, ?_⟩
      rw [WebConstruction.webProd, List.map_cons, List.map_cons, Nat.unpair_pair]
      exact ⟨hn₁, hn₂⟩

variable {𝕜 : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [TopologicalSpace F]

omit [Module 𝕜 E] [Module 𝕜 F] in
/-- The product of two completing webs is a completing web. -/
theorem WebConstruction.isCompletingWeb_webProd {C₁ : List ℕ → Set E} {C₂ : List ℕ → Set F}
    (h₁ : IsCompletingWeb C₁) (h₂ : IsCompletingWeb C₂) :
    IsCompletingWeb (WebConstruction.webProd C₁ C₂) where
  toIsWeb := WebConstruction.isWeb_webProd h₁.toIsWeb h₂.toIsWeb
  exists_radius σ := by
    obtain ⟨ρ₁, hρ₁, H₁⟩ := h₁.exists_radius fun i ↦ (Nat.unpair (σ i)).1
    obtain ⟨ρ₂, hρ₂, H₂⟩ := h₂.exists_radius fun i ↦ (Nat.unpair (σ i)).2
    refine ⟨fun k ↦ min (ρ₁ k) (ρ₂ k), fun k ↦ lt_min (hρ₁ k) (hρ₂ k), fun x c hx hc ↦ ?_⟩
    have hx' (k : ℕ) := WebConstruction.webProd_res C₁ C₂ σ (k + 1) ▸ hx k
    obtain ⟨s, hs⟩ := H₁ (fun k ↦ (x k).1) c (fun k ↦ (hx' k).1) fun k ↦
      ⟨(hc k).1, (hc k).2.trans (min_le_left _ _)⟩
    obtain ⟨t, ht⟩ := H₂ (fun k ↦ (x k).2) c (fun k ↦ (hx' k).2) fun k ↦
      ⟨(hc k).1, (hc k).2.trans (min_le_right _ _)⟩
    exact ⟨(s, t), tendsto_sum_prod (y := fun k ↦ c k • x k) hs ht⟩

/-- The product of two strict webs is a strict web. -/
theorem WebConstruction.isStrictWeb_webProd {C₁ : List ℕ → Set E} {C₂ : List ℕ → Set F}
    (h₁ : IsStrictWeb 𝕜 C₁) (h₂ : IsStrictWeb 𝕜 C₂) : IsStrictWeb 𝕜 (WebConstruction.webProd C₁ C₂) where
  toIsWeb := WebConstruction.isWeb_webProd h₁.toIsWeb h₂.toIsWeb
  convex l := (h₁.convex _).prod (h₂.convex _)
  balanced l := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨h₁.balanced _ a ha (smul_mem_smul_set hx.1),
      h₂.balanced _ a ha (smul_mem_smul_set hx.2)⟩
  exists_radius σ := by
    obtain ⟨ρ₁, hρ₁, H₁⟩ := h₁.exists_radius fun i ↦ (Nat.unpair (σ i)).1
    obtain ⟨ρ₂, hρ₂, H₂⟩ := h₂.exists_radius fun i ↦ (Nat.unpair (σ i)).2
    refine ⟨fun k ↦ min (ρ₁ k) (ρ₂ k), fun k ↦ lt_min (hρ₁ k) (hρ₂ k),
      fun x c hx hc k₀ ↦ ?_⟩
    have hx' (k : ℕ) := WebConstruction.webProd_res C₁ C₂ σ (k + 1) ▸ hx k
    obtain ⟨s, hsC, hs⟩ := H₁ (fun k ↦ (x k).1) c (fun k ↦ (hx' k).1) (fun k ↦
      ⟨(hc k).1, (hc k).2.trans (min_le_left _ _)⟩) k₀
    obtain ⟨t, htC, ht⟩ := H₂ (fun k ↦ (x k).2) c (fun k ↦ (hx' k).2) (fun k ↦
      ⟨(hc k).1, (hc k).2.trans (min_le_right _ _)⟩) k₀
    refine ⟨(s, t), ?_, tendsto_sum_prod (y := fun k ↦ c (k₀ + k) • x (k₀ + k)) hs ht⟩
    rw [WebConstruction.webProd_res]
    exact ⟨hsC, htC⟩

/-- The product of two webbed spaces is webbed. -/
instance Prod.instWebbedSpace [WebbedSpace E] [WebbedSpace F] : WebbedSpace (E × F) := by
  obtain ⟨C₁, h₁⟩ := WebbedSpace.exists_isCompletingWeb (E := E)
  obtain ⟨C₂, h₂⟩ := WebbedSpace.exists_isCompletingWeb (E := F)
  exact ⟨WebConstruction.webProd C₁ C₂, WebConstruction.isCompletingWeb_webProd h₁ h₂⟩

/-- The product of two strictly webbed spaces is strictly webbed. -/
instance Prod.instStrictlyWebbedSpace [StrictlyWebbedSpace 𝕜 E] [StrictlyWebbedSpace 𝕜 F] :
    StrictlyWebbedSpace 𝕜 (E × F) := by
  obtain ⟨C₁, h₁⟩ := StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := E)
  obtain ⟨C₂, h₂⟩ := StrictlyWebbedSpace.exists_isStrictWeb (𝕜 := 𝕜) (F := F)
  exact ⟨WebConstruction.webProd C₁ C₂, WebConstruction.isStrictWeb_webProd h₁ h₂⟩

end Prod
