/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.CompactHull
public import LocallyConvexSpaces.Completion
public import LocallyConvexSpaces.FinalTopology
public import Mathlib.Analysis.Convex.Join

/-!
# Strict inductive limits of locally convex spaces

A *strict inductive sequence* of locally convex spaces consists of spaces `E n`, continuous
linear maps `j n : E n →L[𝕜] E (n + 1)` that are topological embeddings, and injective linear
maps `f n : E n →ₗ[𝕜] F` into a vector space `F` with `f (n + 1) ∘ j n = f n` whose ranges
cover `F`. The space `F` with the final locally convex topology for the family `f` is the
*strict inductive limit* of the sequence; when every `E n` is a Fréchet space it is a
*strict LF space*. The steps are separate types rather than submodules of `F`, as for the spaces of
test functions in Mathlib (`Mathlib/Analysis/Distribution/TestFunction.lean`).

The limit induces on every step its own topology: each `f n` is a topological embedding.
This rests on the extension lemma for `ℝ`-convex balanced neighbourhoods of zero along a linear
embedding. The limit of complete steps is complete, by separation in its completion.

## Main definitions

* `IsStrictInductiveLimit j f`: the maps `j n` and `f n` form a strict inductive sequence with
  limit space `F`.
* `StrictInductiveLimit.transition`: the composed transition maps `E n → E (n + k)`.

## Main statements

* `ContinuousLinearMap.exists_convex_balanced_nhds_preimage_eq`: if `j : E →L[𝕜] G` is an
  injective linear topological embedding of locally convex spaces and `V` is a `ℝ`-convex balanced
  neighbourhood of zero in `E`, then there is a `ℝ`-convex balanced neighbourhood `W` of zero in `G`
  with `j ⁻¹' W = V`. The variants `…_preimage_eq_subset_add` and `…_preimage_eq_notMem` in
  addition make `W ⊆ j '' V + N` for a given neighbourhood `N`, respectively `p ∉ W` for a
  given point `p` outside the closed range of `j`.
* `IsStrictInductiveLimit.exists_nhds_preimage_eq`: a `ℝ`-convex balanced neighbourhood of zero in a
  step `E n` is the preimage of a neighbourhood of zero of the limit.
* `IsStrictInductiveLimit.isInducing`: every `f n` is inducing for the final locally convex
  topology; with injectivity, `IsStrictInductiveLimit.isEmbedding`.
* `IsStrictInductiveLimit.t2Space`: a strict inductive limit of Hausdorff spaces is Hausdorff.
* `IsStrictInductiveLimit.isClosed_range`: if every step is closed in the next one, then every
  step is closed in the limit.
* `IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded`: the **Dieudonné–Schwartz
  theorem**: under the same hypothesis every bounded subset of the limit lies in a step. The
  proof separates points outside the steps by functionals that vanish on the steps, instead of
  the usual recursive construction of a neighbourhood.
* `IsStrictInductiveLimit.exists_subset_range_and_isVonNBounded_preimage`: a bounded set is
  contained and bounded in one step when the transition ranges are closed.
* `IsStrictInductiveLimit.completeSpace`: a countable strict inductive limit of complete
  locally convex spaces is complete, without metrizability or separation hypotheses.

Barrelledness, bornologicity and ultrabornologicity of the limit are instances of the general
statements `locallyConvexFinalTopology.barrelledSpace`,
`locallyConvexFinalTopology.bornologicalSpace` and
`locallyConvexFinalTopology.ultrabornologicalSpace`; in particular a strict LF space (a strict
inductive limit of Fréchet spaces) is barrelled, bornological and ultrabornological.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §6.4–6.6
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §4.6
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §19.4

## Tags

strict inductive limit, LF space, inductive limit, locally convex space
-/

public section

open Set Filter Function

open scoped Topology Pointwise

section Extension

variable {𝕜 E G : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [AddCommGroup G] [Module 𝕜 G] [Module ℝ G] [IsScalarTower ℝ 𝕜 G] [TopologicalSpace G]
  [ContinuousSMul 𝕜 G] [LocallyConvexSpace ℝ G]

/-- The extension lemma for neighbourhoods, with control of the size of the extension. Let
`j : E →L[𝕜] G` be an injective linear map that is a topological embedding into a locally convex
space, let `V` be a `ℝ`-convex balanced neighbourhood of zero in `E` and `N` a neighbourhood of zero
in `G`. Then there is a `ℝ`-convex balanced neighbourhood `W` of zero in `G` with `j ⁻¹' W = V` and
`W ⊆ j '' V + N`. -/
theorem ContinuousLinearMap.exists_convex_balanced_nhds_preimage_eq_subset_add
    (j : E →L[𝕜] G) (hj : Topology.IsInducing j) (hinj : Injective j) {V : Set E}
    (hV : V ∈ 𝓝 (0 : E)) (hVc : Convex ℝ V) (hVb : Balanced 𝕜 V) {N : Set G}
    (hN : N ∈ 𝓝 (0 : G)) :
    ∃ W : Set G, W ∈ 𝓝 (0 : G) ∧ Convex ℝ W ∧ Balanced 𝕜 W ∧ j ⁻¹' W = V ∧
      W ⊆ j '' V + N := by
  -- A convex balanced neighbourhood `W₀ ⊆ N` of zero in `G` with `j ⁻¹' W₀ ⊆ V`.
  rw [hj.nhds_eq_comap, map_zero] at hV
  obtain ⟨W₁, hW₁, hW₁V⟩ := mem_comap.mp hV
  obtain ⟨W₀, ⟨hW₀, hW₀c, hW₀b⟩, hW₀W₁N⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 G).mem_iff.mp (inter_mem hW₁ hN)
  have hW₀W₁ : W₀ ⊆ W₁ := hW₀W₁N.trans inter_subset_left
  have hW₀N : W₀ ⊆ N := hW₀W₁N.trans inter_subset_right
  have hW₀V : j ⁻¹' W₀ ⊆ V := (preimage_mono hW₀W₁).trans hW₁V
  have h0V : (0 : E) ∈ V := hW₀V (by simpa using mem_of_mem_nhds hW₀)
  have hjVc : Convex ℝ (j '' V) := hVc.is_linear_image (j.toLinearMap.restrictScalars ℝ).isLinear
  have hjVb : Balanced 𝕜 (j '' V) := hVb.image j.toLinearMap
  have hjoin : convexHull ℝ (j '' V ∪ W₀) = convexJoin ℝ (j '' V) W₀ :=
    hjVc.convexHull_union hW₀c ⟨j 0, 0, h0V, rfl⟩ ⟨0, mem_of_mem_nhds hW₀⟩
  refine ⟨convexHull ℝ (j '' V ∪ W₀),
    mem_of_superset hW₀ (subset_union_right.trans (subset_convexHull ℝ _)),
    convex_convexHull ℝ _, (hjVb.union hW₀b).convexHull_real, Subset.antisymm ?_ ?_, ?_⟩
  · -- A point of `j ⁻¹' W` is a convex combination of a point of `V` and a point of `j ⁻¹' W₀`.
    intro x hx
    rw [mem_preimage, hjoin, mem_convexJoin] at hx
    obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb, hab, hx⟩ := hx
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · -- `b = 0`, so `j x = j v`.
      have ha1 : a = 1 := by linarith
      rw [← hb0, ha1, one_smul, zero_smul, add_zero] at hx
      exact hinj hx ▸ hv
    · -- `b > 0`, so `w` lies in the range of `j`.
      let u : E := b⁻¹ • (x - a • v)
      have hju : j u = w := by
        have h1 : j u = b⁻¹ • (j x - a • j v) := by
          simp only [u]
          rw [j.map_smul_of_tower, map_sub, j.map_smul_of_tower]
        rw [h1, ← hx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hbpos.ne', one_smul]
      have huV : u ∈ V := hW₀V (by rwa [mem_preimage, hju])
      have hxeq : x = a • v + b • u := by
        simp only [u]
        rw [smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
        abel
      rw [hxeq]
      exact hVc hv huV ha hb hab
  · exact fun x hx ↦ subset_convexHull ℝ _ (Or.inl ⟨x, hx, rfl⟩)
  · -- A point `a • j v + b • w` of the join lies in `j '' V + W₀`.
    intro y hy
    rw [hjoin, mem_convexJoin] at hy
    obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb, hab, rfl⟩ := hy
    refine ⟨j (a • v), ⟨a • v, ?_, rfl⟩, b • w, hW₀N ?_, by rw [j.map_smul_of_tower]⟩
    · have h := hVc hv h0V ha hb hab
      rwa [smul_zero, add_zero] at h
    · have h := hW₀c (mem_of_mem_nhds hW₀) hw ha hb hab
      rwa [smul_zero, zero_add] at h

/-- The extension lemma for neighbourhoods. Let `j : E →L[𝕜] G` be an injective linear map that
is a topological embedding into a locally convex space, and let `V` be a `ℝ`-convex balanced
neighbourhood of zero in `E`. Then there is a `ℝ`-convex balanced neighbourhood `W` of zero in `G`
with `j ⁻¹' W = V`. -/
theorem ContinuousLinearMap.exists_convex_balanced_nhds_preimage_eq (j : E →L[𝕜] G)
    (hj : Topology.IsInducing j) (hinj : Injective j) {V : Set E} (hV : V ∈ 𝓝 (0 : E))
    (hVc : Convex ℝ V) (hVb : Balanced 𝕜 V) :
    ∃ W : Set G, W ∈ 𝓝 (0 : G) ∧ Convex ℝ W ∧ Balanced 𝕜 W ∧ j ⁻¹' W = V := by
  obtain ⟨W, h1, h2, h3, h4, -⟩ :=
    j.exists_convex_balanced_nhds_preimage_eq_subset_add hj hinj hV hVc hVb univ_mem
  exact ⟨W, h1, h2, h3, h4⟩

/-- The extension lemma for neighbourhoods, avoiding a point. If in addition the range of `j` is
closed and `p` does not lie in it, the neighbourhood `W` with `j ⁻¹' W = V` can be chosen so
that `p ∉ W`. -/
theorem ContinuousLinearMap.exists_convex_balanced_nhds_preimage_eq_notMem
    [IsTopologicalAddGroup G] (j : E →L[𝕜] G)
    (hj : Topology.IsInducing j) (hinj : Injective j) (hcl : IsClosed (range j)) {V : Set E}
    (hV : V ∈ 𝓝 (0 : E)) (hVc : Convex ℝ V) (hVb : Balanced 𝕜 V) {p : G} (hp : p ∉ range j) :
    ∃ W : Set G, W ∈ 𝓝 (0 : G) ∧ Convex ℝ W ∧ Balanced 𝕜 W ∧ j ⁻¹' W = V ∧ p ∉ W := by
  -- A neighbourhood `N` of zero such that `p - N` does not meet the range of `j`.
  have hN : {w : G | p - w ∈ (range j)ᶜ} ∈ 𝓝 (0 : G) := by
    have hc : ContinuousAt (fun w : G ↦ p - w) 0 := by fun_prop
    exact hc.preimage_mem_nhds (hcl.isOpen_compl.mem_nhds (by simpa using hp))
  obtain ⟨W, h1, h2, h3, h4, h5⟩ :=
    j.exists_convex_balanced_nhds_preimage_eq_subset_add hj hinj hV hVc hVb hN
  refine ⟨W, h1, h2, h3, h4, fun hpW ↦ ?_⟩
  obtain ⟨_, ⟨v, -, rfl⟩, w, hw, hvw⟩ := h5 hpW
  exact hw ⟨v, by rw [← hvw, add_sub_cancel_right]⟩

end Extension

namespace StrictInductiveLimit

section Transition

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [AddCommGroup F] [Module 𝕜 F]
  (j : ∀ n, E n →L[𝕜] E (n + 1)) (f : ∀ n, E n →ₗ[𝕜] F)

/-- Every element of the range of `f m` lies in the range of `f (m + d)`. -/
theorem exists_apply_eq (hf : ∀ n x, f (n + 1) (j n x) = f n x) (d m : ℕ) (y : E m) :
    ∃ y' : E (m + d), f (m + d) y' = f m y := by
  induction d with
  | zero => exact ⟨y, rfl⟩
  | succ d ih =>
    obtain ⟨y', hy'⟩ := ih
    exact ⟨j (m + d) y', (hf (m + d) y').trans hy'⟩

/-- If the preimage of `U` under `f (m + d)` is a neighbourhood of zero, then so is the preimage
under `f m`. -/
theorem preimage_mem_nhds_of_add (hf : ∀ n x, f (n + 1) (j n x) = f n x) {U : Set F}
    (d m : ℕ) (h : f (m + d) ⁻¹' U ∈ 𝓝 (0 : E (m + d))) : f m ⁻¹' U ∈ 𝓝 (0 : E m) := by
  induction d with
  | zero => exact h
  | succ d ih =>
    refine ih ?_
    have hpre : f (m + d) ⁻¹' U = j (m + d) ⁻¹' (f (m + d + 1) ⁻¹' U) := by
      ext x
      simp only [mem_preimage, hf]
    rw [hpre]
    have h' : f (m + d + 1) ⁻¹' U ∈ 𝓝 (j (m + d) 0) := by
      rw [map_zero]
      exact h
    exact (j (m + d)).continuous.continuousAt.preimage_mem_nhds h'

/-- The transition map `E n → E (n + k)` of an inductive sequence: the composition of the maps
`j n`, `j (n + 1)`, …, `j (n + k - 1)`. -/
@[expose]
def transition (n : ℕ) : ∀ k, E n → E (n + k) := fun k ↦
  Nat.rec (motive := fun k ↦ E n → E (n + k)) id (fun k Tk x ↦ j (n + k) (Tk x)) k

/-- The transition map over zero steps is the identity. -/
@[simp]
theorem transition_zero (n : ℕ) (x : E n) : transition j n 0 x = x :=
  rfl

/-- The transition map over `k + 1` steps. -/
@[simp]
theorem transition_succ (n k : ℕ) (x : E n) :
    transition j n (k + 1) x = j (n + k) (transition j n k x) :=
  rfl

/-- The maps into the limit are compatible with the transition maps. -/
theorem apply_transition (hf : ∀ n x, f (n + 1) (j n x) = f n x) (n k : ℕ) (x : E n) :
    f (n + k) (transition j n k x) = f n x := by
  induction k with
  | zero => rfl
  | succ k ih => exact (hf (n + k) (transition j n k x)).trans ih

/-- The ranges of the maps into the limit increase. -/
theorem range_mono (hf : ∀ n x, f (n + 1) (j n x) = f n x) {m n : ℕ} (hmn : m ≤ n) :
    range (f m) ⊆ range (f n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rintro _ ⟨x, rfl⟩
  exact ⟨transition j m d x, apply_transition j f hf m d x⟩

/-- If every `j n` is a closed embedding, then the range of every transition map is closed. -/
theorem isClosed_range_transition (hj : ∀ n, Topology.IsClosedEmbedding (j n)) (n k : ℕ) :
    IsClosed (range (transition j n k)) := by
  induction k with
  | zero =>
    have h : range (transition j n 0) = univ := range_eq_univ.mpr fun x ↦ ⟨x, rfl⟩
    rw [h]
    exact isClosed_univ
  | succ k ih =>
    have h : range (transition j n (k + 1)) = j (n + k) '' range (transition j n k) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨transition j n k x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [h]
    exact (hj (n + k)).isClosedMap _ ih

end Transition

end StrictInductiveLimit

section Structure

variable {𝕜 : Type*} [Semiring 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommMonoid (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [AddCommMonoid F] [Module 𝕜 F]

/-- A **strict inductive sequence** with limit space `F`: continuous linear maps
`j n : E n →L[𝕜] E (n + 1)` that are topological embeddings, together with injective linear maps
`f n : E n →ₗ[𝕜] F` that are compatible with the maps `j n` and whose ranges cover `F`. The
*strict inductive limit* is `F` with the final locally convex topology
`locallyConvexFinalTopology f`; that topology is not part of this structure. -/
structure IsStrictInductiveLimit (j : ∀ n, E n →L[𝕜] E (n + 1)) (f : ∀ n, E n →ₗ[𝕜] F) :
    Prop where
  /-- Every step is topologically embedded in the next one. -/
  isEmbedding_step : ∀ n, Topology.IsEmbedding (j n)
  /-- The maps into `F` are compatible with the steps. -/
  apply_step : ∀ n x, f (n + 1) (j n x) = f n x
  /-- The maps into `F` are injective. -/
  injective : ∀ n, Injective (f n)
  /-- The ranges of the maps into `F` cover `F`. -/
  exists_apply_eq : ∀ y : F, ∃ n x, f n x = y

end Structure

namespace IsStrictInductiveLimit

open StrictInductiveLimit

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
  [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [∀ n, IsTopologicalAddGroup (E n)] [∀ n, ContinuousSMul 𝕜 (E n)]
  [∀ n, LocallyConvexSpace ℝ (E n)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  (j : ∀ n, E n →L[𝕜] E (n + 1)) (f : ∀ n, E n →ₗ[𝕜] F)

variable {j f} (h : IsStrictInductiveLimit j f)

include h in
/-- In a strict inductive limit, every `ℝ`-convex balanced neighbourhood `V` of zero in a step
`E n` is the preimage under `f n` of a neighbourhood of zero of the limit. -/
theorem exists_nhds_preimage_eq (n : ℕ) {V : Set (E n)} (hV : V ∈ 𝓝 (0 : E n))
    (hVc : Convex ℝ V) (hVb : Balanced 𝕜 V) :
    ∃ U : Set F, U ∈ @nhds F (locallyConvexFinalTopology f) 0 ∧ f n ⁻¹' U = V := by
  -- Extend `V` step by step to neighbourhoods `A k` of zero in `E (n + k)`.
  let P : ∀ k, Set (E (n + k)) → Prop := fun k W ↦
    W ∈ 𝓝 (0 : E (n + k)) ∧ Convex ℝ W ∧ Balanced 𝕜 W
  have step (k : ℕ) (W : Set (E (n + k))) (hW : P k W) :
      ∃ W' : Set (E (n + k + 1)), P (k + 1) W' ∧ j (n + k) ⁻¹' W' = W := by
    obtain ⟨W', h1, h2, h3, h4⟩ :=
      (j (n + k)).exists_convex_balanced_nhds_preimage_eq (h.isEmbedding_step (n + k)).isInducing
        (h.isEmbedding_step (n + k)).injective hW.1 hW.2.1 hW.2.2
    exact ⟨W', ⟨h1, h2, h3⟩, h4⟩
  let A : ∀ k, {W : Set (E (n + k)) // P k W} := fun k ↦
    Nat.rec (motive := fun k ↦ {W : Set (E (n + k)) // P k W}) ⟨V, hV, hVc, hVb⟩
      (fun k W ↦ ⟨Classical.choose (step k W.1 W.2), (Classical.choose_spec (step k W.1 W.2)).1⟩)
      k
  have hA (k : ℕ) : j (n + k) ⁻¹' (A (k + 1)).1 = (A k).1 :=
    (Classical.choose_spec (step k (A k).1 (A k).2)).2
  -- The transition maps `T k : E n → E (n + k)`.
  let T : ∀ k, E n → E (n + k) := fun k ↦
    Nat.rec (motive := fun k ↦ E n → E (n + k)) id (fun k Tk x ↦ j (n + k) (Tk x)) k
  have hT (k : ℕ) (x : E n) : f (n + k) (T k x) = f n x := by
    induction k with
    | zero => rfl
    | succ k ih => exact (h.apply_step (n + k) (T k x)).trans ih
  have hTA (k : ℕ) (x : E n) (hx : T k x ∈ (A k).1) : x ∈ V := by
    induction k with
    | zero => exact hx
    | succ k ih =>
      refine ih ?_
      rw [← hA k]
      exact hx
  -- The union `U` of the images of the `A k`.
  let U : Set F := ⋃ k, f (n + k) '' (A k).1
  have hmono : Monotone fun k ↦ f (n + k) '' (A k).1 := monotone_nat_of_le_succ fun k ↦ by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨j (n + k) x, ?_, h.apply_step (n + k) x⟩
    have : x ∈ j (n + k) ⁻¹' (A (k + 1)).1 := by rwa [hA k]
    exact this
  have hUc : Convex ℝ U := hmono.directed_le.convex_iUnion fun k ↦
    (A k).2.2.1.is_linear_image ((f (n + k)).restrictScalars ℝ).isLinear
  have hUb : Balanced 𝕜 U := balanced_iUnion fun k ↦ (A k).2.2.2.image (f (n + k))
  have hUpre (k : ℕ) : f (n + k) ⁻¹' U ∈ 𝓝 (0 : E (n + k)) :=
    mem_of_superset (A k).2.1 fun x hx ↦ mem_iUnion.mpr ⟨k, x, hx, rfl⟩
  have hUpre' (m : ℕ) : f m ⁻¹' U ∈ 𝓝 (0 : E m) := by
    refine preimage_mem_nhds_of_add j f h.apply_step n m ?_
    have h := hUpre m
    rwa [Nat.add_comm n m] at h
  have hUabs : Absorbent 𝕜 U := by
    intro y
    obtain ⟨m, x, rfl⟩ := h.exists_apply_eq y
    have hx : Absorbs 𝕜 (f m ⁻¹' U) {x} := absorbent_nhds_zero (hUpre' m) x
    refine Filter.Eventually.mono hx fun c hc ↦ ?_
    rw [singleton_subset_iff] at hc ⊢
    obtain ⟨z, hz, hzx⟩ := hc
    exact ⟨f m z, hz, by rw [← hzx]; exact (map_smul (f m) c z).symm⟩
  refine ⟨U, locallyConvexFinalTopology.mem_nhds_zero f hUc hUb hUabs hUpre',
    Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨k, w, hw, hwx⟩ := mem_iUnion.mp hx
    have h1 : T k x = w := (h.injective (n + k) (hwx.trans (hT k x).symm)).symm
    exact hTA k x (h1 ▸ hw)
  · exact fun x hx ↦ mem_iUnion.mpr ⟨0, x, hx, rfl⟩

include h in
/-- In a strict inductive limit the final locally convex topology induces on every step its
own topology: each `f n` is inducing. -/
theorem isInducing (n : ℕ) :
    @Topology.IsInducing (E n) F _ (locallyConvexFinalTopology f) (f n) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  have hcont : Continuous (f n) := locallyConvexFinalTopology.continuous_apply f n
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm ?_ fun V hV ↦ ?_
  · have h := hcont.tendsto 0
    rw [map_zero] at h
    exact map_le_iff_le_comap.mp h
  · obtain ⟨V', ⟨hV', hV'c, hV'b⟩, hV'V⟩ :=
      (nhds_zero_hasBasis_convex_balanced 𝕜 (E n)).mem_iff.mp hV
    obtain ⟨U, hU, hUV'⟩ := h.exists_nhds_preimage_eq n hV' hV'c hV'b
    exact mem_comap.mpr ⟨U, hU, hUV'.subset.trans hV'V⟩

include h in
/-- In a strict inductive limit every step is topologically embedded in the limit. -/
theorem isEmbedding (n : ℕ) :
    @Topology.IsEmbedding (E n) F _ (locallyConvexFinalTopology f) (f n) :=
  @Topology.IsEmbedding.mk _ _ _ (locallyConvexFinalTopology f) _
    (h.isInducing n) (h.injective n)

include h in
/-- A strict inductive limit of Hausdorff locally convex spaces is Hausdorff. -/
theorem t2Space [∀ n, T2Space (E n)] : @T2Space F (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun y hy ↦ ?_
  obtain ⟨n, x, rfl⟩ := h.exists_apply_eq y
  have hx : x ≠ 0 := fun h ↦ hy (by rw [h, map_zero])
  -- A convex balanced neighbourhood of zero in `E n` that does not contain `x`.
  have hV : ({x}ᶜ : Set (E n)) ∈ 𝓝 (0 : E n) := isOpen_compl_singleton.mem_nhds (Ne.symm hx)
  obtain ⟨V, ⟨hV', hVc, hVb⟩, hVx⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 (E n)).mem_iff.mp hV
  obtain ⟨U, hU, hUV⟩ := h.exists_nhds_preimage_eq n hV' hVc hVb
  refine ⟨U, hU, fun hyU ↦ ?_⟩
  have hxV : x ∈ V := by
    rw [← hUV]
    exact hyU
  exact hVx hxV rfl

variable (hjcl : ∀ n, IsClosed (range (j n)))

include h hjcl in
/-- If every step of a strict inductive sequence is closed in the next one, then every step is
closed in the limit. -/
theorem isClosed_range (n : ℕ) : @IsClosed F (locallyConvexFinalTopology f) (range (f n)) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  have hjce (m : ℕ) : Topology.IsClosedEmbedding (j m) := ⟨h.isEmbedding_step m, hjcl m⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨m, x, rfl⟩ := h.exists_apply_eq y
  -- The point lies in a later step, outside the closed range of the transition map.
  rcases le_total m n with hmn | hnm
  · exact absurd (range_mono j f h.apply_step hmn ⟨x, rfl⟩) hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hx : x ∉ range (transition j n k) := by
    rintro ⟨z, rfl⟩
    exact hy ⟨z, (apply_transition j f h.apply_step n k z).symm⟩
  have hN : {v : E (n + k) | x - v ∈ (range (transition j n k))ᶜ} ∈ 𝓝 (0 : E (n + k)) := by
    have hc : ContinuousAt (fun v : E (n + k) ↦ x - v) 0 := by fun_prop
    exact hc.preimage_mem_nhds
      ((isClosed_range_transition j hjce n k).isOpen_compl.mem_nhds (by simpa using hx))
  obtain ⟨V, ⟨hV, hVc, hVb⟩, hVN⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 (E (n + k))).mem_iff.mp hN
  obtain ⟨U, hU, hUV⟩ := h.exists_nhds_preimage_eq (n + k) hV hVc hVb
  -- The neighbourhood `y - U` of `y` does not meet the range of `f n`.
  have hyU : {y' : F | f (n + k) x - y' ∈ U} ∈ 𝓝 (f (n + k) x) := by
    have hc : ContinuousAt (fun y' : F ↦ f (n + k) x - y') (f (n + k) x) := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hU)
  refine mem_of_superset hyU ?_
  rintro _ hy' ⟨z, rfl⟩
  have h2 : f (n + k) (x - transition j n k z) ∈ U := by
    rw [map_sub, apply_transition j f h.apply_step n k z]
    exact hy'
  have h3 : x - transition j n k z ∈ V := by
    rw [← hUV]
    exact h2
  exact hVN h3 ⟨z, by abel⟩

include h hjcl in
/-- The **Dieudonné–Schwartz theorem**: in a strict inductive limit in which every step is
closed in the next one, every bounded set is contained in a step. -/
theorem exists_subset_range_of_isVonNBounded {B : Set F}
    (hB : @Bornology.IsVonNBounded 𝕜 F _ _ _ (locallyConvexFinalTopology f) B) :
    ∃ n, B ⊆ range (f n) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := locallyConvexFinalTopology.isTopologicalAddGroup f
  have h2 : ContinuousSMul 𝕜 F := locallyConvexFinalTopology.continuousSMul f
  have h3 : LocallyConvexSpace ℝ F := locallyConvexFinalTopology.locallyConvexSpace f
  by_contra hcon
  push Not at hcon
  -- Points `y n ∈ B` outside the `n`-th step, and functionals `φ n` that vanish on the `n`-th
  -- step but not at `y n`.
  have hex (n : ℕ) : ∃ y ∈ B, y ∉ range (f n) := Set.not_subset.mp (hcon n)
  choose y hyB hy using hex
  have hφ (n : ℕ) : ∃ φ : StrongDual 𝕜 F, (∀ z ∈ range (f n), φ z = 0) ∧ φ (y n) ≠ 0 := by
    obtain ⟨φ, hφ, hφy⟩ := StrongDual.exists_mem_polar_one_lt_norm (𝕜 := 𝕜)
      ((LinearMap.range (f n)).restrictScalars ℝ).convex (LinearMap.range (f n)).balanced
      (h.isClosed_range hjcl n) ⟨0, (LinearMap.range (f n)).zero_mem⟩
      (hy n)
    refine ⟨φ, fun z hz ↦ ?_, fun h0 ↦ ?_⟩
    · exact LinearMap.eq_zero_of_forall_norm_le_one (Q := LinearMap.range (f n))
        (φ := φ.toLinearMap) hφ hz
    · rw [h0, norm_zero] at hφy
      linarith
  choose φ hφ0 hφy using hφ
  -- The set `U` is a neighbourhood of zero of the limit.
  let U : Set F := {z | ∀ n : ℕ, ‖φ n z‖ ≤ ‖φ n (y n)‖ / (n + 1)}
  have hUeq : U = ⋂ n : ℕ, (φ n) ⁻¹' Metric.closedBall (0 : 𝕜) (‖φ n (y n)‖ / (n + 1)) := by
    ext z
    simp [U]
  have hUc : Convex ℝ U := by
    rw [hUeq]
    exact convex_iInter fun n ↦ (convex_closedBall (0 : 𝕜) _).is_linear_preimage
      ((φ n).toLinearMap.restrictScalars ℝ).isLinear
  have hUb : Balanced 𝕜 U := by
    rw [hUeq]
    exact balanced_iInter fun n ↦ (balanced_closedBall_zero).preimage (φ n).toLinearMap
  have hUpre (m : ℕ) : f m ⁻¹' U ∈ 𝓝 (0 : E m) := by
    -- Only the functionals `φ n` with `n < m` give a condition on the `m`-th step.
    have hfin : (⋂ n ∈ Finset.range m,
        {x : E m | ‖φ n (f m x)‖ ≤ ‖φ n (y n)‖ / (n + 1)}) ∈ 𝓝 (0 : E m) := by
      refine (Filter.biInter_finset_mem _).mpr fun n _ ↦ ?_
      have hc : Continuous fun x : E m ↦ ‖φ n (f m x)‖ :=
        ((φ n).continuous.comp (locallyConvexFinalTopology.continuous_apply f m)).norm
      have hpos : 0 < ‖φ n (y n)‖ / (n + 1) :=
        div_pos (norm_pos_iff.mpr (hφy n)) (by positivity)
      have hopen : IsOpen {x : E m | ‖φ n (f m x)‖ < ‖φ n (y n)‖ / (n + 1)} :=
        isOpen_lt hc continuous_const
      refine mem_of_superset (hopen.mem_nhds ?_) fun x hx ↦ ?_
      · simpa using hpos
      · have hx' : ‖φ n (f m x)‖ < ‖φ n (y n)‖ / (n + 1) := hx
        exact hx'.le
    refine mem_of_superset hfin fun x hx n ↦ ?_
    rcases lt_or_ge n m with hnm | hmn
    · exact (mem_iInter₂.mp hx) n (Finset.mem_range.mpr hnm)
    · rw [hφ0 n _ (range_mono j f h.apply_step hmn ⟨x, rfl⟩), norm_zero]
      exact div_nonneg (norm_nonneg _) (by positivity)
  have hUabs : Absorbent 𝕜 U := by
    intro z
    obtain ⟨m, x, rfl⟩ := h.exists_apply_eq z
    have hx : Absorbs 𝕜 (f m ⁻¹' U) {x} := absorbent_nhds_zero (hUpre m) x
    refine Filter.Eventually.mono hx fun c hc ↦ ?_
    rw [singleton_subset_iff] at hc ⊢
    obtain ⟨w, hw, hwx⟩ := hc
    exact ⟨f m w, hw, by rw [← hwx]; exact (map_smul (f m) c w).symm⟩
  have hU : U ∈ 𝓝 (0 : F) := locallyConvexFinalTopology.mem_nhds_zero f hUc hUb hUabs hUpre
  -- `B` is absorbed by `U`, which bounds `n + 1` by a fixed number for all `n`.
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hB hU)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (max r 0)
  have hcr : r ≤ ‖c‖ := (le_max_left _ _).trans hc.le
  have hcpos : 0 < ‖c‖ := (le_max_right _ _).trans_lt hc
  obtain ⟨n, hn⟩ := exists_nat_gt ‖c‖
  obtain ⟨z, hz, hzy⟩ := hr c hcr (hyB n)
  have h4 : ‖φ n (y n)‖ ≤ ‖c‖ * (‖φ n (y n)‖ / (n + 1)) := by
    have hzy' : c • z = y n := hzy
    have heq : ‖φ n (y n)‖ = ‖c‖ * ‖φ n z‖ := by rw [← hzy', map_smul, norm_smul]
    exact heq.le.trans (mul_le_mul_of_nonneg_left (hz n) hcpos.le)
  have hpos : 0 < ‖φ n (y n)‖ := norm_pos_iff.mpr (hφy n)
  have h5 : (n : ℝ) + 1 ≤ ‖c‖ := by
    have h6 : ‖φ n (y n)‖ * ((n : ℝ) + 1) ≤ ‖c‖ * ‖φ n (y n)‖ := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      calc ‖φ n (y n)‖ * ((n : ℝ) + 1) ≤ ‖c‖ * (‖φ n (y n)‖ / (n + 1)) * (n + 1) :=
            mul_le_mul_of_nonneg_right h4 hn1.le
        _ = ‖c‖ * ‖φ n (y n)‖ := by field_simp
    have h7 : ‖φ n (y n)‖ * ((n : ℝ) + 1) ≤ ‖φ n (y n)‖ * ‖c‖ := by rwa [mul_comm ‖c‖] at h6
    exact le_of_mul_le_mul_left h7 hpos
  linarith

include h hjcl in
/-- In a countable strict inductive limit with closed transition ranges, a bounded set is
contained in one step and its preimage is bounded in that step's own topology. -/
theorem exists_subset_range_and_isVonNBounded_preimage {B : Set F}
    (hB : @Bornology.IsVonNBounded 𝕜 F _ _ _ (locallyConvexFinalTopology f) B) :
    ∃ n, B ⊆ range (f n) ∧ Bornology.IsVonNBounded 𝕜 (f n ⁻¹' B) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  obtain ⟨n, hn⟩ := h.exists_subset_range_of_isVonNBounded hjcl hB
  exact ⟨n, hn, hB.preimage_of_isInducing (f n) (h.isInducing n)⟩

end IsStrictInductiveLimit


namespace IsStrictInductiveLimit

open StrictInductiveLimit

section Completeness

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
  [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, UniformSpace (E n)]
  [∀ n, IsUniformAddGroup (E n)] [∀ n, ContinuousSMul 𝕜 (E n)]
  [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [uF : UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]

/-- A countable strict inductive limit of complete locally convex spaces is complete.
No metrizability or separation assumption is needed. This is the
completeness theorem of Schaefer–Wolff, II §6.6, by separating a hypothetical new point of
its completion from the complete steps. In particular it applies to strict LF spaces. -/
theorem completeSpace {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F}
    (h : IsStrictInductiveLimit j f)
    (hFtop : uF.toTopologicalSpace = locallyConvexFinalTopology f) :
    CompleteSpace F := by
  let : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  let : UniformContinuousConstSMul 𝕜 F :=
    uniformContinuousConstSMul_of_continuousConstSMul 𝕜 F
  let : UniformContinuousConstSMul ℝ F :=
    uniformContinuousConstSMul_of_continuousConstSMul ℝ F
  let : LocallyConvexSpace ℝ F := by
    exact hFtop.symm ▸ locallyConvexFinalTopology.locallyConvexSpace f
  let c := UniformSpace.Completion.coeCLM 𝕜 F
  have hfi (n : ℕ) : Topology.IsInducing (f n) := by
    exact hFtop.symm ▸ h.isInducing n
  let g (n : ℕ) : E n →L[𝕜] UniformSpace.Completion F :=
    c.comp { f n with cont := (hfi n).continuous }
  have hg (n : ℕ) : IsClosed (range (g n)) :=
    ((UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 F).comp
      (AddMonoidHom.isUniformInducing_of_isInducing (hfi n))).isComplete_range.isClosed
  suffices hs : Surjective c from
    ((UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 F).completeSpace_congr hs).mpr
      inferInstance
  intro z
  by_contra hz
  have hψ (n : ℕ) : ∃ ψ : StrongDual 𝕜 (UniformSpace.Completion F),
      (∀ w ∈ range (g n), ψ w = 0) ∧ ψ z ≠ 0 := by
    obtain ⟨ψ, hψ, hψz⟩ := StrongDual.exists_mem_polar_one_lt_norm (𝕜 := 𝕜)
      ((LinearMap.range (g n).toLinearMap).restrictScalars ℝ).convex
      (LinearMap.range (g n).toLinearMap).balanced (hg n)
      ⟨0, (LinearMap.range (g n).toLinearMap).zero_mem⟩
      (fun ⟨x, hx⟩ ↦ hz ⟨f n x, hx⟩)
    refine ⟨ψ, fun w hw ↦ ?_, fun h0 ↦ ?_⟩
    · exact LinearMap.eq_zero_of_forall_norm_le_one (Q := LinearMap.range (g n).toLinearMap)
        (φ := ψ.toLinearMap) hψ hw
    · rw [h0, norm_zero] at hψz
      linarith
  choose ψ hψ0 hψz using hψ
  let φ (n : ℕ) : StrongDual 𝕜 F := (ψ n).comp c
  have hφ0 (n : ℕ) : ∀ w ∈ range (f n), φ n w = 0 := by
    rintro _ ⟨x, rfl⟩
    exact hψ0 n _ ⟨x, rfl⟩
  let U : Set F := {x | ∀ n : ℕ, ‖φ n x‖ ≤ ‖ψ n z‖ / (n + 1)}
  have hUeq : U = ⋂ n : ℕ, (φ n) ⁻¹' Metric.closedBall (0 : 𝕜) (‖ψ n z‖ / (n + 1)) := by
    ext z
    simp [U]
  have hUc : Convex ℝ U := by
    rw [hUeq]
    exact convex_iInter fun n ↦ (convex_closedBall (0 : 𝕜) _).is_linear_preimage
      ((φ n).toLinearMap.restrictScalars ℝ).isLinear
  have hUb : Balanced 𝕜 U := by
    rw [hUeq]
    exact balanced_iInter fun n ↦ (balanced_closedBall_zero).preimage (φ n).toLinearMap
  have hUpre (m : ℕ) : f m ⁻¹' U ∈ 𝓝 (0 : E m) := by
    -- Only the functionals `φ n` with `n < m` give a condition on the `m`-th step.
    have hfin : (⋂ n ∈ Finset.range m,
        {x : E m | ‖φ n (f m x)‖ ≤ ‖ψ n z‖ / (n + 1)}) ∈ 𝓝 (0 : E m) := by
      refine (Filter.biInter_finset_mem _).mpr fun n _ ↦ ?_
      have hc : Continuous fun x : E m ↦ ‖φ n (f m x)‖ :=
        ((φ n).continuous.comp (hfi m).continuous).norm
      have hpos : 0 < ‖ψ n z‖ / (n + 1) :=
        div_pos (norm_pos_iff.mpr (hψz n)) (by positivity)
      have hopen : IsOpen {x : E m | ‖φ n (f m x)‖ < ‖ψ n z‖ / (n + 1)} :=
        isOpen_lt hc continuous_const
      refine mem_of_superset (hopen.mem_nhds ?_) fun x hx ↦ ?_
      · simpa using hpos
      · have hx' : ‖φ n (f m x)‖ < ‖ψ n z‖ / (n + 1) := hx
        exact hx'.le
    refine mem_of_superset hfin fun x hx n ↦ ?_
    rcases lt_or_ge n m with hnm | hmn
    · exact (mem_iInter₂.mp hx) n (Finset.mem_range.mpr hnm)
    · rw [hφ0 n _ (range_mono j f h.apply_step hmn ⟨x, rfl⟩), norm_zero]
      exact div_nonneg (norm_nonneg _) (by positivity)
  have hUabs : Absorbent 𝕜 U := by
    intro z
    obtain ⟨m, x, rfl⟩ := h.exists_apply_eq z
    have hx : Absorbs 𝕜 (f m ⁻¹' U) {x} := absorbent_nhds_zero (hUpre m) x
    refine Filter.Eventually.mono hx fun c hc ↦ ?_
    rw [singleton_subset_iff] at hc ⊢
    obtain ⟨w, hw, hwx⟩ := hc
    exact ⟨f m w, hw, by rw [← hwx]; exact (map_smul (f m) c w).symm⟩
  have hU : U ∈ 𝓝 (0 : F) := by
    exact hFtop.symm ▸ locallyConvexFinalTopology.mem_nhds_zero f hUc hUb hUabs hUpre
  let V : Set (UniformSpace.Completion F) := closure (c '' U)
  have hV : V ∈ 𝓝 (0 : UniformSpace.Completion F) :=
    UniformSpace.Completion.hasBasis_nhds_zero_closure_image.mem_of_mem hU
  have hVbound (n : ℕ) {w : UniformSpace.Completion F} (hw : w ∈ V) :
      ‖ψ n w‖ ≤ ‖ψ n z‖ / (n + 1) := by
    exact (closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact hx n)
      (isClosed_le (ψ n).continuous.norm continuous_const)) hw
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (absorbent_nhds_zero (𝕜 := 𝕜) hV z)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (max r 0)
  have hcr : r ≤ ‖c‖ := (le_max_left _ _).trans hc.le
  have hcpos : 0 < ‖c‖ := (le_max_right _ _).trans_lt hc
  obtain ⟨n, hn⟩ := exists_nat_gt ‖c‖
  obtain ⟨w, hw, hwz⟩ := hr c hcr (Set.mem_singleton z)
  have h4 : ‖ψ n z‖ ≤ ‖c‖ * (‖ψ n z‖ / (n + 1)) := by
    have hwz' : c • w = z := hwz
    have heq : ‖ψ n z‖ = ‖c‖ * ‖ψ n w‖ := by rw [← hwz', map_smul, norm_smul]
    exact heq.le.trans (mul_le_mul_of_nonneg_left (hVbound n hw) hcpos.le)
  have hpos : 0 < ‖ψ n z‖ := norm_pos_iff.mpr (hψz n)
  have h5 : (n : ℝ) + 1 ≤ ‖c‖ := by
    have h6 : ‖ψ n z‖ * ((n : ℝ) + 1) ≤ ‖c‖ * ‖ψ n z‖ := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      calc ‖ψ n z‖ * ((n : ℝ) + 1) ≤ ‖c‖ * (‖ψ n z‖ / (n + 1)) * (n + 1) :=
            mul_le_mul_of_nonneg_right h4 hn1.le
        _ = ‖c‖ * ‖ψ n z‖ := by field_simp
    have h7 : ‖ψ n z‖ * ((n : ℝ) + 1) ≤ ‖ψ n z‖ * ‖c‖ := by rwa [mul_comm ‖c‖] at h6
    exact le_of_mul_le_mul_left h7 hpos
  linarith


end Completeness

end IsStrictInductiveLimit
