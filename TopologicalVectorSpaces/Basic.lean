/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.MetricSpace.PiNat
public import MathlibExtras.Analysis.ConvexCombinations
public import MathlibExtras.Topology.BaireTree
public import TopologicalGroups.Basic

/-!
# General lemmas on topological vector spaces

This file collects lemmas on topological vector spaces that are not specific to locally convex
spaces and that belong with existing files of Mathlib: images and preimages of absorbent,
absorbing and balanced sets under linear maps, scalar multiples and balanced hulls of bounded
sets, a criterion for neighbourhoods of zero in first-countable spaces, convex combinations with
total weight at most one, the closed graph of a continuous linear map, and non-meagre convex
sets.

## Main statements

* `Absorbent.preimage`, `Balanced.preimage`, `Absorbent.image_of_surjective`, `Balanced.image`,
  `Absorbs.image_linearMap`, `Absorbs.preimage_linearMap`, `Absorbent.restrictScalars_real`,
  `Submodule.balanced`.
* `Bornology.IsVonNBounded.smul_set`, `Bornology.IsVonNBounded.balancedHull`,
  `Bornology.IsVonNBounded.preimage_of_isInducing`.
* `mem_nhds_zero_of_forall_absorbs_range`: in a first-countable topological vector space a set
  that absorbs every sequence tending to zero is a neighbourhood of zero.
* `exists_tendsto_atTop_tendsto_smul_zero`: in a first-countable topological vector space, for
  `x n → 0` there are `ρ n → ∞` with `ρ n • x n → 0` (Köthe I §28.1.(5)).
* `Convex.balancedCore`: the balanced core of a convex set containing zero is convex.
* `ContinuousLinearMap.isClosed_graph`: the graph of a continuous linear map into a Hausdorff
  space is closed.
* `closure_mem_nhds_zero_of_not_isMeagre`: in a real topological vector space the closure of a
  convex, symmetric, non-meagre set is a neighbourhood of zero.

## Implementation notes

The two image lemmas are named as in Mathlib PR #40983, which states them in greater
generality; they are to be deleted here once that PR has been merged and Mathlib has been
bumped. The proof of `mem_nhds_zero_of_forall_absorbs_range` follows that of
`LinearMap.continuousAt_zero_of_locally_bounded` in
`Mathlib/Analysis/LocallyConvex/ContinuousOfBounded.lean`.

## Tags

topological vector space, absorbent, balanced, bounded set, Baire category
-/

public section

open Set Filter Bornology PiNat

open scoped Topology Pointwise

section Balanced

variable {𝕜 E F : Type*} [SeminormedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- The preimage of a balanced set under a linear map is balanced. -/
theorem Balanced.preimage {s : Set F} (hs : Balanced 𝕜 s) (f : E →ₗ[𝕜] F) :
    Balanced 𝕜 (f ⁻¹' s) :=
  hs.mulActionHom_preimage f.toMulActionHom

/-- The image of a balanced set under a linear map is balanced.

Duplicate: this is `Balanced.image` of Mathlib PR #40983 (K. H. Wilson), file
`Mathlib/Analysis/LocallyConvex/Basic.lean`, specialized here to linear maps over a seminormed
ring. The proof is adapted. Delete this copy once that PR is in the pinned Mathlib. -/
theorem Balanced.image {s : Set E} (hs : Balanced 𝕜 s) (f : E →ₗ[𝕜] F) :
    Balanced 𝕜 (f '' s) := by
  rintro a ha _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨a • x, hs a ha ⟨x, hx, rfl⟩, map_smul f a x⟩

/-- A submodule is a balanced set. -/
theorem Submodule.balanced (Q : Submodule 𝕜 E) : Balanced 𝕜 (Q : Set E) := by
  rintro a - _ ⟨x, hx, rfl⟩
  exact Q.smul_mem a hx

end Balanced

section AbsorbentBalanced

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The preimage of an absorbent set under a linear map is absorbent. -/
theorem Absorbent.preimage {s : Set F} (hs : Absorbent 𝕜 s) (f : E →ₗ[𝕜] F) :
    Absorbent 𝕜 (f ⁻¹' s) :=
  absorbent_iff_inv_smul.2 fun x ↦ (absorbent_iff_inv_smul.1 hs (f x)).mono fun c hc ↦ by
    simpa only [mem_preimage, map_smul] using hc

/-- The image of an absorbent set under a surjective linear map is absorbent.

Duplicate: this is `Absorbent.image_of_surjective` of Mathlib PR #40983 (K. H. Wilson), file
`Mathlib/Topology/Bornology/Absorbs.lean`, where it is stated for any `MulActionHomClass`.
The proof here is independent. Delete this copy once that PR is in the pinned Mathlib. -/
theorem Absorbent.image_of_surjective {s : Set E} {f : E →ₗ[𝕜] F}
    (hf : Function.Surjective f) (hs : Absorbent 𝕜 s) : Absorbent 𝕜 (f '' s) :=
  absorbent_iff_inv_smul.2 fun y ↦ by
    obtain ⟨x, rfl⟩ := hf y
    exact (absorbent_iff_inv_smul.1 hs x).mono fun c hc ↦ ⟨c⁻¹ • x, hc, map_smul f c⁻¹ x⟩

/-- A set that is absorbent over a real or complex field is absorbent over the reals. -/
theorem Absorbent.restrictScalars_real {𝕜 : Type*} [RCLike 𝕜] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] {s : Set E} (hs : Absorbent 𝕜 s) : Absorbent ℝ s := fun x ↦
  (hs x).restrict_scalars <| by
    rw [← Algebra.algebraMap_eq_smul_one']
    exact tendsto_algebraMap_cobounded ℝ 𝕜

/-- A scalar all of whose multiples have norm at most one is zero. -/
theorem eq_zero_of_forall_norm_mul_le_one {z : 𝕜} (h : ∀ c : 𝕜, ‖c * z‖ ≤ 1) : z = 0 := by
  by_contra hz
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ‖z‖⁻¹
  have h1 := h c
  rw [norm_mul] at h1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : 1 < ‖c‖ * ‖z‖ := by
    have h3 := mul_lt_mul_of_pos_right hc hzpos
    rwa [inv_mul_cancel₀ hzpos.ne'] at h3
  exact (h1.trans_lt h2).false

end AbsorbentBalanced

section Absorbs

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- The image under a linear map of an absorbing set absorbs the image of the absorbed set. -/
theorem Absorbs.image_linearMap {s t : Set E} (h : Absorbs 𝕜 s t) (f : E →ₗ[𝕜] F) :
    Absorbs 𝕜 (f '' s) (f '' t) := by
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp h
  refine absorbs_iff_norm.mpr ⟨r, fun c hc ↦ ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hr c hc hx
  have hwx' : c • w = x := hwx
  exact ⟨f w, ⟨w, hw, rfl⟩, by rw [← hwx', map_smul]⟩

/-- If `W` absorbs the image of `T` under a linear map, then the preimage of `W` absorbs `T`. -/
theorem Absorbs.preimage_linearMap {W : Set F} {T : Set E} {f : E →ₗ[𝕜] F}
    (h : Absorbs 𝕜 W (f '' T)) : Absorbs 𝕜 (f ⁻¹' W) T := by
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp h
  refine absorbs_iff_norm.mpr ⟨max r 1, fun a ha x hx ↦ ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ha
    exact absurd ((le_max_right r 1).trans ha) (by norm_num)
  obtain ⟨w, hw, hwa⟩ := hr a ((le_max_left r 1).trans ha) (mem_image_of_mem f hx)
  have hwa' : a • w = f x := hwa
  refine ⟨a⁻¹ • x, ?_, smul_inv_smul₀ ha0 x⟩
  rw [mem_preimage, map_smul, ← hwa', inv_smul_smul₀ ha0]
  exact hw

end Absorbs

section Bounded

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A scalar multiple of a von Neumann bounded set is von Neumann bounded. -/
theorem Bornology.IsVonNBounded.smul_set [ContinuousConstSMul 𝕜 E]
    {S : Set E} (hS : IsVonNBounded 𝕜 S) (c : 𝕜) : IsVonNBounded 𝕜 (c • S) := by
  rw [← image_smul]
  exact hS.image (c • ContinuousLinearMap.id 𝕜 E)

/-- The balanced hull of a bounded set is bounded. -/
theorem Bornology.IsVonNBounded.balancedHull [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (balancedHull 𝕜 s) := by
  intro V hV
  obtain ⟨W, ⟨hW, hWb⟩, hWV⟩ := (nhds_basis_balanced 𝕜 E).mem_iff.mp hV
  refine Absorbs.mono_left ?_ hWV
  refine Filter.Eventually.mono (hs hW) fun c hc ↦ ?_
  exact Balanced.balancedHull_subset_of_subset (hWb.smul c) hc

/-- In a first-countable topological vector space a set that absorbs the range of every
sequence tending to zero is a neighbourhood of zero. The proof follows
`LinearMap.continuousAt_zero_of_locally_bounded` of Mathlib. -/
theorem mem_nhds_zero_of_forall_absorbs_range [ContinuousSMul 𝕜 E] [FirstCountableTopology E]
    {s : Set E}
    (hs : ∀ x : ℕ → E, Tendsto x atTop (𝓝 0) → Absorbs 𝕜 s (range x)) :
    s ∈ 𝓝 (0 : E) := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  have c_ne : c ≠ 0 := norm_pos_iff.mp hc0
  -- A fast decreasing basis of neighbourhoods of zero.
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩
  simp only [_root_.id] at bE
  have bE' : (𝓝 (0 : E)).HasBasis (fun _ ↦ True) (fun n : ℕ ↦ (c ^ n) • b n) := by
    refine bE.1.to_hasBasis' ?_ ?_
    · intro n _
      use n
      exact ⟨trivial, (bE1 n).2 _ (by grw [norm_pow, hc1, one_pow])⟩
    · intro n _
      simpa using smul_mem_nhds_smul₀ (pow_ne_zero n c_ne) (bE1 n).1
  by_contra hs0
  -- Choose `u n ∈ c ^ n • b n` outside `s`.
  have hex (n : ℕ) : ∃ x ∈ (c ^ n) • b n, x ∉ s := by
    by_contra hcon
    push Not at hcon
    exact hs0 (mem_of_superset (bE'.mem_of_mem trivial) hcon)
  choose u hu hu' using hex
  -- The sequence `c ^ (-n) • u n` tends to zero, so its range is bounded and `s` absorbs it.
  have h_tendsto : Tendsto (fun n : ℕ ↦ (c ^ n)⁻¹ • u n) atTop (𝓝 (0 : E)) := by
    apply bE.tendsto
    intro n
    simpa only [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero n c_ne)] using hu n
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hs _ h_tendsto)
  -- For large `n` the scalar `c ^ (-n)` is large, which forces `u n ∈ s`.
  have hlarge : ∃ n : ℕ, r ≤ ‖(c ^ n)⁻¹‖ := by
    have h1 : Tendsto (fun n : ℕ ↦ ‖(c ^ n)⁻¹‖) atTop atTop := by
      have h2 : ∀ n : ℕ, ‖(c ^ n)⁻¹‖ = (‖c‖⁻¹) ^ n := fun n ↦ by
        rw [norm_inv, norm_pow, inv_pow]
      simp_rw [h2]
      exact tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hc0).mpr hc1)
    exact (h1.eventually_ge_atTop r).exists
  obtain ⟨n, hn⟩ := hlarge
  obtain ⟨z, hz, hzu⟩ := hr _ hn (mem_range_self n)
  have hzeq : z = u n := smul_right_injective E (inv_ne_zero (pow_ne_zero n c_ne)) hzu
  exact hu' n (hzeq ▸ hz)

end Bounded

section Sequence

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  [FirstCountableTopology E]

/-- In a first-countable topological vector space, for every sequence `x n → 0` there are
numbers `ρ n → ∞` such that `ρ n • x n → 0`, Köthe I §28.1.(5). -/
theorem exists_tendsto_atTop_tendsto_smul_zero {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℝ, (∀ n, 1 ≤ ρ n) ∧ Tendsto ρ atTop atTop ∧
      Tendsto (fun n ↦ ρ n • x n) atTop (𝓝 0) := by
  classical
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hev (k : ℕ) : ∀ᶠ n in atTop, ((k : ℝ) + 1) • x n ∈ U k := by
    have h : Tendsto (fun n ↦ ((k : ℝ) + 1) • x n) atTop (𝓝 0) := by
      simpa using hx.const_smul ((k : ℝ) + 1)
    exact h.eventually (hU.mem k)
  choose N hN using fun k ↦ eventually_atTop.mp (hev k)
  -- The greatest `k ≤ n` with `N k ≤ n`.
  let κ : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun k ↦ N k ≤ n) n
  have hκ {k n : ℕ} (hk : k ≤ n) (hNk : N k ≤ n) : k ≤ κ n ∧ N (κ n) ≤ n :=
    ⟨Nat.le_findGreatest hk hNk, Nat.findGreatest_spec (P := fun k ↦ N k ≤ n) hk hNk⟩
  refine ⟨fun n ↦ (κ n : ℝ) + 1, fun n ↦ le_add_of_nonneg_left (Nat.cast_nonneg _), ?_, ?_⟩
  · refine tendsto_atTop.mpr fun b ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    have h1 : (k : ℝ) ≤ κ n :=
      Nat.cast_le.mpr (hκ (le_of_max_le_left hn) (le_of_max_le_right hn)).1
    linarith
  · refine hU.toHasBasis.tendsto_right_iff.mpr fun k _ ↦ ?_
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    obtain ⟨h1, h2⟩ := hκ (le_of_max_le_left hn) (le_of_max_le_right hn)
    exact hU.antitone h1 (hN (κ n) n h2)

end Sequence

section Convex

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [SMulCommClass ℝ 𝕜 E]

/-- The `𝕜`-balanced core of an `ℝ`-convex set containing zero is `ℝ`-convex. -/
theorem Convex.balancedCore {s : Set E} (hs : Convex ℝ s) (h0 : (0 : E) ∈ s) :
    Convex ℝ (balancedCore 𝕜 s) := by
  rw [balancedCore_eq_iInter h0]
  refine convex_iInter₂ fun r _ ↦ ?_
  rw [← image_smul]
  exact hs.is_linear_image ⟨smul_add r, fun c x ↦ (smul_comm c r x).symm⟩

end Convex

section Graph

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The graph of a continuous linear map into a Hausdorff space is closed. -/
theorem ContinuousLinearMap.isClosed_graph [T2Space E] (A : F →L[𝕜] E) :
    IsClosed (A.toLinearMap.graph : Set (F × E)) := by
  have h : (A.toLinearMap.graph : Set (F × E)) = {p | p.2 = A p.1} := by
    ext p
    exact LinearMap.mem_graph_iff _ _
  rw [h]
  exact isClosed_eq continuous_snd (A.continuous.comp continuous_fst)

end Graph

section Baire

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

variable [Module ℝ E] [ContinuousSMul ℝ E]

/-- In a real topological vector space the closure of a convex, symmetric, non-meagre set is a
neighbourhood of zero. -/
theorem closure_mem_nhds_zero_of_not_isMeagre {S : Set E} (hc : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) (hS : ¬IsMeagre S) : closure S ∈ 𝓝 (0 : E) := by
  -- The closure has an interior point `x`, hence also `-x`, hence their midpoint `0`.
  have hne : (interior (closure S)).Nonempty := by
    by_contra h
    exact hS (IsNowhereDense.isMeagre (not_nonempty_iff_eq_empty.mp h))
  obtain ⟨x, hx⟩ := hne
  have hclsymm : ∀ y ∈ closure S, -y ∈ closure S := fun y hy ↦ by
    have h := (map_mem_closure continuous_neg hy fun z hz ↦ hsymm z hz)
    exact h
  have hnegx : -x ∈ interior (closure S) := by
    rw [mem_interior_iff_mem_nhds] at hx ⊢
    have h : (fun y : E ↦ -y) ⁻¹' closure S ∈ 𝓝 (-x) :=
      continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hx)
    exact mem_of_superset h fun y hy ↦ by simpa using hclsymm _ hy
  have h0 : (0 : E) ∈ interior (closure S) := by
    have h := hc.closure.interior hx hnegx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using h
  exact mem_interior_iff_mem_nhds.mp h0


end Baire

section BoundedPreimage

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]

/-- A linear inducing map pulls back von Neumann bounded sets to bounded sets. Injectivity is
unnecessary: the induced topology makes its kernel an indiscrete, hence bounded, subspace. -/
theorem Bornology.IsVonNBounded.preimage_of_isInducing {B : Set F} (hB : IsVonNBounded 𝕜 B)
    (f : E →ₗ[𝕜] F) (hf : Topology.IsInducing f) : IsVonNBounded 𝕜 (f ⁻¹' B) := by
  intro U hU
  rw [hf.nhds_eq_comap, map_zero] at hU
  obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
  exact ((hB hV).mono_right (image_preimage_subset f B)).preimage_linearMap.mono_left hVU

end BoundedPreimage
