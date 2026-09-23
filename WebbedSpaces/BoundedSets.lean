/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.StrongDualBounded
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import MathlibExtras.Analysis.SpecificLimits
public import WebbedSpaces.Basic

/-!
# Spaces covered by a sequence of bounded closed disks are strictly webbed

A complete topological vector space that is the union of a sequence of closed, convex, balanced, von
Neumann bounded sets is strictly webbed: the sets of the web depend only on the first index. The
main application is that the strong dual of a first-countable (for instance metrizable) topological
vector space is strictly webbed, with the polars of a countable basis of neighbourhoods of zero as
the covering sequence ([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(11); compare
§35.4.(12)).

The explicit web constructions and their calculation lemmas live in the `WebConstruction`
namespace.

## Main definitions

* `WebConstruction.webOfSeq K`: the web whose set for a finite sequence with first index `n` is
  `K n`.

## Main statements

* `WebConstruction.isStrictWeb_webOfSeq`
* `StrictlyWebbedSpace.of_iUnion_isVonNBounded`
* `StrongDual.instStrictlyWebbedSpace`: the strong dual of a first-countable topological vector
  space is strictly webbed.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.4.(11), (12)

## Tags

web, webbed space, strong dual, bounded set
-/

public section

open Set Filter PiNat Bornology

open scoped Topology Pointwise

section WebOfSeq

variable {F : Type*}

/-- The web defined by a sequence `K` of sets: the set attached to a finite sequence with first
index `n` is `K n`. As the newest index of a web is at the head of the list, the first index is
the last entry of the list. -/
@[expose]
def WebConstruction.webOfSeq (K : ℕ → Set F) (l : List ℕ) : Set F :=
  match l.reverse with
  | [] => univ
  | n :: _ => K n

/-- The root of `WebConstruction.webOfSeq` is the whole space. -/
@[simp]
theorem WebConstruction.webOfSeq_nil (K : ℕ → Set F) : WebConstruction.webOfSeq K [] = univ :=
  rfl

/-- The set of `WebConstruction.webOfSeq` for a list with first index `n`. -/
@[simp]
theorem WebConstruction.webOfSeq_append_singleton (K : ℕ → Set F) (l : List ℕ) (n : ℕ) :
    WebConstruction.webOfSeq K (l ++ [n]) = K n := by
  simp [WebConstruction.webOfSeq]

/-- The sets of `WebConstruction.webOfSeq` along a strand `σ`. -/
theorem WebConstruction.webOfSeq_res_succ (K : ℕ → Set F) (σ : ℕ → ℕ) (k : ℕ) :
    WebConstruction.webOfSeq K (res σ (k + 1)) = K (σ 0) := by
  induction k with
  | zero => exact WebConstruction.webOfSeq_append_singleton K [] (σ 0)
  | succ k ih =>
    obtain ⟨L, b, hL⟩ : ∃ L b, res σ (k + 1) = L ++ [b] := by
      rcases List.eq_nil_or_concat (res σ (k + 1)) with h | ⟨L, b, h⟩
      · simp [res_succ] at h
      · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
    rw [hL, WebConstruction.webOfSeq_append_singleton] at ih
    rw [res_succ, hL, ← List.cons_append, WebConstruction.webOfSeq_append_singleton, ih]

/-- A sequence of sets that covers the space defines a web. -/
theorem WebConstruction.isWeb_webOfSeq {K : ℕ → Set F} (hK : ⋃ n, K n = univ) :
    IsWeb (WebConstruction.webOfSeq K) where
  nil := rfl
  iUnion_cons l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · rw [WebConstruction.webOfSeq_nil, ← hK]
      exact iUnion_congr fun n ↦ WebConstruction.webOfSeq_append_singleton K [] n
    · simp only [List.concat_eq_append]
      have h (n : ℕ) : WebConstruction.webOfSeq K (n :: (L ++ [b])) = K b := by
        rw [← List.cons_append, WebConstruction.webOfSeq_append_singleton]
      simp_rw [h]
      rw [WebConstruction.webOfSeq_append_singleton, iUnion_const]

variable {𝕜 : Type*} [NormedField 𝕜] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
  [TopologicalSpace F]

/-- A covering sequence of convex balanced sets `K n` defines a strict web, if for points
`x k ∈ K n` and coefficients `0 ≤ c k ≤ (1 / 2) ^ (k + 1)` every tail of the series
`∑ c k • x k` converges to a point of `K n`. -/
theorem WebConstruction.isStrictWeb_webOfSeq {K : ℕ → Set F} (hK : ⋃ n, K n = univ)
    (hconv : ∀ n, Convex ℝ (K n)) (hbal : ∀ n, Balanced 𝕜 (K n))
    (hseries : ∀ (n : ℕ) (x : ℕ → F) (c : ℕ → ℝ), (∀ k, x k ∈ K n) →
      (∀ k, 0 ≤ c k ∧ c k ≤ (1 / 2 : ℝ) ^ (k + 1)) → ∀ k₀, ∃ s ∈ K n,
        Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c (k₀ + k) • x (k₀ + k)) atTop (𝓝 s)) :
    IsStrictWeb 𝕜 (WebConstruction.webOfSeq K) where
  toIsWeb := WebConstruction.isWeb_webOfSeq hK
  convex l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact convex_univ
    · rw [List.concat_eq_append, WebConstruction.webOfSeq_append_singleton]
      exact hconv b
  balanced l := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact balanced_univ
    · rw [List.concat_eq_append, WebConstruction.webOfSeq_append_singleton]
      exact hbal b
  exists_radius σ := by
    refine ⟨fun k ↦ (1 / 2 : ℝ) ^ (k + 1), fun k ↦ by positivity, fun x c hx hc k₀ ↦ ?_⟩
    obtain ⟨s, hs, hlim⟩ := hseries (σ 0) x c
      (fun k ↦ by rw [← WebConstruction.webOfSeq_res_succ K σ k]; exact hx k) hc k₀
    exact ⟨s, by rw [WebConstruction.webOfSeq_res_succ]; exact hs, hlim⟩

end WebOfSeq

section Bounded

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
  [IsScalarTower ℝ 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]

/-- The series condition of `WebConstruction.isStrictWeb_webOfSeq` for a closed, convex, balanced,
von Neumann bounded subset of a complete topological vector space. -/
theorem Bornology.IsVonNBounded.exists_mem_tendsto_sum_smul {K : Set F} (hcl : IsClosed K)
    (hconv : Convex ℝ K) (hbal : Balanced 𝕜 K) (hbdd : IsVonNBounded 𝕜 K) {x : ℕ → F}
    {c : ℕ → ℝ} (hx : ∀ k, x k ∈ K) (hc : ∀ k, 0 ≤ c k ∧ c k ≤ (1 / 2 : ℝ) ^ (k + 1)) :
    ∃ s ∈ K, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c k • x k) atTop (𝓝 s) := by
  have h0 : (0 : F) ∈ K := hbal.zero_mem ⟨x 0, hx 0⟩
  have hgeom : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  have hsum : Summable fun k ↦ c k • x k := by
    rw [summable_iff_vanishing]
    intro e he
    -- A small real multiple of `K` lies in `e`.
    obtain ⟨R, hR⟩ := (absorbs_iff_norm.mp (hbdd he))
    let δ : ℝ := (max R 1)⁻¹
    have hδ : 0 < δ := inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right R 1))
    obtain ⟨sg, hsg⟩ := summable_iff_vanishing.mp hgeom (Metric.ball 0 δ)
      (Metric.ball_mem_nhds 0 hδ)
    refine ⟨sg, fun t ht ↦ ?_⟩
    have hct : ∀ k ∈ t, 0 ≤ c k := fun k _ ↦ (hc k).1
    rcases (Finset.sum_nonneg hct).eq_or_lt with h | h
    · have hzero : ∀ k ∈ t, c k = 0 := (Finset.sum_eq_zero_iff_of_nonneg hct).mp h.symm
      rw [Finset.sum_eq_zero fun k hk ↦ by rw [hzero k hk, zero_smul]]
      exact mem_of_mem_nhds he
    · have hlt : ∑ k ∈ t, c k < δ := by
        have h1 := hsg t ht
        rw [mem_ball_zero_iff, Real.norm_eq_abs] at h1
        exact (Finset.sum_le_sum fun k _ ↦ (hc k).2).trans_lt ((le_abs_self _).trans_lt h1)
      obtain ⟨y, hy, hyx⟩ := hconv.sum_smul_mem_smul hct h fun k _ ↦ hx k
      rw [← hyx]
      -- `K ⊆ r⁻¹ • e` for `r = ∑ k ∈ t, c k`, because `r⁻¹ ≥ R`.
      set r : ℝ := ∑ k ∈ t, c k with hr
      have hrR : R ≤ ‖((r⁻¹ : ℝ) : 𝕜)‖ := by
        rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr h)]
        have h2 : δ⁻¹ ≤ r⁻¹ := inv_anti₀ h hlt.le
        rw [inv_inv] at h2
        exact (le_max_left R 1).trans h2
      obtain ⟨w, hw, hwy⟩ := hR _ hrR hy
      have hwy' : ((r⁻¹ : ℝ) : 𝕜) • w = y := hwy
      change r • y ∈ e
      rw [← hwy', ← algebraMap_smul 𝕜 r, RCLike.algebraMap_eq_ofReal, smul_smul,
        ← RCLike.ofReal_mul, mul_inv_cancel₀ h.ne', RCLike.ofReal_one, one_smul]
      exact hw
  obtain ⟨s, hs⟩ := hsum
  refine ⟨s, hcl.mem_of_tendsto hs.tendsto_sum_nat (Eventually.of_forall fun N ↦ ?_),
    hs.tendsto_sum_nat⟩
  exact hconv.sum_smul_mem h0 (fun k _ ↦ (hc k).1)
    ((Finset.sum_le_sum fun k _ ↦ (hc k).2).trans (sum_half_pow_succ_le_one N)) fun k _ ↦ hx k

/-- A complete topological vector space that is the union of a sequence of closed, convex,
balanced, von Neumann bounded sets is strictly webbed; compare Köthe II §35.4.(12). -/
theorem StrictlyWebbedSpace.of_iUnion_isVonNBounded {K : ℕ → Set F} (hK : ⋃ n, K n = univ)
    (hcl : ∀ n, IsClosed (K n)) (hconv : ∀ n, Convex ℝ (K n)) (hbal : ∀ n, Balanced 𝕜 (K n))
    (hbdd : ∀ n, IsVonNBounded 𝕜 (K n)) : StrictlyWebbedSpace 𝕜 F := by
  refine ⟨WebConstruction.webOfSeq K,
    WebConstruction.isStrictWeb_webOfSeq hK hconv hbal fun n x c hx hc k₀ ↦ ?_⟩
  refine Bornology.IsVonNBounded.exists_mem_tendsto_sum_smul (hcl n) (hconv n) (hbal n) (hbdd n)
    (fun k ↦ hx (k₀ + k)) fun k ↦ ⟨(hc (k₀ + k)).1, (hc (k₀ + k)).2.trans ?_⟩
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

end Bounded

section StrongDual

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- **The strong dual of a first-countable topological vector space is strictly webbed**,
Köthe II §35.4.(11). In particular the strong dual of a metrizable locally convex space is
strictly webbed. -/
instance StrongDual.instStrictlyWebbedSpace [FirstCountableTopology E] :
    StrictlyWebbedSpace 𝕜 (StrongDual 𝕜 E) := by
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  refine StrictlyWebbedSpace.of_iUnion_isVonNBounded (K := fun n ↦ StrongDual.polar 𝕜 (U n))
    (eq_univ_of_forall fun φ ↦ ?_) (fun n ↦ StrongDual.isClosed_polar _)
    (fun n ↦ LinearMap.convex_polar _ _) (fun n ↦ LinearMap.balanced_polar _ _)
    fun n ↦ StrongDual.isVonNBounded_polar_of_mem_nhds (hU.mem n)
  -- A continuous functional is bounded by one on a neighbourhood of zero.
  have hφ : {z : E | ‖φ z‖ ≤ 1} ∈ 𝓝 (0 : E) := by
    have hc : ContinuousAt (fun z ↦ ‖φ z‖) 0 := (continuous_norm.comp φ.continuous).continuousAt
    refine hc.preimage_mem_nhds (Iic_mem_nhds ?_)
    simp
  obtain ⟨n, -, hn⟩ := hU.toHasBasis.mem_iff.mp hφ
  exact mem_iUnion.mpr ⟨n, (StrongDual.mem_polar_iff 𝕜 _).mpr fun z hz ↦ hn hz⟩

end StrongDual
