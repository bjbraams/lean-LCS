/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.CountableSeminorms
public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExtras.Analysis.SpecificLimits
public import WebbedSpaces.Basic

/-!
# Fréchet spaces are strictly webbed

A sequence `p` of seminorms on a vector space `E` defines a web: the set attached to the finite
sequence `n₀, …, n_{k-1}` is `{x | ∀ i < k, p i x ≤ n i + 1}`. If `p` generates the topology of
`E` and `E` is complete, this web is strict. Hence every Fréchet space is strictly webbed, and
De Wilde's closed graph theorem applies to maps into Fréchet spaces.

## Main definitions

* `SeminormFamily.web p`: the web of a sequence of seminorms.

## Main statements

* `WithSeminorms.isStrictWeb_web`: the web of a sequence of seminorms generating the topology of
  a complete space is strict.
* `StrictlyWebbedSpace.of_completeSpace_firstCountableTopology`: Fréchet spaces are strictly webbed.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.1.(4)

## Tags

web, webbed space, Fréchet space
-/

public section

open Set Filter PiNat

open scoped Topology

section General

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace SeminormFamily

/-- The **web of a sequence of seminorms**: the set attached to the finite sequence `n₀, …, n_{k-1}`
(stored with the newest index at the head) is `{x | ∀ i < k, p i x ≤ n i + 1}`. -/
@[expose]
def web (p : SeminormFamily 𝕜 E ℕ) : List ℕ → Set E
  | [] => univ
  | n :: l => web p l ∩ (p l.length).closedBall 0 (n + 1)

variable (p : SeminormFamily 𝕜 E ℕ)

/-- The root of the web of a sequence of seminorms is the whole space. -/
@[simp]
theorem web_nil : web p [] = univ :=
  rfl

/-- The successors of a set of the web of a sequence of seminorms. -/
theorem web_cons (n : ℕ) (l : List ℕ) :
    web p (n :: l) = web p l ∩ (p l.length).closedBall 0 (n + 1) :=
  rfl

/-- The web of a sequence of seminorms is a web. -/
theorem isWeb_web : IsWeb (web p) where
  nil := rfl
  iUnion_cons l := by
    refine Subset.antisymm (iUnion_subset fun n ↦ inter_subset_left) fun x hx ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (p l.length x)
    refine mem_iUnion.mpr ⟨n, hx, (p l.length).mem_closedBall_zero.mpr ?_⟩
    linarith

/-- Membership of the sets along a strand of the web of a sequence of seminorms. -/
theorem mem_web_res {σ : ℕ → ℕ} {k : ℕ} {x : E} :
    x ∈ web p (res σ k) ↔ ∀ i < k, p i x ≤ σ i + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [res_succ, web_cons, mem_inter_iff, ih, res_length, Seminorm.mem_closedBall_zero]
    refine ⟨fun h i hi ↦ ?_, fun h ↦ ⟨fun i hi ↦ h i (Nat.lt_succ_of_lt hi), h k k.lt_succ_self⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h.1 i hi
    · exact h.2

/-- The sets of the web of a sequence of seminorms are balanced. -/
theorem balanced_web (l : List ℕ) : Balanced 𝕜 (web p l) := by
  induction l with
  | nil => exact balanced_univ
  | cons n l ih => exact ih.inter ((p l.length).balanced_closedBall_zero _)

/-- The sets of the web of a sequence of continuous seminorms are closed. -/
theorem isClosed_web [TopologicalSpace E] (hp : ∀ i, Continuous (p i)) (l : List ℕ) :
    IsClosed (web p l) := by
  induction l with
  | nil => exact isClosed_univ
  | cons n l ih =>
    refine ih.inter ?_
    have h : (p l.length).closedBall 0 (n + 1) = {x | p l.length x ≤ n + 1} := by
      ext x
      exact (p l.length).mem_closedBall_zero
    rw [h]
    exact isClosed_le (hp l.length) continuous_const

end SeminormFamily

end General

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace SeminormFamily

variable (p : SeminormFamily 𝕜 E ℕ)

/-- The sets of the web of a sequence of seminorms are `ℝ`-convex. -/
theorem convex_web [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (l : List ℕ) : Convex ℝ (web p l) := by
  induction l with
  | nil => exact convex_univ
  | cons n l ih => exact ih.inter ((p l.length).convex_closedBall 0 _)

end SeminormFamily

variable [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] {p : SeminormFamily 𝕜 E ℕ}


variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The web of a sequence of seminorms that generates the topology of a complete space is a
strict web, Köthe II §35.1.(4). -/
theorem WithSeminorms.isStrictWeb_web (hp : WithSeminorms p) :
    IsStrictWeb 𝕜 (SeminormFamily.web p) where
  toIsWeb := SeminormFamily.isWeb_web p
  convex := SeminormFamily.convex_web p
  balanced := SeminormFamily.balanced_web p
  exists_radius σ := by
    -- Real scalars act through `𝕜`.
    have hpsmul (i : ℕ) (c : ℝ) (z : E) : p i (c • z) = |c| * p i z := by
      rw [← algebraMap_smul 𝕜 c z, map_smul_eq_mul, RCLike.algebraMap_eq_ofReal,
        RCLike.norm_ofReal]
    let B : ℕ → ℝ := fun k ↦ ∑ i ∈ Finset.range (k + 1), ((σ i : ℝ) + 1)
    have hBpos (k : ℕ) : 0 < B k :=
      Finset.sum_pos (fun i _ ↦ by positivity) Finset.nonempty_range_add_one
    have hBle (k i : ℕ) (hi : i ≤ k) : (σ i : ℝ) + 1 ≤ B k :=
      Finset.single_le_sum (f := fun i ↦ (σ i : ℝ) + 1) (fun i _ ↦ by positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    refine ⟨fun k ↦ (1 / 2 : ℝ) ^ (k + 1) / B k, fun k ↦ div_pos (by positivity) (hBpos k),
      fun x c hx hc k₀ ↦ ?_⟩
    -- The key estimate for the terms of the series.
    have hkey (m i : ℕ) (hi : i ≤ m) : p i (c m • x m) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
      have hxi : p i (x m) ≤ σ i + 1 :=
        (SeminormFamily.mem_web_res p).mp (hx m) i (Nat.lt_succ_of_le hi)
      rw [hpsmul, abs_of_nonneg (hc m).1]
      calc c m * p i (x m)
          ≤ (1 / 2 : ℝ) ^ (m + 1) / B m * B m :=
            mul_le_mul (hc m).2 (hxi.trans (hBle m i hi)) (apply_nonneg _ _)
              (div_pos (by positivity) (hBpos m)).le
        _ = (1 / 2 : ℝ) ^ (m + 1) := div_mul_cancel₀ _ (hBpos m).ne'
    have hgeom : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ (k + 1) :=
      (summable_nat_add_iff 1).mpr summable_geometric_two
    have hhalf (a b : ℕ) (hab : a ≤ b) : (1 / 2 : ℝ) ^ (b + 1) ≤ (1 / 2 : ℝ) ^ (a + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_succ hab)
    have hsum : Summable fun k ↦ c (k₀ + k) • x (k₀ + k) :=
      hp.summable_of_forall_le hgeom fun k i hi ↦
        (hkey (k₀ + k) i (hi.trans (Nat.le_add_left k k₀))).trans
          (hhalf k (k₀ + k) (Nat.le_add_left k k₀))
    obtain ⟨s, hs⟩ := hsum
    refine ⟨s, ?_, hs.tendsto_sum_nat⟩
    -- The partial sums lie in the closed set `web p (res σ (k₀ + 1))`.
    refine (SeminormFamily.isClosed_web p (fun i ↦ hp.continuous_seminorm i) _).mem_of_tendsto
      hs.tendsto_sum_nat (Eventually.of_forall fun N ↦ ?_)
    rw [SeminormFamily.mem_web_res]
    intro i hi
    calc p i (∑ k ∈ Finset.range N, c (k₀ + k) • x (k₀ + k))
        ≤ ∑ k ∈ Finset.range N, p i (c (k₀ + k) • x (k₀ + k)) :=
          Finset.le_sum_of_subadditive (p i) (map_zero (p i)).le (map_add_le_add (p i)) _ _
      _ ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) :=
          Finset.sum_le_sum fun k _ ↦
            (hkey (k₀ + k) i ((Nat.le_of_lt_succ hi).trans (Nat.le_add_right k₀ k))).trans
              (hhalf k (k₀ + k) (Nat.le_add_left k k₀))
      _ ≤ 1 := sum_half_pow_succ_le_one N
      _ ≤ σ i + 1 := by
          have : (0 : ℝ) ≤ σ i := Nat.cast_nonneg _
          linarith

/-- **Fréchet spaces are strictly webbed**, Köthe II §35.1.(4). More generally, the result holds for
every complete, first-countable locally convex space, without a Hausdorff assumption. -/
instance StrictlyWebbedSpace.of_completeSpace_firstCountableTopology [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] [FirstCountableTopology E] : StrictlyWebbedSpace 𝕜 E := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨p, hp⟩ := exists_seminormFamily_nat_withSeminorms 𝕜 E
  exact ⟨SeminormFamily.web p, hp.isStrictWeb_web⟩

end RCLike
