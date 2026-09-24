/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bornological
public import LocallyConvexSpaces.CountableSeminorms
public import Mathlib.Basic.Rel
public import Mathlib.Topology.Baire.Lemmas
public import MathlibExtras.Analysis.SpecificLimits
public import TopologicalGroups.Series
public import TopologicalVectorSpaces.LinearRelation
public import WebbedSpaces.Basic

/-!
# De Wilde's theorem for linear relations

De Wilde's closed graph theorem and open mapping theorem are two readings of one statement
about a linear relation. Let `F` be a webbed locally convex space, `E` a topological vector
space, and `G` a linear subspace of `F × E` whose projection to `E` is not meagre. Write
`G[V] = {y | ∃ x ∈ V, (x, y) ∈ G}`. If

* `E` is first-countable and `G` is sequentially closed, or
* `G` is closed,

then `G[V]` is a neighbourhood of zero in `E` for every neighbourhood `V` of zero in `F`.
For the transposed graph of a linear map `A : E → F` this says that `A` is continuous
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.2.(1), (3), (4)); for the graph of
a linear map defined on a subspace of `F` it says that the map is open (§35.3.(2), (4)).

The same conclusion holds if the topology of `E` is the final locally convex topology of a
family of such spaces, in particular if `E` is ultrabornological, and the projection of `G` is
all of `E` (§35.2.(2), (5) and §35.3.(3), (5), (6)).

## The proof

Let `C` be a completing web on `F` and `p` a continuous seminorm on `F`. By Baire's theorem
there is a strand `σ` such that no `G[C (res σ k)]` is meagre, and then integers `m k` such
that `N k = G[C (res σ (k + 1)) ∩ p.closedBall 0 (m k)]` is not meagre. The closure of a
non-meagre set has an interior point, so there are `b k ∈ N k` such that the closure of
`N k - b k` is a neighbourhood of zero. A point `y₀` of the closure of `G[p.closedBall 0 1]` is
approximated successively (`exists_seq_mem_sub_sum_mem_closure`) by sums of terms
`y (k + 1) ∈ ν k • (N k - b k)`, with small `ν k > 0`. The web makes the corresponding series in
`F` converge, to a point `a` with `p a ≤ 3`, and `(a, y₀)` lies in the closure of `G`: in the
sequential closure if `E` is first-countable, and in general by Köthe's argument that uses
§35.1.(3). Köthe treats `ℝ`-convex webs first and handles general webs by a telescoping
construction; here the translation by `b k` lets one approximation lemma serve all cases.

## Main statements

* `Submodule.image_mem_nhds_zero_of_isSeqClosed`, `Submodule.image_mem_nhds_zero_of_isClosed`:
  De Wilde's theorem for linear relations.
* `Submodule.image_mem_nhds_zero_of_locallyConvexFinalTopology`: the passage to locally convex
  hulls.
* `Submodule.image_mem_nhds_zero_of_ultrabornologicalSpace`.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.2, §35.3
* [M. De Wilde, *Closed Graph Theorems and Webbed Spaces*][dewilde1978]

## Tags

closed graph theorem, open mapping theorem, De Wilde, webbed space, linear relation
-/

public section

open Set Filter PiNat

open scoped Topology Pointwise

universe u v

/-- For a map `g` from a nonempty Baire space into a space with a web `C` there is a strand
`σ` such that no preimage `g ⁻¹' C (res σ k)` is meagre. -/
theorem IsWeb.exists_forall_not_isMeagre_preimage {E F : Type*} [TopologicalSpace E]
    [BaireSpace E] [Nonempty E] {C : List ℕ → Set F} (hC : IsWeb C) (g : E → F) :
    ∃ σ : ℕ → ℕ, ∀ k, ¬IsMeagre (g ⁻¹' C (res σ k)) := by
  refine exists_forall_not_isMeagre_res (T := fun l ↦ g ⁻¹' C l) ?_ fun l ↦ ?_
  · rw [hC.nil, preimage_univ]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  · rw [← preimage_iUnion, hC.iUnion_cons l]

section Relation

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  (G : Submodule 𝕜 (F × E))

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- The image of the whole space under a linear relation is the projection of the relation. -/
private theorem Submodule.relImage_univ :
    SetRel.image (G : Set (F × E)) univ = Prod.snd '' (G : Set (F × E)) := by
  ext y
  exact ⟨fun ⟨x, _, h⟩ ↦ ⟨(x, y), h, rfl⟩, fun ⟨q, hq, hqy⟩ ↦ ⟨q.1, mem_univ _, hqy ▸ hq⟩⟩

/-- Real scalars act on the values of a seminorm through their absolute value. -/
private theorem Seminorm.map_real_smul_eq_abs_mul (p : Seminorm 𝕜 F) (c : ℝ) (y : F) :
    p (c • y) = |c| * p y := by
  rw [← algebraMap_smul 𝕜 c y, map_smul_eq_mul, RCLike.algebraMap_eq_ofReal,
    RCLike.norm_ofReal]

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- If the image `G[S]` under a linear relation is not meagre then neither is
`G[S ∩ p.closedBall 0 (m + 1)]` for some natural number `m`. -/
private theorem Submodule.exists_nat_not_isMeagre_relImage_inter_closedBall [TopologicalSpace E]
    (p : Seminorm 𝕜 F) {S : Set F} (hS : ¬IsMeagre (SetRel.image (G : Set (F × E)) S)) :
    ∃ m : ℕ, ¬IsMeagre (SetRel.image (G : Set (F × E)) (S ∩ p.closedBall 0 ((m : ℝ) + 1))) := by
  by_contra hcon
  push Not at hcon
  refine hS ((isMeagre_iUnion hcon).mono ?_)
  rintro y ⟨x, hx, h⟩
  obtain ⟨m, hm⟩ := exists_nat_ge (p x)
  exact mem_iUnion.mpr ⟨m, x, ⟨hx, p.mem_closedBall_zero.mpr (hm.trans (by linarith))⟩, h⟩

/-- If the projection of a linear relation `G ⊆ F × E` to `E` is not meagre then the closure of
the image of the closed unit ball of a seminorm on `F` is a neighbourhood of zero. -/
private theorem Submodule.closure_relImage_closedBall_mem_nhds_zero [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hne : ¬IsMeagre (Prod.snd '' (G : Set (F × E)))) (p : Seminorm 𝕜 F) :
    closure (SetRel.image (G : Set (F × E)) (p.closedBall 0 1)) ∈ 𝓝 (0 : E) := by
  -- Some `G[p.closedBall 0 (n + 1)]` is non-meagre; scale it down.
  rw [← G.relImage_univ] at hne
  obtain ⟨n, hn⟩ := G.exists_nat_not_isMeagre_relImage_inter_closedBall p hne
  rw [univ_inter] at hn
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcl := closure_mem_nhds_zero_of_not_isMeagre
    (G.convex_relImage (p.convex_closedBall 0 ((n : ℝ) + 1)))
    (G.neg_mem_relImage fun x hx ↦ by
      rw [Seminorm.mem_closedBall_zero, map_neg_eq_map]
      exact p.mem_closedBall_zero.mp hx) hn
  have hsc : ((n : ℝ) + 1)⁻¹ • closure (SetRel.image (G : Set (F × E))
      (p.closedBall 0 ((n : ℝ) + 1))) ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff (inv_ne_zero hnpos.ne')).mpr hcl
  refine mem_of_superset hsc ?_
  rintro _ ⟨y, hy, rfl⟩
  refine map_mem_closure (continuous_const_smul ((n : ℝ) + 1)⁻¹) hy fun w hw ↦ ?_
  obtain ⟨x, hx, h⟩ := hw
  refine ⟨((n : ℝ) + 1)⁻¹ • x, ?_, G.smul_of_tower_mem ((n : ℝ) + 1)⁻¹ h⟩
  rw [Seminorm.mem_closedBall_zero, p.map_real_smul_eq_abs_mul, abs_of_pos (inv_pos.mpr hnpos),
    inv_mul_le_iff₀ hnpos, mul_one]
  exact p.mem_closedBall_zero.mp hx

/-- Coefficients for De Wilde's construction: positive numbers `ν k ≤ ρ k` with
`ν k * (m k + 1) ≤ (1 / 2) ^ (k + 1)`. -/
private theorem exists_coeff_mul_le_half_pow {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) (m : ℕ → ℕ) :
    ∃ ν : ℕ → ℝ, (∀ k, 0 < ν k) ∧ (∀ k, ν k ≤ ρ k) ∧
      ∀ k, ν k * ((m k : ℝ) + 1) ≤ (1 / 2) ^ (k + 1) := by
  have hmpos (k : ℕ) : (0 : ℝ) < (m k : ℝ) + 1 := by positivity
  refine ⟨fun k ↦ min (ρ k) ((1 / 2) ^ (k + 1) / ((m k : ℝ) + 1)),
    fun k ↦ lt_min (hρ k) (div_pos (by positivity) (hmpos k)), fun k ↦ min_le_left _ _,
    fun k ↦ ?_⟩
  have h := min_le_right (ρ k) ((1 / 2) ^ (k + 1) / ((m k : ℝ) + 1))
  calc min (ρ k) ((1 / 2) ^ (k + 1) / ((m k : ℝ) + 1)) * ((m k : ℝ) + 1)
      ≤ (1 / 2) ^ (k + 1) / ((m k : ℝ) + 1) * ((m k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h (hmpos k).le
    _ = (1 / 2) ^ (k + 1) := div_mul_cancel₀ _ (hmpos k).ne'

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- The construction in De Wilde's theorem, up to the point where the closedness of the
relation is used. For a continuous seminorm `p` and neighbourhoods `B n` of zero in `E` it
gives sets `T n ⊆ E` and `Z n ⊆ F` such that every point of `T n` is related to a point of
`Z n`, the sets `Z n` shrink to zero, and every point `y₀` of the closure of
`G[p.closedBall 0 1]` comes with a convergent sequence `α n → a` in `F`, `p a ≤ 3`, and
remainders `r n` in the closure of `T n` and in `B n`, with `(α n, y₀ - r n) ∈ G`. -/
private theorem exists_approx {C : List ℕ → Set F} (hC : IsCompletingWeb C)
    (hne : ¬IsMeagre (Prod.snd '' (G : Set (F × E)))) {p : Seminorm 𝕜 F} (hp : Continuous p)
    {B : ℕ → Set E} (hB : ∀ n, B n ∈ 𝓝 (0 : E)) :
    ∃ (T : ℕ → Set E) (Z : ℕ → Set F),
      closure (SetRel.image (G : Set (F × E)) (p.closedBall 0 1)) ∈ 𝓝 (0 : E) ∧
      (∀ n, ∀ t ∈ T n, ∃ ξ ∈ Z n, (ξ, t) ∈ G) ∧
      (∀ W ∈ 𝓝 (0 : F), ∀ᶠ n in atTop, Z n ⊆ W) ∧
      ∀ y₀ ∈ closure (SetRel.image (G : Set (F × E)) (p.closedBall 0 1)),
        ∃ (a : F) (α : ℕ → F) (r : ℕ → E), p a ≤ 3 ∧ Tendsto α atTop (𝓝 a) ∧
          (∀ n, (α n, y₀ - r n) ∈ G) ∧ ∀ n, r n ∈ closure (T n) ∩ B n := by
  -- Step 1: a strand along which all images are non-meagre, with its radii.
  obtain ⟨σ, hσ⟩ := exists_forall_not_isMeagre_res
    (T := fun l ↦ SetRel.image (G : Set (F × E)) (C l))
    (by rwa [hC.nil, G.relImage_univ])
    (by
      rintro l y ⟨x, hx, h⟩
      obtain ⟨n, hn⟩ := hC.toIsWeb.exists_mem_cons hx
      exact mem_iUnion.mpr ⟨n, x, hn, h⟩)
  obtain ⟨ρ, hρ, hconvseries⟩ := hC.exists_radius σ
  -- Step 2: integers `m k` with `G[C (res σ (k + 1)) ∩ p.closedBall 0 (m k + 1)]` non-meagre.
  have hm (k : ℕ) := G.exists_nat_not_isMeagre_relImage_inter_closedBall p (hσ (k + 1))
  choose m hm using hm
  -- The sets `N k` need not be convex; translate them by one of their points `b k` so that
  -- the closure becomes a neighbourhood of zero.
  choose b hbN hbnhds using fun k ↦ exists_mem_closure_image_sub_mem_nhds_zero (hm k)
  choose z' hz' hbG using hbN
  -- Step 3: the coefficients `ν k`.
  obtain ⟨ν, hνpos, hνρ, hνm⟩ := exists_coeff_mul_le_half_pow hρ m
  have hνseries (x : ℕ → F) (hx : ∀ k, x k ∈ C (res σ (k + 1))) :
      ∃ s : F, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, ν k • x k) atTop (𝓝 s) :=
    hconvseries x ν hx fun k ↦ ⟨(hνpos k).le, hνρ k⟩
  -- Step 4: the sets `S k` whose closures are neighbourhoods of zero.
  let S : ℕ → Set E := fun k ↦ Nat.casesOn k (SetRel.image (G : Set (F × E)) (p.closedBall 0 1))
    fun k ↦ ν k • ((fun w ↦ w - b k) '' SetRel.image (G : Set (F × E))
      (C (res σ (k + 1)) ∩ p.closedBall 0 ((m k : ℝ) + 1)))
  have hS0 : closure (S 0) ∈ 𝓝 (0 : E) := G.closure_relImage_closedBall_mem_nhds_zero hne p
  have hSsucc (k : ℕ) : closure (S (k + 1)) ∈ 𝓝 (0 : E) := by
    have hsc := (set_smul_mem_nhds_zero_iff (hνpos k).ne').mpr (hbnhds k)
    refine mem_of_superset hsc ?_
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_closure (continuous_const_smul (ν k)) hx fun w hw ↦ ⟨w, hw, rfl⟩
  have hS (k : ℕ) : closure (S k) ∈ 𝓝 (0 : E) := by
    cases k with
    | zero => exact hS0
    | succ k => exact hSsucc k
  -- The points of `S (k + 1)` are related to differences of points of `ν k • C (res σ (k + 1))`.
  have hrel (k : ℕ) (t : E) (ht : t ∈ S (k + 1)) : ∃ ζ ∈ C (res σ (k + 1)),
      p ζ ≤ (m k : ℝ) + 1 ∧ (ν k • ζ - ν k • z' k, t) ∈ G := by
    obtain ⟨_, ⟨w, ⟨ζ, ⟨hζC, hζp⟩, hζw⟩, rfl⟩, rfl⟩ := ht
    refine ⟨ζ, hζC, p.mem_closedBall_zero.mp hζp, ?_⟩
    have h := G.sub_mem (G.smul_of_tower_mem (ν k) hζw) (G.smul_of_tower_mem (ν k) (hbG k))
    simpa [smul_sub] using h
  refine ⟨fun n ↦ S (n + 1), fun n ↦ {ξ | ∃ ζ ∈ C (res σ (n + 1)), ξ = ν n • ζ - ν n • z' n},
    hS0, fun n t ht ↦ ?_, fun W hW ↦ ?_, fun y₀ hy₀ ↦ ?_⟩
  · obtain ⟨ζ, hζC, -, hζ⟩ := hrel n t ht
    exact ⟨_, ⟨ζ, hζC, rfl⟩, hζ⟩
  · -- The sets `ν n • C (res σ (n + 1))` shrink to zero, Köthe II §35.1.(3).
    obtain ⟨W', hW', hsub⟩ := exists_nhds_half_neg hW
    obtain ⟨k₀, hk₀⟩ := hC.toIsWeb.exists_forall_smul_subset_of_tendsto hνseries hW'
    refine eventually_atTop.mpr ⟨k₀, fun n hn ↦ ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hsub _ (hk₀ n hn (smul_mem_smul_set hζ)) _ (hk₀ n hn (smul_mem_smul_set (hz' n).1))
  · obtain ⟨y, hyS, hrem⟩ := exists_seq_mem_sub_sum_mem_closure hS hB hy₀
    obtain ⟨x₀, hx₀p, hx₀G⟩ : y 0 ∈ SetRel.image (G : Set (F × E)) (p.closedBall 0 1) := hyS 0
    choose z hzC hzp hzG using fun k ↦ hrel k (y (k + 1)) (hyS (k + 1))
    obtain ⟨s, hs⟩ := hνseries z hzC
    obtain ⟨s', hs'⟩ := hνseries z' fun k ↦ (hz' k).1
    -- The sums have `p ≤ 1`, by passing to the limit in the estimate for the partial sums.
    have hpartial (z : ℕ → F) (hzp : ∀ k, p (z k) ≤ (m k : ℝ) + 1) (n : ℕ) :
        p (∑ k ∈ Finset.range n, ν k • z k) ≤ 1 := by
      calc p (∑ k ∈ Finset.range n, ν k • z k)
          ≤ ∑ k ∈ Finset.range n, p (ν k • z k) :=
            Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
        _ ≤ ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) := by
            refine Finset.sum_le_sum fun k _ ↦ ?_
            rw [p.map_real_smul_eq_abs_mul, abs_of_pos (hνpos k)]
            exact (mul_le_mul_of_nonneg_left (hzp k) (hνpos k).le).trans (hνm k)
        _ ≤ 1 := sum_half_pow_succ_le_one n
    have hps : p s ≤ 1 :=
      le_of_tendsto ((hp.tendsto s).comp hs) (Eventually.of_forall (hpartial z hzp))
    have hps' : p s' ≤ 1 :=
      le_of_tendsto ((hp.tendsto s').comp hs') (Eventually.of_forall
        (hpartial z' fun k ↦ p.mem_closedBall_zero.mp (hz' k).2))
    refine ⟨x₀ + (s - s'),
      fun n ↦ x₀ + (∑ k ∈ Finset.range n, ν k • z k - ∑ k ∈ Finset.range n, ν k • z' k),
      fun n ↦ y₀ - ∑ k ∈ Finset.range (n + 1), y k, ?_, tendsto_const_nhds.add (hs.sub hs'),
      fun n ↦ ?_, hrem⟩
    · have h1 := map_add_le_add p x₀ (s - s')
      have h2 := map_sub_le_add p s s'
      have h3 : p x₀ ≤ 1 := p.mem_closedBall_zero.mp hx₀p
      linarith
    · -- The partial sums are related by `G`.
      have hsumG (n : ℕ) : (∑ k ∈ Finset.range n, (ν k • z k - ν k • z' k),
          ∑ k ∈ Finset.range n, y (k + 1)) ∈ G := by
        induction n with
        | zero =>
          rw [Finset.sum_range_zero, Finset.sum_range_zero]
          exact G.zero_mem
        | succ n ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ← Prod.mk_add_mk]
          exact G.add_mem ih (hzG n)
      have h := G.add_mem hx₀G (hsumG n)
      rw [Prod.mk_add_mk, Finset.sum_sub_distrib] at h
      rwa [sub_sub_cancel, Finset.sum_range_succ', add_comm (∑ k ∈ Finset.range n, y (k + 1))]

omit [IsTopologicalAddGroup E] in
/-- From the estimate `closure G[p.closedBall 0 1] ⊆ G[p.closedBall 0 3]` for continuous
seminorms `p` to neighbourhoods of zero. -/
private theorem image_mem_nhds_zero_of_forall_seminorm [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F]
    (h : ∀ p : Seminorm 𝕜 F, Continuous p →
      closure (SetRel.image (G : Set (F × E)) (p.closedBall 0 1)) ∈ 𝓝 (0 : E) ∧
      closure (SetRel.image (G : Set (F × E)) (p.closedBall 0 1)) ⊆
        SetRel.image (G : Set (F × E)) (p.closedBall 0 3))
    {V : Set F} (hV : V ∈ 𝓝 (0 : F)) : SetRel.image (G : Set (F × E)) V ∈ 𝓝 (0 : E) := by
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  obtain ⟨p, hp, hpV⟩ := exists_continuous_seminorm_ball_subset (𝕜 := 𝕜) hV
  obtain ⟨h1, h2⟩ := h p hp
  have h3 : (4 : ℝ)⁻¹ • SetRel.image (G : Set (F × E)) (p.closedBall 0 3) ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff (by norm_num : (4 : ℝ)⁻¹ ≠ 0)).mpr (mem_of_superset h1 h2)
  refine mem_of_superset h3 ((G.smul_relImage_subset _ _).trans (SetRel.image_mono ?_))
  rintro _ ⟨x, hx, rfl⟩
  refine hpV (p.mem_ball_zero.mpr ?_)
  have hsm : p ((4 : ℝ)⁻¹ • x) = 4⁻¹ * p x := by
    rw [← algebraMap_smul 𝕜 (4 : ℝ)⁻¹ x, map_smul_eq_mul, RCLike.algebraMap_eq_ofReal,
      RCLike.norm_ofReal, abs_of_pos (by norm_num)]
  change p ((4 : ℝ)⁻¹ • x) < 1
  rw [hsm]
  have := p.mem_closedBall_zero.mp hx
  linarith

variable [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- **De Wilde's theorem for a sequentially closed linear relation**: let `G` be a sequentially
closed linear subspace of `F × E`, with `F` a webbed locally convex space and `E` a
first-countable topological vector space, whose projection to `E` is not meagre. Then the image
`G[V]` of every neighbourhood `V` of zero in `F` is a neighbourhood of zero in `E`.
Köthe II §35.2.(1) and §35.3.(4). -/
theorem Submodule.image_mem_nhds_zero_of_isSeqClosed [FirstCountableTopology E]
    (hG : IsSeqClosed (G : Set (F × E))) (hne : ¬IsMeagre (Prod.snd '' (G : Set (F × E))))
    {V : Set F} (hV : V ∈ 𝓝 (0 : F)) : SetRel.image (G : Set (F × E)) V ∈ 𝓝 (0 : E) := by
  obtain ⟨C, hC⟩ := WebbedSpace.exists_isCompletingWeb (E := F)
  refine image_mem_nhds_zero_of_forall_seminorm G (fun p hp ↦ ?_) hV
  obtain ⟨b, hb⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨T, Z, h0, -, -, h⟩ := exists_approx G hC hne hp hb.mem
  refine ⟨h0, fun y₀ hy₀ ↦ ?_⟩
  obtain ⟨a, α, r, hpa, hα, hαG, hr⟩ := h y₀ hy₀
  -- The remainders tend to zero, so `(α n, y₀ - r n)` tends to `(a, y₀)`.
  have hr0 : Tendsto r atTop (𝓝 (0 : E)) := hb.tendsto fun n ↦ (hr n).2
  have hy : Tendsto (fun n ↦ y₀ - r n) atTop (𝓝 y₀) := by
    have h := (tendsto_const_nhds (x := y₀)).sub hr0
    rwa [sub_zero] at h
  exact ⟨a, p.mem_closedBall_zero.mpr hpa, hG hαG (hα.prodMk_nhds hy)⟩

/-- **De Wilde's theorem for a closed linear relation**: let `G` be a closed linear subspace of
`F × E`, with `F` a webbed locally convex space and `E` a topological vector space, whose
projection to `E` is not meagre. Then the image `G[V]` of every neighbourhood `V` of zero in
`F` is a neighbourhood of zero in `E`. Köthe II §35.2.(3) and §35.3.(2). -/
theorem Submodule.image_mem_nhds_zero_of_isClosed (hG : IsClosed (G : Set (F × E)))
    (hne : ¬IsMeagre (Prod.snd '' (G : Set (F × E)))) {V : Set F} (hV : V ∈ 𝓝 (0 : F)) :
    SetRel.image (G : Set (F × E)) V ∈ 𝓝 (0 : E) := by
  obtain ⟨C, hC⟩ := WebbedSpace.exists_isCompletingWeb (E := F)
  refine image_mem_nhds_zero_of_forall_seminorm G (fun p hp ↦ ?_) hV
  obtain ⟨T, Z, h0, hTZ, hZ, h⟩ :=
    exists_approx G hC hne hp (B := fun _ ↦ univ) fun _ ↦ univ_mem
  refine ⟨h0, fun y₀ hy₀ ↦ ?_⟩
  obtain ⟨a, α, r, hpa, hα, hαG, hr⟩ := h y₀ hy₀
  refine ⟨a, p.mem_closedBall_zero.mpr hpa, ?_⟩
  -- Every neighbourhood of `(a, y₀)` meets `G`, which is closed.
  rw [← hG.closure_eq, mem_closure_iff_nhds]
  intro O hO
  obtain ⟨O₁, hO₁, O₂, hO₂, hO12⟩ := mem_nhds_prod_iff.mp hO
  -- Split `O₁` as `W₁ + W₂` with `W₁` a neighbourhood of `a` and `W₂` one of zero.
  have hadd : Tendsto (fun q : F × F ↦ q.1 + q.2) (𝓝 (a, 0)) (𝓝 a) := by
    have h := (continuous_add (M := F)).tendsto (a, 0)
    rwa [add_zero] at h
  obtain ⟨W₁, hW₁, W₂, hW₂, hW12⟩ := mem_nhds_prod_iff.mp (hadd hO₁)
  obtain ⟨n, hn1, hn2⟩ := ((hα.eventually hW₁).and (hZ W₂ hW₂)).exists
  -- Approximate the remainder `r n` by a point `t` of `T n`.
  have hc : ContinuousAt (fun t : E ↦ y₀ - r n + t) (r n) := by fun_prop
  have hpre : (fun t : E ↦ y₀ - r n + t) ⁻¹' O₂ ∈ 𝓝 (r n) :=
    hc.preimage_mem_nhds (by simpa using hO₂)
  obtain ⟨t, ht, htT⟩ := mem_closure_iff_nhds.mp (hr n).1 _ hpre
  obtain ⟨ξ, hξZ, hξG⟩ := hTZ n t htT
  exact ⟨(α n + ξ, y₀ - r n + t), hO12 ⟨hW12 (show (α n, ξ) ∈ W₁ ×ˢ W₂ from ⟨hn1, hn2 hξZ⟩), ht⟩,
    G.add_mem (hαG n) hξG⟩

end Relation

section Hull

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {X : ι → Type*} {E F : Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, IsTopologicalAddGroup (X i)] [∀ i, ContinuousSMul 𝕜 (X i)]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F]

/-- The passage to locally convex hulls in De Wilde's theorems. Let `E` carry the final locally
convex topology of a family `f i : X i → E`, and let `G` be a linear subspace of `F × E` whose
projection is all of `E`. If the pullback of `G` to each `F × X i` maps neighbourhoods of zero
to neighbourhoods of zero, then so does `G`. -/
theorem Submodule.image_mem_nhds_zero_of_locallyConvexFinalTopology (f : ∀ i, X i →ₗ[𝕜] E)
    (G : Submodule 𝕜 (F × E)) (hsurj : Prod.snd '' (G : Set (F × E)) = univ)
    (h : ∀ i, ∀ V ∈ 𝓝 (0 : F), SetRel.image
      ((G.comap (LinearMap.prodMap LinearMap.id (f i)) : Submodule 𝕜 (F × X i)) :
        Set (F × X i)) V ∈ 𝓝 (0 : X i))
    {V : Set F} (hV : V ∈ 𝓝 (0 : F)) :
    SetRel.image (G : Set (F × E)) V ∈ @nhds E (locallyConvexFinalTopology f) 0 := by
  obtain ⟨V', ⟨hV', hV'c, hV'b⟩, hV'V⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  have hmem := locallyConvexFinalTopology.mem_nhds_zero f (G.convex_relImage hV'c)
    (G.balanced_relImage hV'b) (G.absorbent_relImage (absorbent_nhds_zero hV') hsurj)
    fun i ↦ mem_of_superset (h i V' hV') ?_
  · exact @mem_of_superset E (@nhds E (locallyConvexFinalTopology f) 0) _ _ hmem
      (SetRel.image_mono hV'V)
  · rintro e ⟨x, hx, hxe⟩
    exact ⟨x, hx, hxe⟩

end Hull

section Ultrabornological

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type u} {F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [UltrabornologicalSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F]

/-- **De Wilde's theorem for an ultrabornological space**: let `G` be a sequentially closed
linear subspace of `F × E`, with `F` a webbed locally convex space and `E` ultrabornological,
whose projection is all of `E`. Then the image `G[V]` of every neighbourhood `V` of zero in `F`
is a neighbourhood of zero in `E`. Köthe II §35.2.(2) and §35.3.(5), (6). -/
theorem Submodule.image_mem_nhds_zero_of_ultrabornologicalSpace (G : Submodule 𝕜 (F × E))
    (hG : IsSeqClosed (G : Set (F × E))) (hsurj : Prod.snd '' (G : Set (F × E)) = univ)
    {V : Set F} (hV : V ∈ 𝓝 (0 : F)) : SetRel.image (G : Set (F × E)) V ∈ 𝓝 (0 : E) := by
  obtain ⟨V', ⟨hV', hV'c, hV'b⟩, hV'V⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  refine mem_of_superset (UltrabornologicalSpace.mem_nhds_zero (G.convex_relImage hV'c)
    (G.balanced_relImage hV'b) (G.absorbent_relImage (absorbent_nhds_zero hV') hsurj)
    fun X _ _ _ f ↦ ?_) (SetRel.image_mono hV'V)
  -- The pullback of `G` to the complete seminormed space `X` is sequentially closed with full
  -- projection, so De Wilde's theorem applies on `X`.
  let _ : Module ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X |>.toModule
  have : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
  have : ContinuousSMul ℝ X := IsScalarTower.continuousSMul 𝕜
  have hcont : Continuous (LinearMap.prodMap (LinearMap.id : F →ₗ[𝕜] F) f.toLinearMap) :=
    continuous_fst.prodMk (f.continuous.comp continuous_snd)
  let Gf := G.comap (LinearMap.prodMap LinearMap.id f.toLinearMap)
  have huniv : Prod.snd '' (Gf : Set (F × X)) = univ := by
    refine eq_univ_of_forall fun e ↦ ?_
    obtain ⟨q, hq, hqe⟩ : f e ∈ Prod.snd '' (G : Set (F × E)) := hsurj ▸ mem_univ _
    refine ⟨(q.1, e), ?_, rfl⟩
    change (q.1, f e) ∈ G
    rw [← hqe]
    exact hq
  have hne : ¬IsMeagre (Prod.snd '' (Gf : Set (F × X))) := by
    rw [huniv]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  refine mem_of_superset (Submodule.image_mem_nhds_zero_of_isSeqClosed Gf
    (hG.preimage hcont.seqContinuous) hne hV') ?_
  rintro x ⟨v, hv, hvx⟩
  exact ⟨v, hv, hvx⟩

end Ultrabornological
