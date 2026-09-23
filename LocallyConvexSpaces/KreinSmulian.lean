/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.CompactConvergenceDual

/-!
# The Banach–Dieudonné and Krein–Šmulian theorems

Let `E` be a topological vector space with dual `E'`. A subset `C` of `E'` is called *almost
weak-\* closed* here if `C ∩ U°` is weak-\* closed for every neighbourhood `U` of zero in `E`,
where `U°` is the polar of `U`. (The literature also says *nearly closed* or *aw\*-closed*.)
Since polars of neighbourhoods of zero are weak-\* compact (Alaoglu–Bourbaki) and every
equicontinuous set lies in such a polar, this says that `C` meets every equicontinuous weak-\*
closed set in a weak-\* closed set.

The **Krein–Šmulian theorem** says that in the dual of a Fréchet space every almost weak-\*
closed *convex* set is weak-\* closed. Applied to linear subspaces, this implies that Fréchet
spaces are `B`-complete (Pták spaces), which is what is needed to apply Pták's open mapping and
closed graph theorems to
Fréchet spaces. It follows from the **Banach–Dieudonné theorem**: in the dual of a metrizable
space, if the complement of `W` is almost weak-\* closed and `0 ∈ W`, then `W` contains the polar
of a compact set; in other words the finest topology on `E'` that agrees with the weak-\*
topology on equicontinuous sets is coarser than the topology of compact convergence at zero.

## Main definitions

* `StrongDual.IsAlmostWeakStarClosed C`: the set `C` of continuous linear functionals meets the
  polar of every neighbourhood of zero in a weak-\* closed set.

## Main statements

* `StrongDual.IsAlmostWeakStarClosed.of_isClosed`: weak-\* closed sets are almost weak-\* closed.
* `StrongDual.IsAlmostWeakStarClosed.inter`, `StrongDual.isAlmostWeakStarClosed_polar`: basic
  stability properties.
* `StrongDual.exists_isCompact_polar_subset`: the **Banach–Dieudonné theorem**.
* `StrongDual.IsAlmostWeakStarClosed.preimage_add_right`: translates of almost weak-\* closed
  sets are almost weak-\* closed.
* `StrongDual.isClosed_of_isAlmostWeakStarClosed`: the **Krein–Šmulian theorem**.

## Implementation notes

Sets of functionals are subsets of `StrongDual 𝕜 E`, and weak-\* closedness of `C` is expressed
as `IsClosed (WeakDual.toStrongDual ⁻¹' C)`. This is how Mathlib defines `WeakDual.polar`. It
keeps convexity hypotheses on `StrongDual 𝕜 E`, where the algebraic instances are the standard
ones; see the implementation notes of `LocallyConvexSpaces.Bipolar` for the difficulty with
convexity of subsets of `WeakDual 𝕜 E`.

## Outline of the proofs

Both theorems are classical; the statements and proofs follow [Schaefer–Wolff][schaefer1999],
IV §6.3 and IV §6.4.

*Banach–Dieudonné.* Take an antitone basis `U n` of neighbourhoods of zero with `U 0 = univ`.
Construct finite sets `F n ⊆ U n` such that, with `H n = F 0 ∪ … ∪ F (n - 1)`, one has
`(H n)° ∩ (U n)° ⊆ W`. For `n = 0` this is `{0} ⊆ W`. For the step, if no finite `F ⊆ U n`
works then the sets `(H n ∪ F)° ∩ (U (n + 1))° ∩ Wᶜ` are nonempty, weak-\* closed in the weak-\*
compact set `(U (n + 1))°` (`WeakDual.isCompact_polar_of_mem_nhds`), and directed, so they have
a common point `φ`; then `φ ∈ (U n)°`, hence `φ ∈ (H n)° ∩ (U n)° ⊆ W`, a contradiction. The
union `S` of the `F n` together with `0` is compact, because every neighbourhood of zero contains
all but finitely many of its points, and `S° ⊆ W` because every `φ` lies in some `(U m)°`.

*Krein–Šmulian.* Let `C` be convex and almost weak-\* closed and `ψ ∉ C`. After a translation,
which preserves almost weak-\* closedness, `ψ = 0`. By Banach–Dieudonné there is a compact `S`
with `S° ∩ C = ∅`. The interior of `S°` for the topology of compact convergence is an open
convex set containing zero, so the geometric Hahn–Banach theorem separates it from `C` by a
functional `Λ` on `E'` that is continuous for compact convergence. Because `E` is complete, `Λ`
is evaluation at a point `x` of `E`. These two steps are
`CompactConvergenceCLM.exists_pos_le_re_apply` in `LocallyConvexSpaces.CompactConvergenceDual`.
Hence `C` lies in a weak-\* closed half-space that does not contain `0`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §6
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.10
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], IV §3.5

## Tags

Krein–Šmulian, Banach–Dieudonné, weak-* topology, equicontinuous, B-complete, Pták space
-/

public section

open Set Filter

open scoped Topology Pointwise CompactConvergenceCLM

namespace StrongDual

section Defs

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A set `C` of continuous linear functionals on `E` is *almost weak-\* closed* if its
intersection with the polar of every neighbourhood of zero in `E` is weak-\* closed. -/
@[expose]
def IsAlmostWeakStarClosed (C : Set (StrongDual 𝕜 E)) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), IsClosed (WeakDual.toStrongDual ⁻¹' (C ∩ polar 𝕜 U))

variable {C D : Set (StrongDual 𝕜 E)}

/-- A weak-\* closed set is almost weak-\* closed. -/
theorem IsAlmostWeakStarClosed.of_isClosed (hC : IsClosed (WeakDual.toStrongDual ⁻¹' C)) :
    IsAlmostWeakStarClosed C := fun U _ ↦ by
  rw [preimage_inter]
  exact hC.inter (WeakDual.isClosed_polar 𝕜 U)

/-- The intersection of two almost weak-\* closed sets is almost weak-\* closed. -/
theorem IsAlmostWeakStarClosed.inter (hC : IsAlmostWeakStarClosed C)
    (hD : IsAlmostWeakStarClosed D) : IsAlmostWeakStarClosed (C ∩ D) := fun U hU ↦ by
  have h : C ∩ D ∩ polar 𝕜 U = (C ∩ polar 𝕜 U) ∩ (D ∩ polar 𝕜 U) := by
    ext φ
    simp only [mem_inter_iff]
    tauto
  rw [h, preimage_inter]
  exact (hC U hU).inter (hD U hU)

/-- Polars are almost weak-\* closed. -/
theorem isAlmostWeakStarClosed_polar (s : Set E) : IsAlmostWeakStarClosed (polar 𝕜 s) :=
  .of_isClosed (WeakDual.isClosed_polar 𝕜 s)

/-- The whole dual is almost weak-\* closed. -/
theorem isAlmostWeakStarClosed_univ : IsAlmostWeakStarClosed (univ : Set (StrongDual 𝕜 E)) :=
  .of_isClosed (by simp)

/-- The preimage of an almost weak-\* closed set under a translation is almost weak-\*
closed. -/
theorem IsAlmostWeakStarClosed.preimage_add_right [ContinuousSMul 𝕜 E]
    (hC : IsAlmostWeakStarClosed C) (ψ : StrongDual 𝕜 E) :
    IsAlmostWeakStarClosed {φ : StrongDual 𝕜 E | φ + ψ ∈ C} := by
  intro U hU
  -- If `φ ∈ U°` then `φ + ψ ∈ V°`, where `V` is a small multiple of `U ∩ {x | ‖ψ x‖ ≤ 1}`.
  have hN : {x : E | ‖ψ x‖ ≤ 1} ∈ 𝓝 (0 : E) := by
    have h : ContinuousAt (fun x ↦ ‖ψ x‖) 0 := ψ.continuous.norm.continuousAt
    have h1 : Iic (1 : ℝ) ∈ 𝓝 (‖ψ 0‖) := by
      rw [map_zero, norm_zero]
      exact Iic_mem_nhds one_pos
    exact h.preimage_mem_nhds h1
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 2
  have hcpos : 0 < ‖c‖ := two_pos.trans hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hV : c⁻¹ • (U ∩ {x : E | ‖ψ x‖ ≤ 1}) ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff (inv_ne_zero hc0)).mpr (inter_mem hU hN)
  let g : WeakDual 𝕜 E → WeakDual 𝕜 E := fun χ ↦
    StrongDual.toWeakDual (WeakDual.toStrongDual χ + ψ)
  have hg : Continuous g := WeakDual.continuous_of_continuous_eval fun x ↦ by
    change Continuous fun χ : WeakDual 𝕜 E ↦ χ x + ψ x
    exact (WeakDual.eval_continuous x).add continuous_const
  have hbound (φ : StrongDual 𝕜 E) (hφ : φ ∈ polar 𝕜 U) :
      φ + ψ ∈ polar 𝕜 (c⁻¹ • (U ∩ {x : E | ‖ψ x‖ ≤ 1})) := by
    rintro _ ⟨x, ⟨hxU, hxN⟩, rfl⟩
    change ‖(φ + ψ) (c⁻¹ • x)‖ ≤ 1
    rw [map_smul, norm_smul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
    calc ‖(φ + ψ) x‖ ≤ ‖φ x‖ + ‖ψ x‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add (hφ x hxU) hxN
      _ ≤ ‖c‖ := by linarith
  have key : WeakDual.toStrongDual ⁻¹' ({φ : StrongDual 𝕜 E | φ + ψ ∈ C} ∩ polar 𝕜 U) =
      g ⁻¹' (WeakDual.toStrongDual ⁻¹'
        (C ∩ polar 𝕜 (c⁻¹ • (U ∩ {x : E | ‖ψ x‖ ≤ 1})))) ∩
        WeakDual.toStrongDual ⁻¹' polar 𝕜 U := by
    ext χ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, hbound _ h2⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [key]
  exact ((hC _ hV).preimage hg).inter (WeakDual.isClosed_polar 𝕜 U)

end Defs

section BanachDieudonne

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [FirstCountableTopology E]

omit [FirstCountableTopology E] in
/-- The inductive step of the Banach–Dieudonné theorem. Suppose that the complement of `W` is
almost weak-\* closed, that `V` is a neighbourhood of zero and that `H° ∩ U° ⊆ W`. Then there is
a finite subset `F` of `U` with `(H ∪ F)° ∩ V° ⊆ W`. -/
theorem exists_finset_polar_union_inter_subset {W : Set (StrongDual 𝕜 E)}
    (hW : IsAlmostWeakStarClosed Wᶜ) {U V : Set E} (hV : V ∈ 𝓝 (0 : E)) {H : Set E}
    (hH : polar 𝕜 H ∩ polar 𝕜 U ⊆ W) :
    ∃ F : Finset E, (F : Set E) ⊆ U ∧ polar 𝕜 (H ∪ F) ∩ polar 𝕜 V ⊆ W := by
  classical
  by_contra hcon
  push Not at hcon
  -- The sets `Z F`, for finite `F ⊆ U`, are nonempty, weak-* compact and directed.
  let ι := {F : Finset E // (F : Set E) ⊆ U}
  let Z : ι → Set (WeakDual 𝕜 E) := fun F ↦
    WeakDual.toStrongDual ⁻¹' (polar 𝕜 (H ∪ (F.1 : Set E)) ∩ (Wᶜ ∩ polar 𝕜 V))
  have hne (F : ι) : (Z F).Nonempty := by
    obtain ⟨φ, hφ, hφW⟩ := Set.not_subset.mp (hcon F.1 F.2)
    exact ⟨StrongDual.toWeakDual φ, hφ.1, hφW, hφ.2⟩
  have hclosed (F : ι) : IsClosed (Z F) :=
    (WeakDual.isClosed_polar 𝕜 (H ∪ (F.1 : Set E))).inter (hW V hV)
  have hcompact (F : ι) : IsCompact (Z F) :=
    (WeakDual.isCompact_polar_of_mem_nhds hV).of_isClosed_subset (hclosed F)
      fun ψ hψ ↦ hψ.2.2
  have hdir : Directed (· ⊇ ·) Z := fun F₁ F₂ ↦
    ⟨⟨F₁.1 ∪ F₂.1, by
      rw [Finset.coe_union]
      exact union_subset F₁.2 F₂.2⟩,
      fun ψ hψ ↦ ⟨fun x hx ↦ hψ.1 x (hx.imp_right fun h ↦ by simp [h]), hψ.2⟩,
      fun ψ hψ ↦ ⟨fun x hx ↦ hψ.1 x (hx.imp_right fun h ↦ by simp [h]), hψ.2⟩⟩
  have : Nonempty ι := ⟨⟨∅, by simp⟩⟩
  obtain ⟨ψ, hψ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed Z hdir hne hcompact hclosed
  rw [mem_iInter] at hψ
  -- The common point lies in `H° ∩ U°` but not in `W`.
  have hφW : WeakDual.toStrongDual ψ ∈ Wᶜ := (hψ ⟨∅, by simp⟩).2.1
  refine hφW (hH ⟨fun x hx ↦ (hψ ⟨∅, by simp⟩).1 x (Or.inl hx), fun x hx ↦ ?_⟩)
  exact (hψ ⟨{x}, by simpa using hx⟩).1 x (Or.inr (by simp))

/-- The **Banach–Dieudonné theorem**. Let `E` be a first-countable topological vector space and
let `W` be a set of continuous linear functionals that contains zero and whose complement is
almost weak-\* closed. Then `W` contains the polar of a compact subset of `E`. -/
theorem exists_isCompact_polar_subset {W : Set (StrongDual 𝕜 E)} (hW0 : (0 : StrongDual 𝕜 E) ∈ W)
    (hW : IsAlmostWeakStarClosed Wᶜ) : ∃ S : Set E, IsCompact S ∧ polar 𝕜 S ⊆ W := by
  classical
  -- An antitone basis of neighbourhoods of zero, preceded by the whole space.
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  let V : ℕ → Set E := fun n ↦ n.casesOn univ U
  have hVmem (n : ℕ) : V n ∈ 𝓝 (0 : E) := by
    cases n with
    | zero => exact univ_mem
    | succ n => exact hU.mem n
  have hVanti : Antitone V := antitone_nat_of_succ_le fun n ↦ by
    cases n with
    | zero => exact subset_univ _
    | succ n => exact hU.antitone (Nat.le_succ n)
  have hVbasis {N : Set E} (hN : N ∈ 𝓝 (0 : E)) : ∃ m, V m ⊆ N := by
    obtain ⟨k, hk⟩ := hU.mem_iff.mp hN
    exact ⟨k + 1, hk⟩
  -- The recursive construction of the finite sets.
  have step (n : ℕ) (H : Set E) (hH : H.Finite ∧ polar 𝕜 H ∩ polar 𝕜 (V n) ⊆ W) :
      ∃ F : Finset E, (F : Set E) ⊆ V n ∧ polar 𝕜 (H ∪ F) ∩ polar 𝕜 (V (n + 1)) ⊆ W :=
    exists_finset_polar_union_inter_subset hW (hVmem (n + 1)) hH.2
  have base : polar 𝕜 (∅ : Set E) ∩ polar 𝕜 (V 0) ⊆ W := by
    rintro φ ⟨-, hφ⟩
    have h0 : φ = 0 := by
      have := polar_univ (𝕜 := 𝕜) (E := E)
      exact (this ▸ hφ : φ ∈ ({0} : Set (StrongDual 𝕜 E)))
    rw [h0]
    exact hW0
  let G : (n : ℕ) → {H : Set E // H.Finite ∧ polar 𝕜 H ∩ polar 𝕜 (V n) ⊆ W} := fun n ↦
    Nat.rec (motive := fun n ↦ {H : Set E // H.Finite ∧ polar 𝕜 H ∩ polar 𝕜 (V n) ⊆ W})
      ⟨∅, finite_empty, base⟩
      (fun n Hn ↦ ⟨Hn.1 ∪ ((Classical.choose (step n Hn.1 Hn.2) : Finset E) : Set E),
        Hn.2.1.union (Finset.finite_toSet _), (Classical.choose_spec (step n Hn.1 Hn.2)).2⟩) n
  let F : ℕ → Finset E := fun n ↦ Classical.choose (step n (G n).1 (G n).2)
  have hF (n : ℕ) : (F n : Set E) ⊆ V n := (Classical.choose_spec (step n (G n).1 (G n).2)).1
  have hGsucc (n : ℕ) : (G (n + 1)).1 = (G n).1 ∪ (F n : Set E) := rfl
  have hGmono : Monotone fun n ↦ (G n).1 := monotone_nat_of_le_succ fun n ↦ by
    rw [hGsucc]
    exact subset_union_left
  -- Everything that is added from stage `m` on lies in `V m`.
  have hGsub (m n : ℕ) : (G n).1 ⊆ (G m).1 ∪ V m := by
    induction n with
    | zero => exact (empty_subset _ : (∅ : Set E) ⊆ _)
    | succ n ih =>
      rw [hGsucc]
      refine union_subset ih ?_
      rcases le_or_gt m n with hmn | hmn
      · exact ((hF n).trans (hVanti hmn)).trans subset_union_right
      · exact (subset_union_right.trans (hGsucc n).ge).trans
          ((hGmono (Nat.succ_le_of_lt hmn)).trans subset_union_left)
  refine ⟨insert 0 (⋃ n, (G n).1), ?_, ?_⟩
  · -- Compactness: a neighbourhood of zero contains all but finitely many points.
    refine isCompact_of_finite_subcover fun {κ} O hO hcover ↦ ?_
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcover (mem_insert _ _))
    obtain ⟨m, hm⟩ := hVbasis ((hO i₀).mem_nhds hi₀)
    obtain ⟨t, ht⟩ := (G m).2.1.isCompact.elim_finite_subcover O hO
      ((subset_iUnion _ m).trans ((subset_insert _ _).trans hcover))
    refine ⟨insert i₀ t, ?_⟩
    rintro x (rfl | hx)
    · exact mem_biUnion (Finset.mem_insert_self _ _) hi₀
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      rcases hGsub m n hn with h | h
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht h)
        exact mem_biUnion (Finset.mem_insert_of_mem hi) hxi
      · exact mem_biUnion (Finset.mem_insert_self _ _) (hm h)
  · -- Every functional lies in the polar of some `V m`.
    intro φ hφ
    have hN : {x : E | ‖φ x‖ ≤ 1} ∈ 𝓝 (0 : E) := by
      have h : ContinuousAt (fun x ↦ ‖φ x‖) 0 := φ.continuous.norm.continuousAt
      have h1 : Iic (1 : ℝ) ∈ 𝓝 (‖φ 0‖) := by
        rw [map_zero, norm_zero]
        exact Iic_mem_nhds one_pos
      exact h.preimage_mem_nhds h1
    obtain ⟨m, hm⟩ := hVbasis hN
    exact (G m).2.2 ⟨fun x hx ↦ hφ x (mem_insert_of_mem _ (mem_iUnion.mpr ⟨m, hx⟩)),
      fun x hx ↦ hm hx⟩

end BanachDieudonne

section KreinSmulian

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E] [FirstCountableTopology E]

/-- The **Krein–Šmulian theorem**. In the dual of a complete, first-countable, locally convex
space every convex almost weak-\* closed set is weak-\* closed. -/
theorem isClosed_of_isAlmostWeakStarClosed {C : Set (StrongDual 𝕜 E)} (hC : Convex ℝ C)
    (h : IsAlmostWeakStarClosed C) : IsClosed (WeakDual.toStrongDual ⁻¹' C) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  refine isClosed_of_closure_subset fun ψ' hψ' ↦ ?_
  by_contra hψC
  -- Translate so that the point to be separated from `C` is zero.
  let ψ : StrongDual 𝕜 E := WeakDual.toStrongDual ψ'
  let D : Set (StrongDual 𝕜 E) := {φ | φ + ψ ∈ C}
  have hD : IsAlmostWeakStarClosed D := h.preimage_add_right ψ
  have hDc : Convex ℝ D := hC.translate_preimage_left ψ
  have h0 : (0 : StrongDual 𝕜 E) ∈ Dᶜ := fun h0 ↦ hψC (by simpa [D] using h0)
  -- Banach–Dieudonné: the polar of a compact set `S` misses `D`.
  obtain ⟨S, hS, hSD⟩ := exists_isCompact_polar_subset h0 (by rwa [compl_compl])
  -- Separate `D` from zero by a point `x` of `E`, using the topology of compact convergence.
  let e : StrongDual 𝕜 E ≃ₗ[𝕜] (E →L_c[𝕜] 𝕜) :=
    ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id 𝕜) 𝕜 {S : Set E | IsCompact S}
  have htc : Convex ℝ (e '' D) :=
    hDc.is_linear_image (e.toLinearMap.restrictScalars ℝ).isLinear
  have hdisj : Disjoint (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S} S) (e '' D) := by
    rw [Set.disjoint_left]
    rintro _ hf ⟨φ, hφ, rfl⟩
    exact hSD (fun x hx ↦ hf x hx) hφ
  obtain ⟨x, u, hu, hxu⟩ := CompactConvergenceCLM.exists_pos_le_re_apply hS htc hdisj
  -- The weak-* closed half-space `{χ | u ≤ re (χ x - ψ x)}` contains `C` but not `ψ`.
  have hA : IsClosed {χ : WeakDual 𝕜 E | u ≤ RCLike.re (χ x - ψ x)} :=
    isClosed_le continuous_const
      (RCLike.continuous_re.comp ((WeakDual.eval_continuous x).sub continuous_const))
  have hCA : WeakDual.toStrongDual ⁻¹' C ⊆ {χ : WeakDual 𝕜 E | u ≤ RCLike.re (χ x - ψ x)} := by
    intro χ hχ
    have hmem : WeakDual.toStrongDual χ - ψ ∈ D := by
      change WeakDual.toStrongDual χ - ψ + ψ ∈ C
      rwa [sub_add_cancel]
    exact hxu _ ⟨_, hmem, rfl⟩
  have h2 : u ≤ RCLike.re (ψ' x - ψ x) := closure_minimal hCA hA hψ'
  have h3 : ψ' x - ψ x = 0 := sub_self _
  rw [h3, map_zero] at h2
  exact (h2.trans_lt hu).false

/-- In the dual of a complete, first-countable, locally convex space a convex set is weak-\*
closed if and only if it is almost weak-\* closed. -/
theorem isClosed_iff_isAlmostWeakStarClosed {C : Set (StrongDual 𝕜 E)} (hC : Convex ℝ C) :
    IsClosed (WeakDual.toStrongDual ⁻¹' C) ↔ IsAlmostWeakStarClosed C :=
  ⟨.of_isClosed, isClosed_of_isAlmostWeakStarClosed hC⟩

end KreinSmulian

end StrongDual
