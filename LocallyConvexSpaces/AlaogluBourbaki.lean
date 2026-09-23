/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Equicontinuity

/-!
# The Alaoglu–Bourbaki theorem

For a topological vector space `E` over a nontrivially normed field `𝕜`, the polar of a
neighbourhood of zero is an equicontinuous set of functionals and, if `𝕜` is a proper space, a
compact subset of the weak-* dual `WeakDual 𝕜 E`. Conversely every equicontinuous set of
continuous linear functionals is contained in the polar of a neighbourhood of zero.

Mathlib has the compactness statement for normed spaces, `WeakDual.isCompact_polar` in
`Mathlib/Analysis/Normed/Module/WeakDual.lean`, deduced from a statement about bounded sets of
operators. Here there is no norm on `E`; the polar of `U` is identified, inside the space of all
functions `E → 𝕜` with the topology of pointwise convergence, with the closed set of functions
that are linear and bounded by one on `U`, and that set lies in a product of closed balls because
`U` is absorbent.

## Main statements

* `WeakDual.isClosed_image_coe_polar`: the image of the polar of a neighbourhood of zero under
  `↑ : WeakDual 𝕜 E → (E → 𝕜)` is closed.
* `WeakDual.isCompact_polar_of_mem_nhds`: the **Alaoglu–Bourbaki theorem**.
* `StrongDual.equicontinuous_polar`: the polar of a neighbourhood of zero is equicontinuous.
* `StrongDual.exists_mem_nhds_subset_polar`: an equicontinuous set of continuous linear
  functionals is contained in the polar of a neighbourhood of zero.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §3.4
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §4.3

## Tags

Alaoglu, Bourbaki, Banach, polar, equicontinuous, weak-* compact
-/

public section

open Set Filter Bornology Metric

open scoped Topology Pointwise

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace WeakDual

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of the polar of a neighbourhood `U` of zero is
the set of functions that are additive, homogeneous and bounded by one on `U`. -/
theorem image_coe_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    ((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 U =
      {g : E → 𝕜 | (∀ x y, g (x + y) = g x + g y) ∧ (∀ (c : 𝕜) x, g (c • x) = c • g x) ∧
        ∀ x ∈ U, ‖g x‖ ≤ 1} := by
  ext g
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨fun x y ↦ map_add φ x y, fun c x ↦ map_smul φ c x, hφ⟩
  · rintro ⟨hadd, hsmul, hg⟩
    let f : E →ₗ[𝕜] 𝕜 := { toFun := g, map_add' := hadd, map_smul' := hsmul }
    have hb : ∃ V ∈ 𝓝 (0 : E), IsVonNBounded 𝕜 (f '' V) :=
      ⟨U, hU, (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 1).subset <| by
        rintro _ ⟨x, hx, rfl⟩
        exact mem_closedBall_zero_iff.mpr (hg x hx)⟩
    exact ⟨StrongDual.toWeakDual (f.clmOfExistsBoundedImage hb), hg, rfl⟩

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of the polar of a neighbourhood of zero is
closed in the topology of pointwise convergence. For normed spaces this is
`WeakDual.isClosed_image_polar_of_mem_nhds`. -/
theorem isClosed_image_coe_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 U) := by
  rw [image_coe_polar hU]
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_).inter
    ((isClosed_iInter fun c ↦ isClosed_iInter fun x ↦ ?_).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ ?_))
  · exact isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  · exact isClosed_eq (continuous_apply (c • x)) ((continuous_apply x).const_smul c)
  · exact isClosed_le (continuous_apply x).norm continuous_const

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- Pointwise bounds on a polar follow from scalar containment in the original set, without
assuming that the set is a neighbourhood. -/
theorem image_coe_polar_subset_pi_of_mem_smul {U : Set E} {c : E → 𝕜}
    (hc : ∀ x, x ∈ c x • U) :
    ((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 U ⊆
      Set.pi univ fun x ↦ closedBall (0 : 𝕜) ‖c x‖ := by
  rintro _ ⟨φ, hφ, rfl⟩ x _
  obtain ⟨u, hu, hxu⟩ := hc x
  have hxφ : φ x = c x • φ u :=
    (congrArg φ hxu).symm.trans (map_smul φ (c x) u)
  rw [mem_closedBall_zero_iff, hxφ, norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg (c x)) (hφ u hu)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- If `x ∈ c x • U` for all `x`, then the image of the polar of `U` under
`↑ : WeakDual 𝕜 E → (E → 𝕜)` lies in the product of the closed balls of radius `‖c x‖`. -/
theorem image_coe_polar_subset_pi {U : Set E} (_hU : U ∈ 𝓝 (0 : E)) {c : E → 𝕜}
    (hc : ∀ x, x ∈ c x • U) :
    ((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 U ⊆
      Set.pi univ fun x ↦ closedBall (0 : 𝕜) ‖c x‖ :=
  image_coe_polar_subset_pi_of_mem_smul hc

/-- The **Alaoglu–Bourbaki theorem**: the polar of a neighbourhood of zero in a topological
vector space `E` over a proper nontrivially normed field is a compact subset of `WeakDual 𝕜 E`.
For normed spaces this is `WeakDual.isCompact_polar`. -/
theorem isCompact_polar_of_mem_nhds [ProperSpace 𝕜] {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 U) := by
  -- `U` is absorbent: every `x` lies in `c x • U` for some scalar `c x`.
  have habs (x : E) : ∃ c : 𝕜, x ∈ c • U :=
    ((absorbent_nhds_zero hU) x).exists.imp fun _ h ↦ singleton_subset_iff.mp h
  choose c hc using habs
  have he : Topology.IsEmbedding ((↑) : WeakDual 𝕜 E → E → 𝕜) :=
    DFunLike.coe_injective.isEmbedding_induced
  have hK : IsCompact (Set.pi univ fun x ↦ closedBall (0 : 𝕜) ‖c x‖) :=
    isCompact_univ_pi fun x ↦ ProperSpace.isCompact_closedBall (0 : 𝕜) ‖c x‖
  exact he.isCompact_iff.mpr
    (hK.of_isClosed_subset (isClosed_image_coe_polar hU) (image_coe_polar_subset_pi hU hc))

end WeakDual

namespace StrongDual

/-- The polar of a neighbourhood of zero is an equicontinuous set of functionals. -/
theorem equicontinuous_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    Equicontinuous ((↑) : polar 𝕜 U → E → 𝕜) := by
  refine equicontinuous_of_equicontinuousAt_zero (fun φ : polar 𝕜 U ↦ (φ : StrongDual 𝕜 E)) ?_
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨a, ha0, haε⟩ := NormedField.exists_norm_lt 𝕜 hε
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  filter_upwards [(set_smul_mem_nhds_zero_iff ha).mpr hU] with x hx φ
  obtain ⟨u, hu, rfl⟩ := hx
  refine hεV ?_
  change dist ((φ : StrongDual 𝕜 E) 0) ((φ : StrongDual 𝕜 E) (a • u)) < ε
  rw [map_zero, dist_zero_left, map_smul, norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (φ.2 u hu)).trans_lt haε

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- An equicontinuous set of continuous linear functionals is contained in the polar of a
neighbourhood of zero. -/
theorem exists_mem_nhds_subset_polar {A : Set (StrongDual 𝕜 E)}
    (hA : Equicontinuous ((↑) : A → E → 𝕜)) : ∃ U ∈ 𝓝 (0 : E), A ⊆ polar 𝕜 U := by
  have h := hA 0 {p : 𝕜 × 𝕜 | dist p.1 p.2 ≤ 1}
    (Filter.mem_of_superset (Metric.dist_mem_uniformity one_pos)
      fun p (hp : dist p.1 p.2 < 1) ↦ (le_of_lt hp : dist p.1 p.2 ≤ 1))
  refine ⟨_, h, fun φ hφ x hx ↦ ?_⟩
  have hx' := hx ⟨φ, hφ⟩
  change dist (φ 0) (φ x) ≤ 1 at hx'
  rwa [map_zero, dist_zero_left] at hx'

end StrongDual
