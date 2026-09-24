/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Final locally convex topologies

Let `f i : E i →ₗ[𝕜] F` be a family of linear maps from topological vector spaces `E i` into a
vector space `F` over `ℝ` or `ℂ`. The *final locally convex topology* on `F` is the finest
locally convex vector space topology on `F` for which all `f i` are continuous. This is the
final structure on the specified target `F`; algebraic colimit and spanning assumptions are
separate. Locally convex direct sums, quotients, and the (LF) topologies of distribution theory
are instances.

The topology is defined as the infimum of all locally convex vector space topologies on `F` that
make every `f i` continuous. This is the construction that Mathlib uses for the space of test
functions in `Mathlib/Analysis/Distribution/TestFunction.lean`, made general.

## Main definitions

* `locallyConvexFinalTopology f`: the final locally convex topology on `F` for the family `f`.

## Main statements

* `locallyConvexFinalTopology.isTopologicalAddGroup`, `.continuousSMul`, `.locallyConvexSpace`:
  it is a locally convex vector space topology.
* `locallyConvexFinalTopology.continuous_apply`: every `f i` is continuous.
* `locallyConvexFinalTopology.preimage_mem_nhds_zero`: the preimage under `f i` of a
  neighbourhood of zero is a neighbourhood of zero.
* `locallyConvexFinalTopology.le_iff`: a locally convex vector space topology `t` on `F` is
  coarser than the final one if and only if every `f i` is continuous for `t`.
* `locallyConvexFinalTopology.continuous_iff`: the **universal property**: a linear map from `F`
  to a locally convex space is continuous if and only if its composition with every `f i` is
  continuous.
* `locallyConvexFinalTopology.trans`: transitivity of final locally convex topologies.
* `locallyConvexFinalTopology.mem_nhds_zero`: a `ℝ`-convex, balanced, absorbent set whose preimage
  under every `f i` is a neighbourhood of zero is a neighbourhood of zero.
* `locallyConvexFinalTopology.barrelledSpace`: if every `E i` is barrelled then so is `F`.

## Implementation notes

The topology is a term, not an instance, so statements about it use `@`-notation or a local
instance, in the same way as `LocallyConvexSpace.sInf` in Mathlib.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], II §4.4 and III §4.1
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §6 and II §7.2

## Tags

inductive limit, final topology, locally convex space, barrelled space
-/

public section

open Set Filter TopologicalSpace

open scoped Topology Pointwise

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]

/-- The final locally convex topology on `F` for a family of linear maps `f i : E i →ₗ[𝕜] F`:
the finest locally convex vector space topology on `F` for which all `f i` are continuous. -/
@[expose, instance_reducible]
def locallyConvexFinalTopology (f : ∀ i, E i →ₗ[𝕜] F) : TopologicalSpace F :=
  sInf {t : TopologicalSpace F | @IsTopologicalAddGroup F t _ ∧ @ContinuousSMul 𝕜 F _ _ t ∧
    @LocallyConvexSpace ℝ F _ _ _ _ t ∧ ∀ i, @Continuous (E i) F _ t (f i)}

namespace locallyConvexFinalTopology

variable (f : ∀ i, E i →ₗ[𝕜] F)

/-- The final locally convex topology is a group topology. -/
theorem isTopologicalAddGroup : @IsTopologicalAddGroup F (locallyConvexFinalTopology f) _ :=
  isTopologicalAddGroup_sInf fun _ ht ↦ ht.1

/-- Scalar multiplication is continuous for the final locally convex topology. -/
theorem continuousSMul : @ContinuousSMul 𝕜 F _ _ (locallyConvexFinalTopology f) :=
  continuousSMul_sInf fun _ ht ↦ ht.2.1

/-- The final locally convex topology is locally convex. -/
theorem locallyConvexSpace : @LocallyConvexSpace ℝ F _ _ _ _ (locallyConvexFinalTopology f) :=
  .sInf fun _ ht ↦ ht.2.2.1

/-- Every map of the family is continuous for the final locally convex topology. -/
theorem continuous_apply (i : ι) :
    @Continuous (E i) F _ (locallyConvexFinalTopology f) (f i) :=
  continuous_sInf_rng.2 fun _ ht ↦ ht.2.2.2 i

/-- The preimage under a map of the family of a neighbourhood of zero for the final locally
convex topology is a neighbourhood of zero. -/
theorem preimage_mem_nhds_zero (i : ι) {W : Set F}
    (hW : W ∈ @nhds F (locallyConvexFinalTopology f) 0) : f i ⁻¹' W ∈ 𝓝 (0 : E i) := by
  have ht := @Continuous.tendsto _ F _ (locallyConvexFinalTopology f) _ (continuous_apply f i) 0
  rw [map_zero] at ht
  exact ht hW

/-- A locally convex vector space topology `t` on `F` is coarser than the final locally convex
topology if and only if every map of the family is continuous for `t`. -/
theorem le_iff {t : TopologicalSpace F} [@IsTopologicalAddGroup F t _]
    [@ContinuousSMul 𝕜 F _ _ t] [@LocallyConvexSpace ℝ F _ _ _ _ t] :
    locallyConvexFinalTopology f ≤ t ↔ ∀ i, @Continuous (E i) F _ t (f i) :=
  ⟨fun h i ↦ continuous_le_rng h (continuous_apply f i),
    fun h ↦ sInf_le ⟨inferInstance, inferInstance, inferInstance, h⟩⟩

variable [IsScalarTower ℝ 𝕜 F]

/-- The **universal property** of the final locally convex topology: a linear map from `F` to a
locally convex space `G` is continuous if and only if its composition with every map of the
family is continuous. -/
theorem continuous_iff {G : Type*} [AddCommGroup G] [Module 𝕜 G] [Module ℝ G]
    [IsScalarTower ℝ 𝕜 G] [tG : TopologicalSpace G] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 G] [LocallyConvexSpace ℝ G] (g : F →ₗ[𝕜] G) :
    @Continuous F G (locallyConvexFinalTopology f) _ g ↔ ∀ i, Continuous (g ∘ f i) := by
  have h1 : @IsTopologicalAddGroup F (induced g tG) _ := isTopologicalAddGroup_induced g
  have h2 : @ContinuousSMul 𝕜 F _ _ (induced g tG) := continuousSMul_induced g
  have h3 : @LocallyConvexSpace ℝ F _ _ _ _ (induced g tG) :=
    LocallyConvexSpace.induced (g.restrictScalars ℝ)
  rw [continuous_iff_le_induced, le_iff f]
  exact forall_congr' fun i ↦ continuous_induced_rng

section Transitivity

variable {κ : ι → Type*} {X : ∀ i, κ i → Type*} [∀ i k, AddCommGroup (X i k)]
  [∀ i k, Module 𝕜 (X i k)] [∀ i k, TopologicalSpace (X i k)]

/-- **Transitivity of final locally convex topologies.** If every `E i` carries the final
locally convex topology for a family `h i k : X i k →ₗ[𝕜] E i`, then the final locally convex
topology on `F` for the family `f i` is the final locally convex topology for the composed
family `f i ∘ h i k`. -/
theorem trans [∀ i, Module ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    (h : ∀ i k, X i k →ₗ[𝕜] E i)
    (hE : ∀ i, (inferInstance : TopologicalSpace (E i)) = locallyConvexFinalTopology (h i)) :
    locallyConvexFinalTopology f =
      locallyConvexFinalTopology fun p : Σ i, κ i ↦ f p.1 ∘ₗ h p.1 p.2 := by
  let g : ∀ p : Σ i, κ i, X p.1 p.2 →ₗ[𝕜] F := fun p ↦ f p.1 ∘ₗ h p.1 p.2
  have hh (i : ι) (k : κ i) : Continuous (h i k) := by
    have h1 := continuous_apply (h i) k
    rwa [← hE i] at h1
  refine le_antisymm ?_ ?_
  · -- Every `f i` is continuous for the final topology of the composed family.
    have h1 := isTopologicalAddGroup g
    have h2 := continuousSMul g
    have h3 := locallyConvexSpace g
    refine (le_iff f).mpr fun i ↦ ?_
    have key := (@continuous_iff 𝕜 _ (κ i) (X i) (E i) _ _ _ _ _ _ (h i) _ F _ _ _ _
      (locallyConvexFinalTopology g) h1 h2 h3 (f i)).mpr fun k ↦ continuous_apply g ⟨i, k⟩
    rwa [← hE i] at key
  · have h1 := isTopologicalAddGroup f
    have h2 := continuousSMul f
    have h3 := locallyConvexSpace f
    refine (le_iff g).mpr fun p ↦ ?_
    exact @Continuous.comp (X p.1 p.2) (E p.1) F _ _ (locallyConvexFinalTopology f)
      (⇑(h p.1 p.2)) (⇑(f p.1)) (continuous_apply f p.1) (hh p.1 p.2)

end Transitivity

section Nhds

variable [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]

/-- A `ℝ`-convex, balanced, absorbent subset of `F` whose preimage under every map of the family is
a neighbourhood of zero is a neighbourhood of zero for the final locally convex topology. -/
theorem mem_nhds_zero {U : Set F} (hc : Convex ℝ U) (hb : Balanced 𝕜 U) (ha : Absorbent 𝕜 U)
    (h : ∀ i, f i ⁻¹' U ∈ 𝓝 (0 : E i)) : U ∈ @nhds F (locallyConvexFinalTopology f) 0 := by
  -- The topology `t` defined by the gauge of `U` makes every `f i` continuous.
  let p : Seminorm 𝕜 F := gaugeSeminorm hb hc ha.restrictScalars_real
  let P : SeminormFamily 𝕜 F Unit := fun _ ↦ p
  let t : TopologicalSpace F := P.moduleFilterBasis.topology
  have hP : WithSeminorms P := ⟨rfl⟩
  have h1 : IsTopologicalAddGroup F := hP.isTopologicalAddGroup
  have h2 : ContinuousSMul 𝕜 F := hP.continuousSMul
  have h3 : LocallyConvexSpace ℝ F := hP.toLocallyConvexSpace
  have hpU (y : F) (hy : y ∈ U) : p y ≤ 1 := gauge_le_one_of_mem hy
  have hcont (i : ι) : Continuous (f i) := by
    refine continuous_of_continuousAt_zero (f i) ?_
    rw [ContinuousAt, map_zero, hP.hasBasis_zero_ball.tendsto_right_iff]
    rintro ⟨s, r⟩ hr
    have hr2 : (0 : ℝ) < r / 2 := half_pos hr
    have hne : ((r / 2 : ℝ) : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero]
      exact hr2.ne'
    filter_upwards [(set_smul_mem_nhds_zero_iff hne).mpr (h i)] with x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hle : s.sup P ≤ p := Finset.sup_le fun _ _ ↦ le_rfl
    rw [Seminorm.mem_ball_zero]
    calc (s.sup P) (f i (((r / 2 : ℝ) : 𝕜) • u)) ≤ p (f i (((r / 2 : ℝ) : 𝕜) • u)) := hle _
      _ = r / 2 * p (f i u) := by
        rw [map_smul, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hr2]
      _ ≤ r / 2 * 1 := by
        gcongr
        exact hpU _ hu
      _ < r := by linarith
  have hle : locallyConvexFinalTopology f ≤ t := (le_iff f).2 hcont
  -- `U` contains the open unit ball of its gauge.
  have hball : p.ball 0 1 ∈ 𝓝 (0 : F) := by
    have := hP.hasBasis_zero_ball.mem_of_mem (i := (({()} : Finset Unit), (1 : ℝ))) one_pos
    simpa [P] using this
  have hsub : p.ball 0 1 ⊆ U := fun x hx ↦
    setOfPred_gauge_lt_one_subset_self hc ha.zero_mem ha.restrictScalars_real
      (by simpa [Seminorm.mem_ball_zero, p] using hx)
  exact nhds_mono hle (mem_of_superset hball hsub)

/-- A seminorm on `F` is continuous for the final locally convex topology as soon as its
compositions with the maps of the family are continuous. -/
theorem continuous_seminorm (p : Seminorm 𝕜 F) (hp : ∀ i, Continuous fun x ↦ p (f i x)) :
    @Continuous F ℝ (locallyConvexFinalTopology f) _ p := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := isTopologicalAddGroup f
  have h2 : ContinuousSMul 𝕜 F := continuousSMul f
  refine Seminorm.continuous (r := 1) (mem_nhds_zero f (p.convex_ball 0 1)
    (p.balanced_ball_zero 1) (p.absorbent_ball_zero one_pos) fun i ↦ ?_)
  refine mem_of_superset (((hp i).isOpen_preimage _ (isOpen_Iio (a := (1 : ℝ)))).mem_nhds
    (by simp)) ?_
  intro x hx
  rw [mem_preimage, p.mem_ball_zero]
  exact hx

/-- The final locally convex topology for a family of maps from barrelled spaces is barrelled.
In particular locally convex direct sums and inductive limits of barrelled spaces are
barrelled. -/
theorem barrelledSpace [∀ i, Module ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    [∀ i, BarrelledSpace 𝕜 (E i)] :
    @BarrelledSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) := by
  let _ : TopologicalSpace F := locallyConvexFinalTopology f
  have h1 : IsTopologicalAddGroup F := isTopologicalAddGroup f
  have h2 : ContinuousSMul 𝕜 F := continuousSMul f
  have h3 : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  have h4 : ∀ i, ContinuousSMul ℝ (E i) := fun i ↦ IsScalarTower.continuousSMul 𝕜
  refine BarrelledSpace.of_forall_isBarrel_mem_nhds fun s hs ↦ ?_
  refine mem_nhds_zero f hs.convex hs.balanced hs.absorbent fun i ↦ ?_
  exact (hs.preimage (⟨f i, continuous_apply f i⟩ : E i →L[𝕜] F)).mem_nhds_zero

end Nhds

end locallyConvexFinalTopology
