/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.AlaogluBourbaki
public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.CompactHull
public import LocallyConvexSpaces.PairingTopology

/-!
# The Mackey topology and the Mackey–Arens theorem

Let `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` be a pairing. The *Mackey topology* `τ(E, F)` on `E` is the topology
of uniform convergence on the `σ(F, E)`-compact, convex, balanced subsets of `F`. A topology on
`E` is *compatible* with the pairing if its continuous linear functionals are exactly the
functionals `x ↦ B x y` with `y : F`. The **Mackey–Arens theorem** says that a locally convex
vector space topology on `E` is compatible with the pairing if and only if it is finer than the
weak topology `σ(E, F)` and coarser than the Mackey topology `τ(E, F)`.

## Main definitions

* `LinearMap.mackeyFamily B`: the `σ(F, E)`-compact, convex, balanced subsets of `F`.
* `LinearMap.mackeyTopology B`: the Mackey topology on `E`.
* `LinearMap.IsCompatibleTopology B`: the topology of `E` is compatible with the pairing.

## Main statements

* `LinearMap.isVonNBounded_of_mem_mackeyFamily`: the members of the Mackey family are weakly
  bounded.
* `LinearMap.exists_eq_of_continuous_mackeyTopology`: every linear functional that is continuous
  for the Mackey topology is of the form `x ↦ B x y`.
* `LinearMap.mackeyTopology_le_of_isCompatibleTopology`: a compatible locally convex topology is
  coarser than the Mackey topology.
* `LinearMap.isCompatibleTopology_mackeyTopology`: the Mackey topology is compatible with the
  pairing.
* `LinearMap.isCompatibleTopology_iff_mackeyTopology_le`: the **Mackey–Arens theorem**.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §3.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], IV §1.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.4

## Tags

Mackey topology, Mackey–Arens theorem, dual pair, compatible topology
-/

public section

open Set Filter Bornology Function

open scoped Topology Pointwise UniformConvergenceCLM

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The family of `σ(F, E)`-compact, convex, balanced subsets of `F`, which defines the Mackey
topology on `E`. -/
@[expose]
def mackeyFamily : Set (Set (WeakBilin B.flip)) :=
  {K | IsCompact K ∧ Convex ℝ K ∧ Balanced 𝕜 K}

omit [IsScalarTower ℝ 𝕜 F] in
/-- The Mackey family is not empty. -/
theorem mackeyFamily_nonempty : (B.mackeyFamily).Nonempty :=
  ⟨{0}, isCompact_singleton, convex_singleton 0, balanced_zero⟩

/-- The Mackey family is directed: two of its members lie in the convex hull of their union. -/
theorem directedOn_mackeyFamily : DirectedOn (· ⊆ ·) B.mackeyFamily := by
  have : ContinuousSMul ℝ (WeakBilin B.flip) := IsScalarTower.continuousSMul 𝕜
  rintro K₁ ⟨h₁c, h₁v, h₁b⟩ K₂ ⟨h₂c, h₂v, h₂b⟩
  exact ⟨convexHull ℝ (K₁ ∪ K₂),
    ⟨h₁c.convexHull_union h₂c h₁v h₂v, convex_convexHull ℝ _, (h₁b.union h₂b).convexHull_real⟩,
    subset_union_left.trans (subset_convexHull ℝ _),
    subset_union_right.trans (subset_convexHull ℝ _)⟩

/-- The Mackey family is stable under scalar multiples. -/
theorem smul_mem_mackeyFamily {K : Set (WeakBilin B.flip)} (hK : K ∈ B.mackeyFamily) (c : 𝕜) :
    c • K ∈ B.mackeyFamily := by
  obtain ⟨hc, hv, hb⟩ := hK
  refine ⟨hc.image (continuous_const_smul c), ?_, hb.smul c⟩
  have hlin : IsLinearMap ℝ (fun y : WeakBilin B.flip ↦ c • y) :=
    ⟨smul_add c, fun a y ↦ smul_comm c a y⟩
  rw [← image_smul]
  exact hv.is_linear_image hlin

omit [IsScalarTower ℝ 𝕜 F] in
/-- The members of the Mackey family are weakly bounded. -/
theorem isVonNBounded_of_mem_mackeyFamily {K : Set (WeakBilin B.flip)}
    (hK : K ∈ B.mackeyFamily) : IsVonNBounded 𝕜 K :=
  hK.1.isVonNBounded 𝕜

/-- The **Mackey topology** `τ(E, F)` on `E` for a pairing `B`: the topology of uniform
convergence on the `σ(F, E)`-compact, convex, balanced subsets of `F`. -/
@[expose, instance_reducible]
noncomputable def mackeyTopology : TopologicalSpace E :=
  B.polarTopology B.mackeyFamily

/-- The polars of the weakly compact, convex, balanced subsets of `F` form a basis of
neighbourhoods of zero for the Mackey topology. -/
theorem mackeyTopology_hasBasis_nhds_zero :
    (@nhds E B.mackeyTopology 0).HasBasis (· ∈ B.mackeyFamily) fun K ↦ B.flip.polar K :=
  polarTopology.hasBasis_nhds_zero B _ B.mackeyFamily_nonempty B.directedOn_mackeyFamily
    fun _ hK c _ ↦ B.smul_mem_mackeyFamily hK c

/-- **The hard half of the Mackey–Arens theorem**: every linear functional on `E` that is
continuous for the Mackey topology is of the form `x ↦ B x y` with `y : F`. -/
theorem exists_eq_of_continuous_mackeyTopology (f : E →ₗ[𝕜] 𝕜)
    (hf : @Continuous E 𝕜 B.mackeyTopology _ f) : ∃ y : F, ∀ x, f x = B x y := by
  -- `f` is bounded by one on the polar of a nonempty member `K` of the Mackey family.
  have hU : f ⁻¹' Metric.closedBall 0 1 ∈ @nhds E B.mackeyTopology 0 := by
    have ht := @Continuous.tendsto E 𝕜 B.mackeyTopology _ f hf 0
    rw [map_zero] at ht
    exact ht (Metric.closedBall_mem_nhds 0 one_pos)
  obtain ⟨K₀, hK₀, hK₀U⟩ := B.mackeyTopology_hasBasis_nhds_zero.mem_iff.mp hU
  obtain ⟨K, hK, hK₀K, h0K⟩ :=
    B.directedOn_mackeyFamily K₀ hK₀ {0} ⟨isCompact_singleton, convex_singleton 0, balanced_zero⟩
  have hKU : B.flip.polar K ⊆ f ⁻¹' Metric.closedBall 0 1 :=
    (B.flip.polar_antitone hK₀K).trans hK₀U
  -- The algebraic dual of `E` with the weak topology, and the image of `K` in it.
  let D : Module.Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 := LinearMap.id
  have hDinj : Injective D := fun _ _ h ↦ h
  have : T2Space (WeakBilin D) := (WeakBilin.isEmbedding hDinj).t2Space
  let j : WeakBilin B.flip →ₗ[𝕜] WeakBilin D := B.flip
  have hj : Continuous j :=
    WeakBilin.continuous_of_continuous_eval D fun x ↦ WeakBilin.eval_continuous B.flip x
  have hcl : IsClosed (j '' K) := (hK.1.image hj).isClosed
  have hconv : Convex ℝ (j '' K) :=
    Convex.is_linear_image (𝕜 := ℝ) (E := WeakBilin B.flip) (F := WeakBilin D) hK.2.1
      (j.restrictScalars ℝ).isLinear
  have hbal : Balanced 𝕜 (j '' K) :=
    Balanced.image (E := WeakBilin B.flip) (F := WeakBilin D) hK.2.2 j
  have hne : (j '' K).Nonempty := ⟨j 0, 0, h0K rfl, rfl⟩
  -- By the bipolar theorem `f` lies in the image of `K`.
  have hf_mem : (f : WeakBilin D) ∈ D.flip.polar (D.polar (j '' K)) := by
    intro x hx
    have hxK : x ∈ B.flip.polar K := fun y hy ↦ hx (j y) ⟨y, hy, rfl⟩
    have h := hKU hxK
    rw [mem_preimage, mem_closedBall_zero_iff] at h
    exact h
  obtain ⟨y, -, hy⟩ := D.flip_polar_polar_subset Subset.rfl hconv hbal hcl hne hf_mem
  exact ⟨y, fun x ↦ (LinearMap.congr_fun hy x).symm⟩

/-- A topology on `E` is **compatible** with the pairing `B` if its continuous linear functionals
are exactly the functionals `x ↦ B x y` with `y : F`. -/
@[expose]
def IsCompatibleTopology [TopologicalSpace E] : Prop :=
  ∀ f : E →ₗ[𝕜] 𝕜, Continuous f ↔ ∃ y : F, ∀ x, f x = B x y

/-- Every point of `F` lies in a member of the Mackey family: the balanced hull of a point is
weakly compact, convex and balanced. -/
theorem sUnion_mackeyFamily : ⋃₀ B.mackeyFamily = univ := by
  have : ContinuousSMul ℝ (WeakBilin B.flip) := IsScalarTower.continuousSMul 𝕜
  refine eq_univ_of_forall fun y ↦ ?_
  let φ : 𝕜 →ₗ[𝕜] WeakBilin B.flip := LinearMap.toSpanSingleton 𝕜 (WeakBilin B.flip) y
  have hφ : Continuous φ := continuous_id.smul continuous_const
  refine ⟨φ '' Metric.closedBall (0 : 𝕜) 1, ⟨?_, ?_, ?_⟩, 1, by simp, by simp [φ]⟩
  · exact (ProperSpace.isCompact_closedBall (0 : 𝕜) 1).image hφ
  · exact Convex.is_linear_image (𝕜 := ℝ) (E := 𝕜) (F := WeakBilin B.flip)
      (convex_closedBall (0 : 𝕜) 1) (φ.restrictScalars ℝ).isLinear
  · exact Balanced.image (E := 𝕜) (F := WeakBilin B.flip) balanced_closedBall_zero φ

/-- The functionals `x ↦ B x y` are continuous for the Mackey topology. -/
theorem continuous_apply_mackeyTopology (y : F) :
    @Continuous E 𝕜 B.mackeyTopology _ fun x ↦ B x y := by
  have := UniformConvergenceCLM.continuousEvalConst (RingHom.id 𝕜) 𝕜 B.mackeyFamily
    B.sUnion_mackeyFamily
  have hc1 : @Continuous E _ B.mackeyTopology _ (B.toUniformConvergenceCLM B.mackeyFamily) :=
    continuous_induced_dom
  have hc2 : Continuous fun φ : (WeakBilin B.flip →Lᵤ[𝕜, B.mackeyFamily] 𝕜) ↦
      φ (y : WeakBilin B.flip) := continuous_eval_const (y : WeakBilin B.flip)
  exact @Continuous.comp E _ 𝕜 B.mackeyTopology _ _ _ _ hc2 hc1

/-- The Mackey topology is compatible with the pairing. -/
theorem isCompatibleTopology_mackeyTopology :
    @IsCompatibleTopology 𝕜 E F _ _ _ _ _ B B.mackeyTopology :=
  fun f ↦ ⟨B.exists_eq_of_continuous_mackeyTopology f, fun ⟨y, hy⟩ ↦ by
    have hfy : (f : E → 𝕜) = fun x ↦ B x y := funext hy
    rw [hfy]
    exact B.continuous_apply_mackeyTopology y⟩

section Compatible

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

omit [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] in
/-- For a compatible topology the functionals `x ↦ B x y` are continuous. -/
theorem IsCompatibleTopology.continuous_apply (h : B.IsCompatibleTopology) (y : F) :
    Continuous fun x ↦ B x y :=
  (h (B.flip y)).mpr ⟨y, fun _ ↦ rfl⟩

/-- **The easy half of the Mackey–Arens theorem**: a locally convex topology that is compatible
with the pairing is coarser than the Mackey topology. -/
theorem mackeyTopology_le_of_isCompatibleTopology (h : B.IsCompatibleTopology) :
    B.mackeyTopology ≤ (inferInstance : TopologicalSpace E) := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have hτ : @IsTopologicalAddGroup E B.mackeyTopology _ :=
    polarTopology.isTopologicalAddGroup B _
  -- It suffices that every neighbourhood of zero is a Mackey neighbourhood of zero.
  refine continuous_id_iff_le.mp ?_
  refine @continuous_of_continuousAt_zero E B.mackeyTopology _ hτ E (E →+ E) _ _ _ _ _
    (AddMonoidHom.id E) ?_
  intro U hU
  rw [AddMonoidHom.id_apply] at hU
  change U ∈ @nhds E B.mackeyTopology 0
  -- A closed, convex, balanced neighbourhood `U'` of zero inside `U`.
  obtain ⟨C, ⟨hC, hCcl⟩, hCU⟩ := (closed_nhds_basis (0 : E)).mem_iff.mp hU
  obtain ⟨V, ⟨hV, hVc, hVb⟩, hVC⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hC
  have hU'U : closure V ⊆ U := (closure_minimal hVC hCcl).trans hCU
  have hU' : closure V ∈ 𝓝 (0 : E) := mem_of_superset hV subset_closure
  -- The map `y ↦ B · y` from `F` onto the dual of `E`, both with their weak topologies.
  let g : WeakBilin B.flip → WeakDual 𝕜 E := fun y ↦
    StrongDual.toWeakDual ⟨B.flip y, h.continuous_apply B y⟩
  have hg : Topology.IsInducing g := ⟨by
    change (TopologicalSpace.induced (fun (y : WeakBilin B.flip) (x : E) ↦ B.flip y x)
      Pi.topologicalSpace) = TopologicalSpace.induced g (TopologicalSpace.induced
        (fun (φ : WeakDual 𝕜 E) (x : E) ↦ φ x) Pi.topologicalSpace)
    rw [induced_compose]
    rfl⟩
  have hgsurj : Surjective g := fun φ ↦ by
    obtain ⟨y, hy⟩ := (h (WeakDual.toStrongDual φ).toLinearMap).mp
      (WeakDual.toStrongDual φ).continuous
    exact ⟨y, DFunLike.ext _ _ fun x ↦ (hy x).symm⟩
  -- The polar of `closure V` in `F` is weakly compact, by the Alaoglu–Bourbaki theorem.
  let K : Set (WeakBilin B.flip) := B.polar (closure V)
  have hKpre : K = g ⁻¹' WeakDual.polar 𝕜 (closure V) := rfl
  have hK : K ∈ B.mackeyFamily := by
    refine ⟨?_, B.convex_polar _, B.balanced_polar _⟩
    rw [hKpre]
    exact hg.isCompact_preimage (by rw [hgsurj.range_eq]; exact isClosed_univ)
      (WeakDual.isCompact_polar_of_mem_nhds hU')
  -- By the bipolar theorem the polar of `K` is `closure V`.
  refine mem_of_superset (polarTopology.polar_mem_nhds_zero B _ B.mackeyFamily_nonempty
    B.directedOn_mackeyFamily hK) (Subset.trans ?_ hU'U)
  intro x hx
  rw [← StrongDual.bipolar_eq_self (𝕜 := 𝕜) hVc.closure hVb.closure isClosed_closure
    ⟨0, subset_closure (mem_of_mem_nhds hV)⟩]
  intro φ hφ
  obtain ⟨y, hy⟩ := (h φ.toLinearMap).mp φ.continuous
  have hyK : y ∈ K := fun z hz ↦ by
    have h1 : ‖φ z‖ ≤ 1 := hφ z hz
    change ‖B z y‖ ≤ 1
    rw [← hy z]
    exact h1
  have h2 := hx y hyK
  change ‖φ x‖ ≤ 1
  rw [show φ x = B x y from hy x]
  exact h2

/-- The **Mackey–Arens theorem**: a locally convex vector space topology on `E` is compatible
with a pairing `B` of `E` and `F` if and only if the functionals `x ↦ B x y` are continuous,
which says that the topology is finer than the weak topology `σ(E, F)`, and the topology is
coarser than the Mackey topology `τ(E, F)`. -/
theorem isCompatibleTopology_iff_mackeyTopology_le :
    B.IsCompatibleTopology ↔ (∀ y : F, Continuous fun x ↦ B x y) ∧
      B.mackeyTopology ≤ (inferInstance : TopologicalSpace E) := by
  refine ⟨fun h ↦ ⟨h.continuous_apply B, B.mackeyTopology_le_of_isCompatibleTopology h⟩,
    fun ⟨h1, h2⟩ f ↦ ⟨fun hf ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩⟩
  · exact B.exists_eq_of_continuous_mackeyTopology f (continuous_le_dom h2 hf)
  · have hfy : (f : E → 𝕜) = fun x ↦ B x y := funext hy
    rw [hfy]
    exact h1 y

/-- If the pairing evaluations are continuous, compatibility is equivalent to the topology
being coarser than the Mackey topology. -/
theorem isCompatibleTopology_iff_mackeyTopology_le_of_continuous
    (h : ∀ y : F, Continuous fun x ↦ B x y) :
    B.IsCompatibleTopology ↔ B.mackeyTopology ≤ (inferInstance : TopologicalSpace E) := by
  rw [B.isCompatibleTopology_iff_mackeyTopology_le]
  exact and_iff_right h

end Compatible

end LinearMap
