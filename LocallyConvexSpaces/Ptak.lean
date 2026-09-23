/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Barrel
public import LocallyConvexSpaces.Basic
public import LocallyConvexSpaces.KreinSmulian
public import LocallyConvexSpaces.Transpose

/-!
# Pták spaces and Pták's closed graph and open mapping theorems

A topological vector space `E` is a *Pták space* (or *`B`-complete*, or *fully complete*) if
every almost weak-\* closed subspace of its dual is weak-\* closed, and an *infra-Pták space*
(or *`B_r`-complete*) if every weak-\* dense, almost weak-\* closed subspace of its dual is the
whole dual. Here a set of functionals is almost weak-\* closed if it meets the polar of every
neighbourhood of zero in a weak-\* closed set (`StrongDual.IsAlmostWeakStarClosed`).

By the Krein–Šmulian theorem every Fréchet space is a Pták space. Pták's closed graph theorem
says that a linear map with closed graph from a barrelled locally convex space to an infra-Pták
locally convex space is continuous. It contains the closed graph theorem for a barrelled domain
and a Fréchet codomain (`LinearMap.continuous_of_isClosed_graph_of_barrelledSpace` in
`LocallyConvexSpaces.ClosedGraph`), which was proved there by successive approximation.
Pták's open mapping theorem says that a continuous linear map from a Pták locally convex space
onto a barrelled Hausdorff locally convex space is open; it contains the open mapping theorem of
`LocallyConvexSpaces.OpenMapping` for a Fréchet domain.

## Main definitions

* `PtakSpace 𝕜 E`, `InfraPtakSpace 𝕜 E`: the two classes of spaces.
* `LinearMap.transposeDomain g`: for a linear map `g : E →ₗ[𝕜] F`, the subspace of the dual of
  `F` of all `φ` such that `φ ∘ g` is continuous; the domain of the transpose of `g`.

## Main statements

* `PtakSpace.toInfraPtakSpace`: a Pták space is an infra-Pták space.
* `PtakSpace.of_completeSpace_firstCountableTopology`: a complete, first-countable, locally convex
  space is a Pták space.
* `LinearMap.isAlmostWeakStarClosed_transposeDomain`: if `E` is barrelled then the domain of the
  transpose of a linear map `g : E →ₗ[𝕜] F` is almost weak-\* closed.
* `LinearMap.eq_zero_of_forall_transposeDomain_apply_eq_zero`: if `g` has closed graph then the
  domain of its transpose separates the points of the codomain.
* `LinearMap.dense_transposeDomain`: if `g` has closed graph then the domain of its transpose is
  weak-\* dense.
* `LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace`: **Pták's closed graph theorem**.
* `LinearEquiv.continuous_symm_of_infraPtakSpace`: a continuous linear bijection from an
  infra-Pták space onto a Hausdorff barrelled space has a continuous inverse.
* `ContinuousLinearMap.isAlmostWeakStarClosed_range_transpose`: if `f` maps onto a barrelled
  space then the range of its transpose is almost weak-\* closed.
* `ContinuousLinearMap.mem_range_transpose_of_forall_ker`: if the range of the transpose is
  weak-\* closed then it is the annihilator of the kernel of `f`.
* `ContinuousLinearMap.isOpenMap_of_ptakSpace`: **Pták's open mapping theorem**.

## Implementation notes

The open mapping theorem is proved directly, without quotient spaces. The range `Q` of the
transpose of `f` meets the polar of a neighbourhood `U` of zero in the image, under the
transpose, of the polar of the closure of `f '' U`; that polar is weak-\* compact by the
Alaoglu–Bourbaki theorem, because the closure of `f '' U` is a neighbourhood of zero when the
codomain is barrelled. Hence `Q` is almost weak-\* closed, so it is weak-\* closed when the
domain is a Pták space, and then it is the annihilator of the kernel of `f`. The bipolar
theorem in `E` then shows that the closure of `f '' W` lies in `f '' (W + W)`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §8
* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §34
* V. Pták, *Completeness and the open mapping theorem*, Bull. Soc. Math. France 86 (1958)

## Tags

Pták space, B-complete, infra-Pták space, closed graph theorem, barrelled space
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise

section Defs

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A topological vector space is a **Pták space** (is `B`-complete) if every almost weak-\*
closed subspace of its dual is weak-\* closed. -/
class PtakSpace : Prop where
  /-- In the dual of a Pták space every almost weak-\* closed subspace is weak-\* closed. -/
  isClosed_of_isAlmostWeakStarClosed : ∀ Q : Submodule 𝕜 (StrongDual 𝕜 E),
    StrongDual.IsAlmostWeakStarClosed (Q : Set (StrongDual 𝕜 E)) →
      IsClosed (WeakDual.toStrongDual ⁻¹' (Q : Set (StrongDual 𝕜 E)))

/-- A topological vector space is an **infra-Pták space** (is `B_r`-complete) if every weak-\*
dense, almost weak-\* closed subspace of its dual is the whole dual. -/
class InfraPtakSpace : Prop where
  /-- In the dual of an infra-Pták space every weak-\* dense, almost weak-\* closed subspace is
  the whole dual. -/
  eq_top_of_dense : ∀ Q : Submodule 𝕜 (StrongDual 𝕜 E),
    StrongDual.IsAlmostWeakStarClosed (Q : Set (StrongDual 𝕜 E)) →
      Dense (WeakDual.toStrongDual ⁻¹' (Q : Set (StrongDual 𝕜 E))) → Q = ⊤

variable {𝕜 E}

/-- A Pták space is an infra-Pták space. -/
instance (priority := 100) PtakSpace.toInfraPtakSpace [PtakSpace 𝕜 E] : InfraPtakSpace 𝕜 E where
  eq_top_of_dense Q hQ hd := by
    have h := (PtakSpace.isClosed_of_isAlmostWeakStarClosed Q hQ).closure_eq
    rw [hd.closure_eq] at h
    refine (Submodule.eq_top_iff'.mpr fun φ ↦ ?_)
    have hφ : StrongDual.toWeakDual φ ∈ (univ : Set (WeakDual 𝕜 E)) := mem_univ _
    rw [h] at hφ
    exact hφ

end Defs

section Frechet

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [CompleteSpace E] [FirstCountableTopology E]

/-- A complete, first-countable, locally convex space is a Pták space. This is the
Krein–Šmulian theorem applied to subspaces. -/
instance (priority := 100) PtakSpace.of_completeSpace_firstCountableTopology : PtakSpace 𝕜 E where
  isClosed_of_isAlmostWeakStarClosed Q hQ :=
    StrongDual.isClosed_of_isAlmostWeakStarClosed (Q.restrictScalars ℝ).convex hQ

end Frechet

section ClosedGraph

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The domain of the transpose of a linear map `g : E →ₗ[𝕜] F`: the subspace of the dual of `F`
consisting of the functionals `φ` for which `φ ∘ g` is continuous. -/
@[expose]
def LinearMap.transposeDomain (g : E →ₗ[𝕜] F) : Submodule 𝕜 (StrongDual 𝕜 F) where
  carrier := {φ | Continuous fun x ↦ φ (g x)}
  add_mem' hφ hψ := hφ.add hψ
  zero_mem' := continuous_const
  smul_mem' c _ hφ := hφ.const_smul c

/-- Membership of the domain of the transpose of a linear map. -/
@[simp]
theorem LinearMap.mem_transposeDomain {g : E →ₗ[𝕜] F} {φ : StrongDual 𝕜 F} :
    φ ∈ g.transposeDomain ↔ Continuous fun x ↦ φ (g x) :=
  Iff.rfl

end ClosedGraph

section ClosedGraphTheorem

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F]

omit [IsTopologicalAddGroup F] in
/-- If `E` is barrelled then the domain of the transpose of any linear map `g : E →ₗ[𝕜] F` into
a locally convex space is almost weak-\* closed. -/
theorem LinearMap.isAlmostWeakStarClosed_transposeDomain [BarrelledSpace 𝕜 E] (g : E →ₗ[𝕜] F) :
    StrongDual.IsAlmostWeakStarClosed (g.transposeDomain : Set (StrongDual 𝕜 F)) := by
  intro V hV
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWV⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV
  -- By barrelledness the closure `U` of `g ⁻¹' W` is a neighbourhood of zero.
  have hU : closure (g ⁻¹' W) ∈ 𝓝 (0 : E) :=
    g.closure_preimage_mem_nhds_of_barrelledSpace hWc hWb hW
  -- `A` is the set of functionals `φ` with `φ ∘ g` bounded by one on `U`.
  let A : Set (StrongDual 𝕜 F) := {φ | ∀ x ∈ closure (g ⁻¹' W), ‖φ (g x)‖ ≤ 1}
  have hAQ : A ⊆ g.transposeDomain := fun φ hφ ↦ by
    have hb : ∃ U ∈ 𝓝 (0 : E), IsVonNBounded 𝕜 ((φ.toLinearMap ∘ₗ g) '' U) :=
      ⟨_, hU, (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 1).subset <| by
        rintro _ ⟨x, hx, rfl⟩
        exact mem_closedBall_zero_iff.mpr (hφ x hx)⟩
    exact ((φ.toLinearMap ∘ₗ g).clmOfExistsBoundedImage hb).continuous
  have hQA : (g.transposeDomain : Set (StrongDual 𝕜 F)) ∩ StrongDual.polar 𝕜 V ⊆ A := by
    rintro φ ⟨hφQ, hφV⟩
    have hcl : IsClosed {x : E | ‖φ (g x)‖ ≤ 1} :=
      isClosed_le (LinearMap.mem_transposeDomain.mp hφQ).norm continuous_const
    exact closure_minimal (fun x hx ↦ hφV (g x) (hWV hx)) hcl
  have hA : IsClosed (WeakDual.toStrongDual ⁻¹' A) := by
    have h : WeakDual.toStrongDual ⁻¹' A =
        ⋂ x ∈ closure (g ⁻¹' W), {χ : WeakDual 𝕜 F | ‖χ (g x)‖ ≤ 1} := by
      ext χ
      simp only [mem_preimage, mem_iInter]
      rfl
    rw [h]
    exact isClosed_biInter fun x _ ↦
      isClosed_le (WeakDual.eval_continuous (g x)).norm continuous_const
  have key : WeakDual.toStrongDual ⁻¹'
      ((g.transposeDomain : Set (StrongDual 𝕜 F)) ∩ StrongDual.polar 𝕜 V) =
      WeakDual.toStrongDual ⁻¹' A ∩ WeakDual.toStrongDual ⁻¹' StrongDual.polar 𝕜 V := by
    ext χ
    exact ⟨fun h ↦ ⟨hQA h, h.2⟩, fun h ↦ ⟨hAQ h.1, h.2⟩⟩
  rw [key]
  exact hA.inter (WeakDual.isClosed_polar 𝕜 V)

variable [LocallyConvexSpace ℝ E]

/-- If a linear map `g` between locally convex spaces has closed graph then the domain of its
transpose separates the points of the codomain. -/
theorem LinearMap.eq_zero_of_forall_transposeDomain_apply_eq_zero (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) {y : F}
    (hy : ∀ φ ∈ g.transposeDomain, φ y = 0) : y = 0 := by
  by_contra hy_ne
  -- The point `(0, y)` is not in the graph; separate it from the graph.
  have hnot : ((0 : E), y) ∉ (g.graph : Set (E × F)) := by
    intro h
    have h' : y = g 0 := h
    exact hy_ne (by rw [h', map_zero])
  obtain ⟨Φ, hΦ, hΦy⟩ := StrongDual.exists_mem_polar_one_lt_norm (𝕜 := 𝕜)
    (g.graph.restrictScalars ℝ).convex g.graph.balanced hg ⟨0, g.graph.zero_mem⟩ hnot
  have hΦ0 (p : E × F) (hp : p ∈ g.graph) : Φ p = 0 :=
    LinearMap.eq_zero_of_forall_norm_le_one (Q := g.graph) (φ := Φ.toLinearMap) hΦ hp
  -- The second component of `Φ` lies in the domain of the transpose, so it vanishes at `y`.
  let β : StrongDual 𝕜 F := Φ.comp (ContinuousLinearMap.inr 𝕜 E F)
  let α : StrongDual 𝕜 E := Φ.comp (ContinuousLinearMap.inl 𝕜 E F)
  have hβ : β ∈ g.transposeDomain := by
    have h : (fun x ↦ β (g x)) = fun x ↦ -α x := by
      funext x
      have h1 : Φ (x, g x) = 0 := hΦ0 (x, g x) rfl
      have h2 : Φ (x, g x) = α x + β (g x) := by
        change Φ (x, g x) = Φ (x, 0) + Φ (0, g x)
        rw [← map_add]
        simp
      rw [h2] at h1
      exact eq_neg_of_add_eq_zero_right h1
    rw [LinearMap.mem_transposeDomain, h]
    exact α.continuous.neg
  have hβy : Φ ((0 : E), y) = 0 := hy β hβ
  rw [hβy, norm_zero] at hΦy
  linarith

/-- If a linear map `g` between locally convex spaces has closed graph then the domain of its
transpose is weak-\* dense in the dual of the codomain. -/
theorem LinearMap.dense_transposeDomain (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) :
    Dense (WeakDual.toStrongDual ⁻¹' (g.transposeDomain : Set (StrongDual 𝕜 F))) := by
  -- Work in `WeakBilin` for the pairing of the dual of `F` with `F`.
  have : ContinuousSMul ℝ (WeakBilin (topDualPairing 𝕜 F)) := IsScalarTower.continuousSMul 𝕜
  let Q : Set (WeakBilin (topDualPairing 𝕜 F)) := (g.transposeDomain : Set (StrongDual 𝕜 F))
  have hQc : Convex ℝ Q := (g.transposeDomain.restrictScalars ℝ).convex
  have hQb : Balanced 𝕜 Q := g.transposeDomain.balanced
  change Dense Q
  intro ψ
  by_contra hψ
  -- Separate `ψ` from the weak-* closure of the domain by a vector `y` of `F`.
  have hTc : Convex ℝ (closure Q) :=
    Convex.closure (𝕜 := ℝ) (E := WeakBilin (topDualPairing 𝕜 F)) hQc
  have hTb : Balanced 𝕜 (closure Q) :=
    Balanced.closure (𝕜 := 𝕜) (E := WeakBilin (topDualPairing 𝕜 F)) hQb
  have hQsub : Q ⊆ closure Q := subset_closure
  have hTne : (closure Q).Nonempty := ⟨0, hQsub g.transposeDomain.zero_mem⟩
  obtain ⟨y, hy, hψy⟩ :=
    (topDualPairing 𝕜 F).exists_mem_polar_one_lt_norm hTc hTb isClosed_closure hTne hψ
  -- Then `y` is annihilated by the domain of the transpose, hence `y = 0`.
  have hy0 : y = 0 := g.eq_zero_of_forall_transposeDomain_apply_eq_zero hg fun φ hφ ↦
    LinearMap.eq_zero_of_forall_norm_le_one (Q := g.transposeDomain)
      (φ := ((topDualPairing 𝕜 F).flip y)) (fun χ hχ ↦ hy χ (hQsub hχ)) hφ
  rw [hy0, map_zero, norm_zero] at hψy
  linarith

variable [BarrelledSpace 𝕜 E] [InfraPtakSpace 𝕜 F]

/-- **Pták's closed graph theorem**: a linear map with closed graph from a barrelled locally
convex space to an infra-Pták (`B_r`-complete) locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := by
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  -- The transpose is everywhere defined: `φ ∘ g` is continuous for every `φ`.
  have htop : g.transposeDomain = ⊤ :=
    InfraPtakSpace.eq_top_of_dense _ g.isAlmostWeakStarClosed_transposeDomain
      (g.dense_transposeDomain hg)
  have hcont (φ : StrongDual 𝕜 F) : Continuous fun x ↦ φ (g x) :=
    LinearMap.mem_transposeDomain.mp (htop ▸ Submodule.mem_top)
  -- It suffices to show that preimages of closed convex balanced neighbourhoods are
  -- neighbourhoods of zero.
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero]
  intro V hV
  obtain ⟨V₁, hV₁, hV₁cl, hV₁V⟩ := exists_mem_nhds_isClosed_subset hV
  obtain ⟨W₀, ⟨hW₀, hW₀c, hW₀b⟩, hW₀V⟩ :=
    (nhds_zero_hasBasis_convex_balanced 𝕜 F).mem_iff.mp hV₁
  -- `W` is a closed convex balanced neighbourhood of zero inside `V`.
  have hWV : closure W₀ ⊆ V := (closure_minimal hW₀V hV₁cl).trans hV₁V
  have hWnhds : closure W₀ ∈ 𝓝 (0 : F) := mem_of_superset hW₀ subset_closure
  -- Its preimage is closed, because it is an intersection of closed sets `‖φ (g x)‖ ≤ 1`.
  have hbip : (topDualPairing 𝕜 F).polar (StrongDual.polar 𝕜 (closure W₀)) = closure W₀ :=
    StrongDual.bipolar_eq_self hW₀c.closure hW₀b.closure isClosed_closure
      ⟨0, mem_of_mem_nhds hWnhds⟩
  have hpre : g ⁻¹' closure W₀ =
      ⋂ φ ∈ StrongDual.polar 𝕜 (closure W₀), {x : E | ‖φ (g x)‖ ≤ 1} := by
    ext x
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro hx φ hφ
      exact hφ (g x) hx
    · intro h
      have h' : g x ∈ (topDualPairing 𝕜 F).polar (StrongDual.polar 𝕜 (closure W₀)) :=
        fun φ hφ ↦ h φ hφ
      rwa [hbip] at h'
  have hclosed : IsClosed (g ⁻¹' closure W₀) := by
    rw [hpre]
    exact isClosed_biInter fun φ _ ↦ isClosed_le (hcont φ).norm continuous_const
  -- By barrelledness the closure of the preimage is a neighbourhood of zero.
  have hnear := g.closure_preimage_mem_nhds_of_barrelledSpace hW₀c.closure hW₀b.closure hWnhds
  rw [hclosed.closure_eq] at hnear
  exact mem_of_superset hnear (preimage_mono hWV)

end ClosedGraphTheorem

section Inverse

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
  [InfraPtakSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F] [BarrelledSpace 𝕜 F] [T2Space F]

/-- A continuous linear bijection from an infra-Pták locally convex space onto a barrelled
Hausdorff locally convex space has a continuous inverse. -/
theorem LinearEquiv.continuous_symm_of_infraPtakSpace (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    Continuous e.symm := by
  refine e.symm.toLinearMap.continuous_of_isClosed_graph_of_infraPtakSpace ?_
  -- The graph of `e.symm` is the transposed graph of `e`, which is closed.
  have hgraph : (e.symm.toLinearMap.graph : Set (F × E)) = {p : F × E | e p.2 = p.1} := by
    ext p
    change p.2 = e.symm p.1 ↔ e p.2 = p.1
    rw [LinearEquiv.eq_symm_apply]
  rw [hgraph]
  exact isClosed_eq (h.comp continuous_snd) continuous_fst

end Inverse

section OpenMappingTheorem

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

omit [IsTopologicalAddGroup E] in
/-- If `f` is a continuous linear map from a locally convex space onto a barrelled space, then
the range of its transpose is almost weak-\* closed. -/
theorem ContinuousLinearMap.isAlmostWeakStarClosed_range_transpose [LocallyConvexSpace ℝ E]
    [BarrelledSpace 𝕜 F] (f : E →L[𝕜] F) (hf : Function.Surjective f) :
    StrongDual.IsAlmostWeakStarClosed
      (LinearMap.range f.transpose.toLinearMap : Set (StrongDual 𝕜 E)) := by
  intro U hU
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hU
  -- By barrelledness the closure `V` of `f '' W` is a neighbourhood of zero.
  have hV : closure (f '' W) ∈ 𝓝 (0 : F) :=
    LinearMap.closure_image_mem_nhds_of_barrelledSpace (f := f.toLinearMap) hf hWc hWb hW
  -- The transpose, as a weak-* continuous map, and the image of the weak-* compact polar of `V`.
  let T : WeakDual 𝕜 F → WeakDual 𝕜 E := fun ξ ↦
    StrongDual.toWeakDual (f.transpose (WeakDual.toStrongDual ξ))
  have hT : Continuous T := f.continuous_transpose_weakDual
  have hK : IsClosed (T '' WeakDual.polar 𝕜 (closure (f '' W))) :=
    ((WeakDual.isCompact_polar_of_mem_nhds hV).image hT).isClosed
  have key : WeakDual.toStrongDual ⁻¹'
      ((LinearMap.range f.transpose.toLinearMap : Set (StrongDual 𝕜 E)) ∩
        StrongDual.polar 𝕜 U) =
      T '' WeakDual.polar 𝕜 (closure (f '' W)) ∩
        WeakDual.toStrongDual ⁻¹' StrongDual.polar 𝕜 U := by
    ext χ
    constructor
    · rintro ⟨⟨ψ, hψ⟩, hχU⟩
      refine ⟨⟨StrongDual.toWeakDual ψ, ?_, WeakDual.toStrongDual.injective hψ⟩, hχU⟩
      have hcl : IsClosed {y : F | ‖ψ y‖ ≤ 1} := isClosed_le ψ.continuous.norm continuous_const
      refine closure_minimal ?_ hcl
      rintro _ ⟨w, hw, rfl⟩
      have h1 := hχU w (hWU hw)
      rw [← hψ] at h1
      exact h1
    · rintro ⟨⟨ξ, -, rfl⟩, hχU⟩
      exact ⟨⟨WeakDual.toStrongDual ξ, rfl⟩, hχU⟩
  rw [key]
  exact hK.inter (WeakDual.isClosed_polar 𝕜 U)

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/-- If the dual of `F` separates points and the range of the transpose of `f : E →L[𝕜] F` is
weak-\* closed, then it consists of all functionals that vanish on the kernel of `f`. -/
theorem ContinuousLinearMap.mem_range_transpose_of_forall_ker_of_separatingDual
    [SeparatingDual 𝕜 F] (f : E →L[𝕜] F)
    (hQ : IsClosed (WeakDual.toStrongDual ⁻¹'
      (LinearMap.range f.transpose.toLinearMap : Set (StrongDual 𝕜 E))))
    {φ : StrongDual 𝕜 E} (hφ : ∀ x, f x = 0 → φ x = 0) :
    φ ∈ LinearMap.range f.transpose.toLinearMap := by
  by_contra hφQ
  let R : Submodule 𝕜 (StrongDual 𝕜 E) := LinearMap.range f.transpose.toLinearMap
  let Q : Set (WeakBilin (topDualPairing 𝕜 E)) := (R : Set (StrongDual 𝕜 E))
  have hQc : Convex ℝ Q := (R.restrictScalars ℝ).convex
  have hQb : Balanced 𝕜 Q := R.balanced
  have hQcl : IsClosed Q := hQ
  obtain ⟨x, hx, hφx⟩ := (topDualPairing 𝕜 E).exists_mem_polar_one_lt_norm hQc hQb hQcl
    ⟨0, R.zero_mem⟩ hφQ
  -- Every functional of the form `ψ ∘ f` vanishes at `x`, so `f x = 0`.
  have hx0 (χ : StrongDual 𝕜 E) (hχ : χ ∈ R) : χ x = 0 :=
    LinearMap.eq_zero_of_forall_norm_le_one (Q := R)
      (φ := ((topDualPairing 𝕜 E).flip x)) (fun χ hχ ↦ hx χ hχ) hχ
  have hfx : f x = 0 :=
    f.mem_ker_iff_forall_transpose_of_separatingDual.mpr fun ψ ↦ hx0 (f.transpose ψ) ⟨ψ, rfl⟩
  have h1 : ‖φ x‖ = 0 := by rw [hφ x hfx, norm_zero]
  have h2 : (1 : ℝ) < ‖φ x‖ := hφx
  linarith

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
/-- If `F` is a Hausdorff locally convex space and the range of the transpose of `f : E →L[𝕜] F`
is weak-\* closed, then it consists of all functionals that vanish on the kernel of `f`. -/
theorem ContinuousLinearMap.mem_range_transpose_of_forall_ker [LocallyConvexSpace ℝ F]
    [T1Space F] (f : E →L[𝕜] F)
    (hQ : IsClosed (WeakDual.toStrongDual ⁻¹'
      (LinearMap.range f.transpose.toLinearMap : Set (StrongDual 𝕜 E))))
    {φ : StrongDual 𝕜 E} (hφ : ∀ x, f x = 0 → φ x = 0) :
    φ ∈ LinearMap.range f.transpose.toLinearMap := by
  have : SeparatingDual 𝕜 F := SeparatingDual.of_locallyConvexSpace_real 𝕜 F
  exact f.mem_range_transpose_of_forall_ker_of_separatingDual hQ hφ

/-- **Pták's open mapping theorem**: a continuous linear map from a Pták (`B`-complete) locally
convex space onto a barrelled Hausdorff locally convex space is an open map. -/
theorem ContinuousLinearMap.isOpenMap_of_ptakSpace [LocallyConvexSpace ℝ E] [PtakSpace 𝕜 E]
    [LocallyConvexSpace ℝ F] [BarrelledSpace 𝕜 F] [T1Space F] (f : E →L[𝕜] F)
    (hf : Function.Surjective f) : IsOpenMap f := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  -- The range of the transpose is weak-* closed, hence it is the annihilator of the kernel.
  have hQ : IsClosed (WeakDual.toStrongDual ⁻¹'
      (LinearMap.range f.transpose.toLinearMap : Set (StrongDual 𝕜 E))) :=
    PtakSpace.isClosed_of_isAlmostWeakStarClosed _ (f.isAlmostWeakStarClosed_range_transpose hf)
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro s hs
  -- Choose a convex balanced neighbourhood `W` of zero with `W + W ⊆ f ⁻¹' s`.
  obtain ⟨U₁, hU₁, hU₁s⟩ := exists_nhds_zero_half (mem_map.mp hs)
  obtain ⟨W, ⟨hW, hWc, hWb⟩, hWU₁⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hU₁
  have hV : closure (f '' W) ∈ 𝓝 (0 : F) :=
    LinearMap.closure_image_mem_nhds_of_barrelledSpace (f := f.toLinearMap) hf hWc hWb hW
  refine mem_of_superset hV fun y₀ hy₀ ↦ ?_
  obtain ⟨x₀, rfl⟩ := hf y₀
  -- The point `x₀` lies in the closure of `W + ker f`, by the bipolar theorem.
  let N : Set E := (LinearMap.ker f.toLinearMap : Set E)
  have hNc : Convex ℝ N := ((LinearMap.ker f.toLinearMap).restrictScalars ℝ).convex
  have hNb : Balanced 𝕜 N := (LinearMap.ker f.toLinearMap).balanced
  have hx₀ : x₀ ∈ closure (W + N) := by
    by_contra hx₀
    obtain ⟨φ, hφ, hφx₀⟩ := StrongDual.exists_mem_polar_one_lt_norm (𝕜 := 𝕜)
      (hWc.add hNc).closure (hWb.add hNb).closure isClosed_closure
      ⟨0, subset_closure ⟨0, mem_of_mem_nhds hW, 0, (LinearMap.ker f.toLinearMap).zero_mem,
        add_zero 0⟩⟩ hx₀
    have hφW (w : E) (hw : w ∈ W) : ‖φ w‖ ≤ 1 :=
      hφ w (subset_closure ⟨w, hw, 0, (LinearMap.ker f.toLinearMap).zero_mem, add_zero w⟩)
    have hφN (x : E) (hx : f x = 0) : φ x = 0 :=
      LinearMap.eq_zero_of_forall_norm_le_one (Q := LinearMap.ker f.toLinearMap)
        (φ := φ.toLinearMap)
        (fun n hn ↦ hφ n (subset_closure ⟨0, mem_of_mem_nhds hW, n, hn, zero_add n⟩))
        (LinearMap.mem_ker.mpr hx)
    obtain ⟨ψ, rfl⟩ := f.mem_range_transpose_of_forall_ker hQ hφN
    have hcl : IsClosed {y : F | ‖ψ y‖ ≤ 1} := isClosed_le ψ.continuous.norm continuous_const
    have hψ : ‖ψ (f x₀)‖ ≤ 1 :=
      closure_minimal (s := f '' W) (by
        rintro _ ⟨w, hw, rfl⟩
        exact hφW w hw) hcl hy₀
    have h2 : (1 : ℝ) < ‖ψ (f x₀)‖ := hφx₀
    linarith
  -- Hence `x₀ ∈ W + ker f + W`, and `f x₀ ∈ f '' (W + W)`.
  have hmem : {z : E | x₀ - z ∈ W} ∈ 𝓝 x₀ := by
    have hc : ContinuousAt (fun z : E ↦ x₀ - z) x₀ := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hW)
  obtain ⟨z, hzW, w, hw, n, hn, rfl⟩ := mem_closure_iff_nhds.mp hx₀ _ hmem
  have hfn : f n = 0 := LinearMap.mem_ker.mp hn
  have hfx₀ : f x₀ = f (w + (x₀ - (w + n))) := by
    rw [map_add, map_sub, map_add, hfn]
    abel
  rw [hfx₀]
  exact hU₁s w (hWU₁ hw) _ (hWU₁ hzW)

/-- A continuous linear map from a Pták locally convex space onto a barrelled Hausdorff locally
convex space is a quotient map. -/
theorem ContinuousLinearMap.isQuotientMap_of_ptakSpace [LocallyConvexSpace ℝ E] [PtakSpace 𝕜 E]
    [LocallyConvexSpace ℝ F] [BarrelledSpace 𝕜 F] [T1Space F] (f : E →L[𝕜] F)
    (hf : Function.Surjective f) : Topology.IsQuotientMap f :=
  (f.isOpenMap_of_ptakSpace hf).isQuotientMap f.continuous hf

end OpenMappingTheorem
