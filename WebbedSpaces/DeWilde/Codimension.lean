/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.FinestTopology
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WebbedSpaces.DeWilde.Kato
public import WebbedSpaces.DeWilde.OpenMapping
public import WebbedSpaces.Frechet
public import WebbedSpaces.Hereditary
public import WebbedSpaces.InductiveLimit

/-!
# Ranges of finite or countable codimension

Let `A` be a sequentially closed linear map from a subspace of a webbed locally convex space `E`
into an ultrabornological space `F`. If the range of `A` has finite or countable codimension in
`F`, then `A` is open onto its range, the range is closed, and every algebraic complement of the
range is a topological complement that carries its finest locally convex topology
([G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5.(2)). For Banach spaces and finite
codimension this is Kato's theorem. If moreover `F` is first-countable, for instance a Fréchet
space, then the codimension is finite (§35.5.(3)), because the space `φ` of finitely supported
sequences with its finest locally convex topology is not metrizable.

The proof applies `WebbedSpaces.DeWilde.Kato` to the space `ι →₀ 𝕜` of finitely supported
families with its finest locally convex topology, which is webbed for countable `ι`, and to the
map `c ↦ ∑ c i • v i` onto an algebraic complement of the range.

## Imported construction

* `Finsupp.finestLocallyConvexTopology 𝕜 ι`: the finest locally convex topology on `ι →₀ 𝕜`,
  that is the topology of the locally convex direct sum of copies of `𝕜`.

## Main statements

* `Finsupp.finestLocallyConvexTopology.webbedSpace`; Hausdorffness, the universal property,
  and the failure of first countability are imported from `LocallyConvexSpaces.FinestTopology`.
* `Submodule.isClosed_snd_image_of_countable_codimension`,
  `Submodule.exists_nhds_inter_subset_image_of_countable_codimension`,
  `Submodule.exists_nhds_forall_decomposition_of_countable_codimension`,
  `Submodule.finite_of_countable_codimension_of_firstCountableTopology`: the statements for linear
  relations.
* `LinearMap.isClosed_range_of_basis_quotient`,
  `LinearMap.exists_nhds_inter_range_subset_image_of_basis_quotient`: a sequentially closed
  linear map whose range has countable codimension has a closed range and is open onto it.
* `LinearMap.finite_of_basis_quotient_of_firstCountableTopology`: §35.5.(3).
* `LinearMap.continuous_projectionOnto_of_basis_isCompl`,
  `LinearMap.continuous_of_basis_isCompl_range`, `LinearMap.isClosed_of_basis_isCompl_range`:
  algebraic complements of the range are topological complements with the finest locally convex
  topology.
* `Submodule.isClosed_of_isSeqClosed_of_basis_quotient`,
  `Submodule.continuous_projectionOnto_of_isSeqClosed_of_basis`,
  `Submodule.finite_of_isSeqClosed_of_basis_quotient`: a sequentially closed subspace of
  countable codimension of a webbed ultrabornological space is closed and topologically
  complemented, §35.5.(5) b).

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5.(2), (3), (5)

## Tags

Kato theorem, codimension, closed range, webbed space, De Wilde
-/

public section

open Set Filter Function

open scoped Topology

universe u v

namespace Finsupp.finestLocallyConvexTopology

variable {𝕜 ι : Type*} [RCLike 𝕜]

/-- For countable `ι` the space `ι →₀ 𝕜` with its finest locally convex topology is webbed. -/
theorem webbedSpace [Countable ι] :
    @WebbedSpace (ι →₀ 𝕜) _ _ (Finsupp.finestLocallyConvexTopology 𝕜 ι) := by
  have : WebbedSpace 𝕜 := StrictlyWebbedSpace.toWebbedSpace (𝕜 := 𝕜)
  exact locallyConvexFinalTopology.webbedSpace
    (fun i : ι ↦ (Finsupp.lsingle i : 𝕜 →ₗ[𝕜] ι →₀ 𝕜)) Finsupp.iSup_lsingle_range

end Finsupp.finestLocallyConvexTopology

section Codimension

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type*} {F : Type u} {ι : Type*} [Countable ι]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [WebbedSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [UltrabornologicalSpace 𝕜 F]

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [WebbedSpace E] in
/-- The common part of the statements below: the hypotheses of
`WebbedSpaces.DeWilde.Kato` hold for the map `c ↦ ∑ c i • v i` on `ι →₀ 𝕜` with its
finest locally convex topology. -/
private theorem exists_clm_linearCombination (G : Submodule 𝕜 (E × F)) (v : ι → F)
    (hsum : ∀ y : F, ∃ q ∈ G, ∃ c : ι →₀ 𝕜, y = q.2 + Finsupp.linearCombination 𝕜 v c)
    (hindep : ∀ q ∈ G, ∀ c : ι →₀ 𝕜, q.2 = Finsupp.linearCombination 𝕜 v c → c = 0) :
    ∃ (t : TopologicalSpace (ι →₀ 𝕜)) (_ : IsTopologicalAddGroup (ι →₀ 𝕜))
      (_ : ContinuousSMul 𝕜 (ι →₀ 𝕜)) (_ : LocallyConvexSpace ℝ (ι →₀ 𝕜))
      (_ : WebbedSpace (ι →₀ 𝕜)) (_ : T2Space (ι →₀ 𝕜)) (j : (ι →₀ 𝕜) →L[𝕜] F),
      t = Finsupp.finestLocallyConvexTopology 𝕜 ι ∧
      (∀ y : F, ∃ q ∈ G, ∃ z : ι →₀ 𝕜, y = q.2 + j z) ∧
      (∀ q ∈ G, ∀ z : ι →₀ 𝕜, q.2 = j z → j z = 0) ∧ Injective j ∧
      ∀ c, j c = Finsupp.linearCombination 𝕜 v c := by
  have : IsTopologicalAddGroup F := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 F
  have : ContinuousSMul 𝕜 F := UltrabornologicalSpace.continuousSMul 𝕜 F
  have : LocallyConvexSpace ℝ F := UltrabornologicalSpace.locallyConvexSpace 𝕜 F
  let f := fun i : ι ↦ (Finsupp.lsingle i : 𝕜 →ₗ[𝕜] ι →₀ 𝕜)
  let _ : TopologicalSpace (ι →₀ 𝕜) := Finsupp.finestLocallyConvexTopology 𝕜 ι
  let j : (ι →₀ 𝕜) →L[𝕜] F :=
    ⟨Finsupp.linearCombination 𝕜 v, Finsupp.finestLocallyConvexTopology.continuous_linearMap _⟩
  have hj (c : ι →₀ 𝕜) : j c = Finsupp.linearCombination 𝕜 v c := rfl
  refine ⟨Finsupp.finestLocallyConvexTopology 𝕜 ι,
    locallyConvexFinalTopology.isTopologicalAddGroup f,
    locallyConvexFinalTopology.continuousSMul f,
    locallyConvexFinalTopology.locallyConvexSpace f,
    Finsupp.finestLocallyConvexTopology.webbedSpace,
    Finsupp.finestLocallyConvexTopology.t2Space, j, rfl, hsum,
    fun q hq c hqc ↦ by rw [hindep q hq c hqc, map_zero], fun c c' hcc' ↦ ?_, hj⟩
  have h := hindep 0 G.zero_mem (c - c') (by
    rw [← hj, map_sub, hcc', sub_self]
    rfl)
  exact sub_eq_zero.mp h

variable (G : Submodule 𝕜 (E × F)) (hG : IsSeqClosed (G : Set (E × F))) (v : ι → F)
  (hsum : ∀ y : F, ∃ q ∈ G, ∃ c : ι →₀ 𝕜, y = q.2 + Finsupp.linearCombination 𝕜 v c)
  (hindep : ∀ q ∈ G, ∀ c : ι →₀ 𝕜, q.2 = Finsupp.linearCombination 𝕜 v c → c = 0)

include hG hsum hindep

/-- Let `G` be a sequentially closed linear relation between a webbed locally convex space and an
ultrabornological space, and let `v` be a countable family that is a basis of an algebraic
complement of the range of `G`. Then the range of `G` is closed, Köthe II §35.5.(2). -/
theorem Submodule.isClosed_snd_image_of_countable_codimension :
    IsClosed (Prod.snd '' (G : Set (E × F))) := by
  obtain ⟨_, _, _, _, _, _, j, -, hsum', hdisj, hinj, -⟩ :=
    exists_clm_linearCombination G v hsum hindep
  exact G.isClosed_snd_image_of_webbed_complement hG j hsum' hdisj hinj

/-- Under the hypotheses of `Submodule.isClosed_snd_image_of_countable_codimension`,
the relation `G` is open onto its range, Köthe II §35.5.(2). -/
theorem Submodule.exists_nhds_inter_subset_image_of_countable_codimension {V : Set E}
    (hV : V ∈ 𝓝 (0 : E)) :
    ∃ N ∈ 𝓝 (0 : F), N ∩ Prod.snd '' (G : Set (E × F)) ⊆ SetRel.image (G : Set (E × F)) V := by
  obtain ⟨_, _, _, _, _, _, j, -, hsum', hdisj, -, -⟩ :=
    exists_clm_linearCombination G v hsum hindep
  exact G.exists_nhds_inter_subset_image_of_webbed_complement hG j hsum' hdisj hV

/-- Under the hypotheses of `Submodule.isClosed_snd_image_of_countable_codimension`, the coefficients of the component in the complement of a point
near zero are small for the finest locally convex topology of `ι →₀ 𝕜`: the projection onto
the complement is continuous and the complement carries its finest locally convex topology,
Köthe II §35.5.(2). -/
theorem Submodule.exists_nhds_forall_decomposition_of_countable_codimension
    {W : Set (ι →₀ 𝕜)} (hW : W ∈ @nhds _ (Finsupp.finestLocallyConvexTopology 𝕜 ι) 0) :
    ∃ N ∈ 𝓝 (0 : F), ∀ y ∈ N, ∀ q ∈ G, ∀ c : ι →₀ 𝕜,
      y = q.2 + Finsupp.linearCombination 𝕜 v c → c ∈ W := by
  obtain ⟨t, _, _, _, _, _, j, ht, hsum', hdisj, hinj, hj⟩ :=
    exists_clm_linearCombination G v hsum hindep
  rw [← ht] at hW
  obtain ⟨N, hN, h⟩ :=
    G.exists_nhds_forall_decomposition_of_webbed_complement hG j hsum' hdisj hW
  refine ⟨N, hN, fun y hy q hq c hyc ↦ ?_⟩
  obtain ⟨w, hw, hwc⟩ := h y hy q hq c (by rw [hj, hyc])
  exact hinj hwc ▸ hw

/-- Under the hypotheses of `Submodule.isClosed_snd_image_of_countable_codimension`,
if `F` is first-countable then the complement is finite
dimensional, since the space `φ` is not metrizable, Köthe II §35.5.(3). -/
theorem Submodule.finite_of_countable_codimension_of_firstCountableTopology
    [FirstCountableTopology F] : Finite ι := by
  by_contra hfin
  have : Infinite ι := not_finite_iff_infinite.mp hfin
  obtain ⟨t, _, _, _, _, _, j, ht, hsum', hdisj, hinj, -⟩ :=
    exists_clm_linearCombination G v hsum hindep
  have hind := G.isInducing_of_webbed_complement hG j hsum' hdisj hinj
  refine Finsupp.finestLocallyConvexTopology.not_isCountablyGenerated_nhds_zero
    (𝕜 := 𝕜) (ι := ι) ?_
  rw [← ht, hind.nhds_eq_comap, map_zero]
  infer_instance

end Codimension

section Family

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- A basis of the quotient by the range of `A` lifts to a family that is a basis of an algebraic
complement of the range. -/
private theorem LinearMap.exists_family_of_basis_quotient (A : E →ₗ[𝕜] F)
    (b : Module.Basis ι 𝕜 (F ⧸ LinearMap.range A)) :
    ∃ v : ι → F,
      (∀ y : F, ∃ q ∈ A.graph, ∃ c : ι →₀ 𝕜, y = q.2 + Finsupp.linearCombination 𝕜 v c) ∧
      ∀ q ∈ A.graph, ∀ c : ι →₀ 𝕜, q.2 = Finsupp.linearCombination 𝕜 v c → c = 0 := by
  choose v hv using fun i ↦ (LinearMap.range A).mkQ_surjective (b i)
  have hmk (c : ι →₀ 𝕜) :
      (LinearMap.range A).mkQ (Finsupp.linearCombination 𝕜 v c) = b.repr.symm c := by
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, map_finsuppSum]
    exact Finsupp.sum_congr fun i _ ↦ by rw [map_smul, hv]
  refine ⟨v, fun y ↦ ?_, fun q hq c hqc ↦ ?_⟩
  · -- `y` minus its component along `v` lies in the range of `A`.
    let c := b.repr ((LinearMap.range A).mkQ y)
    have hmem : y - Finsupp.linearCombination 𝕜 v c ∈ LinearMap.range A := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change (LinearMap.range A).mkQ y - (LinearMap.range A).mkQ _ = 0
      rw [hmk, LinearEquiv.symm_apply_apply, sub_self]
    obtain ⟨x, hx⟩ := hmem
    exact ⟨(x, A x), (LinearMap.mem_graph_iff _ _).mpr rfl, c, by rw [hx, sub_add_cancel]⟩
  · have hq2 : q.2 = A q.1 := (LinearMap.mem_graph_iff _ _).mp hq
    have h0 : b.repr.symm c = 0 := by
      rw [← hmk, ← hqc, hq2]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨q.1, rfl⟩
    exact (LinearEquiv.map_eq_zero_iff _).mp h0

/-- The linear combinations of a basis of a subspace, computed in the ambient space. -/
private theorem linearCombination_coe_basis {K : Submodule 𝕜 F} (b : Module.Basis ι 𝕜 K)
    (c : ι →₀ 𝕜) : Finsupp.linearCombination 𝕜 (fun i ↦ (b i : F)) c =
      ((Finsupp.linearCombination 𝕜 b c : K) : F) :=
  (Finsupp.apply_linearCombination 𝕜 K.subtype b c).symm

/-- A basis of an algebraic complement of the range of `A`, as a family in the codomain. -/
private theorem LinearMap.family_of_basis_isCompl (A : E →ₗ[𝕜] F) {K : Submodule 𝕜 F}
    (hK : IsCompl (LinearMap.range A) K) (b : Module.Basis ι 𝕜 K) :
    (∀ y : F, ∃ q ∈ A.graph, ∃ c : ι →₀ 𝕜,
      y = q.2 + Finsupp.linearCombination 𝕜 (fun i ↦ (b i : F)) c) ∧
      ∀ q ∈ A.graph, ∀ c : ι →₀ 𝕜,
        q.2 = Finsupp.linearCombination 𝕜 (fun i ↦ (b i : F)) c → c = 0 := by
  refine ⟨fun y ↦ ?_, fun q hq c hqc ↦ ?_⟩
  · have hy : y ∈ LinearMap.range A ⊔ K := hK.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨_, ⟨x, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨(x, A x), (LinearMap.mem_graph_iff _ _).mpr rfl, b.repr ⟨k, hk⟩, ?_⟩
    rw [linearCombination_coe_basis, b.linearCombination_repr]
  · have hq2 : q.2 = A q.1 := (LinearMap.mem_graph_iff _ _).mp hq
    rw [linearCombination_coe_basis] at hqc
    have h0 : ((Finsupp.linearCombination 𝕜 b c : K) : F) = 0 :=
      Submodule.disjoint_def.mp hK.disjoint _ ⟨q.1, by rw [← hqc, hq2]⟩ (Subtype.coe_prop _)
    have h1 : Finsupp.linearCombination 𝕜 b c = 0 := Subtype.ext h0
    rw [← b.repr_linearCombination c, h1, map_zero]

end Family

section LinearMap

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type*} {F : Type u} {ι : Type*} [Countable ι]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [WebbedSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [UltrabornologicalSpace 𝕜 F]

/-- **Kato's theorem in De Wilde's form**: a linear map with sequentially closed graph from a
webbed locally convex space into an ultrabornological space whose range has finite or countable
codimension has a closed range, Köthe II §35.5.(2). The codimension is expressed by a basis of
the quotient by the range with a countable index type. -/
theorem LinearMap.isClosed_range_of_basis_quotient (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F)))
    (b : Module.Basis ι 𝕜 (F ⧸ LinearMap.range A)) : IsClosed (Set.range A) := by
  obtain ⟨v, hsum, hindep⟩ := A.exists_family_of_basis_quotient b
  have hclosed := A.graph.isClosed_snd_image_of_countable_codimension hA v hsum hindep
  rwa [A.snd_image_graph] at hclosed

/-- A linear map with sequentially closed graph from a webbed locally convex space into an
ultrabornological space whose range has finite or countable codimension is open onto its range,
Köthe II §35.5.(2). -/
theorem LinearMap.exists_nhds_inter_range_subset_image_of_basis_quotient (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F)))
    (b : Module.Basis ι 𝕜 (F ⧸ LinearMap.range A)) {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    ∃ N ∈ 𝓝 (0 : F), N ∩ Set.range A ⊆ A '' V := by
  obtain ⟨v, hsum, hindep⟩ := A.exists_family_of_basis_quotient b
  have h := A.graph.exists_nhds_inter_subset_image_of_countable_codimension hA v hsum hindep hV
  rwa [A.snd_image_graph, A.image_graph] at h

/-- A linear map with sequentially closed graph from a webbed locally convex space into a
first-countable ultrabornological space, for instance a Fréchet space, whose range has at most
countable codimension has a range of finite codimension, Köthe II §35.5.(3). -/
theorem LinearMap.finite_of_basis_quotient_of_firstCountableTopology
    [FirstCountableTopology F] (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F)))
    (b : Module.Basis ι 𝕜 (F ⧸ LinearMap.range A)) : Finite ι := by
  obtain ⟨v, hsum, hindep⟩ := A.exists_family_of_basis_quotient b
  exact A.graph.finite_of_countable_codimension_of_firstCountableTopology hA v hsum hindep

/-- Let `A` be a linear map with sequentially closed graph from a webbed locally convex space
into an ultrabornological space. Every algebraic complement of the range of `A` that has a
countable basis is a topological complement: the projection onto it along the range is
continuous, Köthe II §35.5.(2). -/
theorem LinearMap.continuous_projectionOnto_of_basis_isCompl (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) {K : Submodule 𝕜 F}
    (hK : IsCompl (LinearMap.range A) K) (b : Module.Basis ι 𝕜 K) :
    Continuous (K.projectionOnto (LinearMap.range A) hK.symm) := by
  have : IsTopologicalAddGroup F := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 F
  have : ContinuousSMul 𝕜 F := UltrabornologicalSpace.continuousSMul 𝕜 F
  have : LocallyConvexSpace ℝ F := UltrabornologicalSpace.locallyConvexSpace 𝕜 F
  obtain ⟨hsum, hindep⟩ := A.family_of_basis_isCompl hK b
  let P := K.projectionOnto (LinearMap.range A) hK.symm
  -- The projection of `A x + ∑ c i • b i` is `∑ c i • b i`.
  have hP (q : E × F) (hq : q ∈ A.graph) (c : ι →₀ 𝕜) :
      P (q.2 + Finsupp.linearCombination 𝕜 (fun i ↦ (b i : F)) c) =
        Finsupp.linearCombination 𝕜 b c := by
    have hq2 : q.2 = A q.1 := (LinearMap.mem_graph_iff _ _).mp hq
    have h1 : P q.2 = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff hK.symm).mpr ⟨q.1, hq2.symm⟩
    rw [map_add, h1, zero_add, linearCombination_coe_basis]
    exact Submodule.projectionOnto_apply_left hK.symm _
  refine continuous_of_continuousAt_zero P ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  -- Neighbourhoods of zero in `K` come from neighbourhoods of zero in `F`.
  rw [nhds_subtype_eq_comap] at hW
  obtain ⟨W', hW', hWW'⟩ := hW
  let g : (ι →₀ 𝕜) →ₗ[𝕜] F := Finsupp.linearCombination 𝕜 fun i ↦ (b i : F)
  have hg : g ⁻¹' W' ∈ @nhds _ (Finsupp.finestLocallyConvexTopology 𝕜 ι) 0 := by
    let _ : TopologicalSpace (ι →₀ 𝕜) := Finsupp.finestLocallyConvexTopology 𝕜 ι
    have hc : Continuous g := Finsupp.finestLocallyConvexTopology.continuous_linearMap g
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW')
  obtain ⟨N, hN, h⟩ := A.graph.exists_nhds_forall_decomposition_of_countable_codimension hA
    (fun i ↦ (b i : F)) hsum hindep hg
  refine mem_map.mpr (mem_of_superset hN fun y hy ↦ hWW' ?_)
  obtain ⟨q, hq, c, hyc⟩ := hsum y
  have hc : g c ∈ W' := h y hy q hq c hyc
  rw [hyc, hP q hq c, mem_preimage, ← linearCombination_coe_basis]
  exact hc

/-- Under the hypotheses of `LinearMap.continuous_projectionOnto_of_basis_isCompl` an algebraic
complement of the range with a countable basis carries its finest locally convex topology: every
linear map from it into a locally convex space is continuous, Köthe II §35.5.(2). -/
theorem LinearMap.continuous_of_basis_isCompl_range (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) {K : Submodule 𝕜 F}
    (hK : IsCompl (LinearMap.range A) K) (b : Module.Basis ι 𝕜 K) {X : Type*} [AddCommGroup X]
    [Module 𝕜 X] [Module ℝ X] [IsScalarTower ℝ 𝕜 X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [LocallyConvexSpace ℝ X] (g : K →ₗ[𝕜] X) :
    Continuous g := by
  have : IsTopologicalAddGroup F := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 F
  obtain ⟨hsum, hindep⟩ := A.family_of_basis_isCompl hK b
  let _ : TopologicalSpace (ι →₀ 𝕜) := Finsupp.finestLocallyConvexTopology 𝕜 ι
  have : IsTopologicalAddGroup (ι →₀ 𝕜) := locallyConvexFinalTopology.isTopologicalAddGroup _
  -- It suffices that the coordinates `b.repr` are continuous.
  suffices hrepr : Continuous b.repr by
    have hc := (Finsupp.finestLocallyConvexTopology.continuous_linearMap
      (g ∘ₗ b.repr.symm.toLinearMap)).comp hrepr
    refine hc.congr fun k ↦ ?_
    simp
  refine continuous_of_continuousAt_zero b.repr ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  obtain ⟨N, hN, h⟩ := A.graph.exists_nhds_forall_decomposition_of_countable_codimension hA
    (fun i ↦ (b i : F)) hsum hindep hW
  have hpre : ((↑) : K → F) ⁻¹' N ∈ 𝓝 (0 : K) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN)
  refine mem_map.mpr (mem_of_superset hpre fun k hk ↦ ?_)
  refine h (k : F) hk 0 (Submodule.zero_mem _) (b.repr k) ?_
  rw [linearCombination_coe_basis, b.linearCombination_repr, Prod.snd_zero, zero_add]

/-- Under the hypotheses of `LinearMap.continuous_projectionOnto_of_basis_isCompl`, if `F` is
Hausdorff then the complement is closed. -/
theorem LinearMap.isClosed_of_basis_isCompl_range [T2Space F] (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) {K : Submodule 𝕜 F}
    (hK : IsCompl (LinearMap.range A) K) (b : Module.Basis ι 𝕜 K) : IsClosed (K : Set F) := by
  have hc := A.continuous_projectionOnto_of_basis_isCompl hA hK b
  have h : (K : Set F) = {y | ((K.projectionOnto (LinearMap.range A) hK.symm y : K) : F) = y} := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hK.symm ⟨y, hy⟩)
    · have hy' : ((K.projectionOnto (LinearMap.range A) hK.symm y : K) : F) = y := hy
      exact hy' ▸ Subtype.coe_prop _
  rw [h]
  exact isClosed_eq (continuous_subtype_val.comp hc) continuous_id

end LinearMap

section Subspace

variable {𝕜 : Type v} [RCLike 𝕜] {E : Type u} {ι : Type*} [Countable ι] [AddCommGroup E]
  [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [UltrabornologicalSpace 𝕜 E] [WebbedSpace E] [T2Space E]

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UltrabornologicalSpace 𝕜 E] [WebbedSpace E] in
/-- The inclusion of a subspace of a Hausdorff space has a sequentially closed graph. -/
private theorem Submodule.isSeqClosed_graph_subtype (H : Submodule 𝕜 E) :
    IsSeqClosed (H.subtype.graph : Set (H × E)) :=
  H.subtypeL.isClosed_graph.isSeqClosed

/-- In a Hausdorff space that is webbed and ultrabornological, a sequentially closed subspace of
finite or countable codimension is closed, Köthe II §35.5.(5) b). -/
theorem Submodule.isClosed_of_isSeqClosed_of_basis_quotient (H : Submodule 𝕜 E)
    (hH : IsSeqClosed (H : Set E)) (b : Module.Basis ι 𝕜 (E ⧸ H)) : IsClosed (H : Set E) := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  have : ContinuousSMul 𝕜 E := UltrabornologicalSpace.continuousSMul 𝕜 E
  have : LocallyConvexSpace ℝ E := UltrabornologicalSpace.locallyConvexSpace 𝕜 E
  have : LocallyConvexSpace ℝ H :=
    Topology.IsInducing.locallyConvexSpace (f := H.subtype.restrictScalars ℝ) .subtypeVal
  have : WebbedSpace H := WebbedSpace.of_isSeqClosed H hH
  have h := H.subtype.isClosed_range_of_basis_quotient H.isSeqClosed_graph_subtype
    (b.map (Submodule.quotEquivOfEq _ _ H.range_subtype.symm))
  have hset : Set.range H.subtype = (H : Set E) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rwa [hset] at h

/-- In a Hausdorff space that is webbed and ultrabornological, every algebraic complement with a
countable basis of a sequentially closed subspace is a topological complement: the projection
onto it is continuous, Köthe II §35.5.(5) b). -/
theorem Submodule.continuous_projectionOnto_of_isSeqClosed_of_basis (H : Submodule 𝕜 E)
    (hH : IsSeqClosed (H : Set E)) {K : Submodule 𝕜 E} (hK : IsCompl H K)
    (b : Module.Basis ι 𝕜 K) : Continuous (K.projectionOnto H hK.symm) := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  have : ContinuousSMul 𝕜 E := UltrabornologicalSpace.continuousSMul 𝕜 E
  have : LocallyConvexSpace ℝ E := UltrabornologicalSpace.locallyConvexSpace 𝕜 E
  have : LocallyConvexSpace ℝ H :=
    Topology.IsInducing.locallyConvexSpace (f := H.subtype.restrictScalars ℝ) .subtypeVal
  have : WebbedSpace H := WebbedSpace.of_isSeqClosed H hH
  have key : ∀ (H' : Submodule 𝕜 E) (_ : H' = H) (h' : IsCompl H' K),
      Continuous (K.projectionOnto H' h'.symm) → Continuous (K.projectionOnto H hK.symm) := by
    rintro _ rfl _ h
    exact h
  have hK' : IsCompl (LinearMap.range H.subtype) K := by rwa [H.range_subtype]
  exact key _ H.range_subtype hK'
    (H.subtype.continuous_projectionOnto_of_basis_isCompl H.isSeqClosed_graph_subtype hK' b)

/-- In a Hausdorff first-countable space that is webbed and ultrabornological, for instance in a
Fréchet space, a sequentially closed subspace of at most countable codimension has finite
codimension, Köthe II §35.5.(3). -/
theorem Submodule.finite_of_isSeqClosed_of_basis_quotient [FirstCountableTopology E]
    (H : Submodule 𝕜 E) (hH : IsSeqClosed (H : Set E)) (b : Module.Basis ι 𝕜 (E ⧸ H)) :
    Finite ι := by
  have : IsTopologicalAddGroup E := UltrabornologicalSpace.isTopologicalAddGroup 𝕜 E
  have : ContinuousSMul 𝕜 E := UltrabornologicalSpace.continuousSMul 𝕜 E
  have : LocallyConvexSpace ℝ E := UltrabornologicalSpace.locallyConvexSpace 𝕜 E
  have : LocallyConvexSpace ℝ H :=
    Topology.IsInducing.locallyConvexSpace (f := H.subtype.restrictScalars ℝ) .subtypeVal
  have : WebbedSpace H := WebbedSpace.of_isSeqClosed H hH
  exact H.subtype.finite_of_basis_quotient_of_firstCountableTopology H.isSeqClosed_graph_subtype
    (b.map (Submodule.quotEquivOfEq _ _ H.range_subtype.symm))

end Subspace
