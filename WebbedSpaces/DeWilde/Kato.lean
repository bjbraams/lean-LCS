/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.PairingTopology
public import WebbedSpaces.DeWilde.Relation
public import WebbedSpaces.Product

/-!
# De Wilde's generalization of the open mapping theorem to ranges with a webbed complement

Kato proved that a closed operator between Banach spaces whose range has finite codimension has a
closed range and is open onto its range. De Wilde's version ([G. Köthe, *Topological Vector Spaces
II*][kothe1979], §35.5.(1)) is as follows. Let `E` be a webbed locally convex space, `F` an
ultrabornological space and `A` a sequentially closed linear map from a subspace of `E` into `F`.
Suppose that the range of `A` has an algebraic complement `H` in `F` that is a webbed space for some
locally convex topology finer than the one induced by `F`. Then `A` is open onto its range, the
finer topology of `H` is the induced one, and the projection of `F` onto `H` along the range of `A`
is continuous. With the appropriate Hausdorff hypotheses the complements are also closed. The formal
closed-range theorem assumes that `H` is Hausdorff and that its map into `F` is injective.

Here the map `A` is represented by its graph `G`, a linear subspace of `E × F`, and the
complement with its finer topology by a continuous linear map `ι : H → F` from a webbed locally
convex space `H`. The algebraic assumptions are `hsum`: every `y : F` is `q.2 + ι z` with
`q ∈ G`, and `hdisj`: if `q.2 = ι z` with `q ∈ G` then `ι z = 0`. The proof applies De Wilde's
theorem for relations to the relation `{((x, z), y) | (x, y - ι z) ∈ G}` between the webbed space
`E × H` and `F`.

## Main statements

* `Submodule.exists_nhds_inter_subset_image_of_webbed_complement`: `A` is open onto its range.
* `Submodule.exists_nhds_forall_decomposition_of_webbed_complement`: the projection onto the
  complement is continuous at zero.
* `Submodule.isInducing_of_webbed_complement`: the topology of the complement is induced by `F`.
* `Submodule.isClosed_snd_image_of_webbed_complement`: the range is closed.

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5.(1)

## Tags

open mapping theorem, De Wilde, Kato, codimension, complemented subspace
-/

public section

open Set Filter Function

open scoped Topology

universe u v

variable {𝕜 : Type v} [RCLike 𝕜] {E H : Type*} {F : Type u}
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [WebbedSpace E]
  [AddCommGroup H] [Module 𝕜 H] [Module ℝ H] [IsScalarTower ℝ 𝕜 H] [TopologicalSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul 𝕜 H] [LocallyConvexSpace ℝ H] [WebbedSpace H]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [UltrabornologicalSpace 𝕜 F]

namespace Submodule

/-- The relation `{((x, z), y) | (x, y - ι z) ∈ G}` between `E × H` and `F`. -/
private def sumRel (G : Submodule 𝕜 (E × F)) (ι : H →L[𝕜] F) : Submodule 𝕜 ((E × H) × F) :=
  G.comap ((LinearMap.fst 𝕜 E H ∘ₗ LinearMap.fst 𝕜 (E × H) F).prod
    (LinearMap.snd 𝕜 (E × H) F - ι.toLinearMap ∘ₗ LinearMap.snd 𝕜 E H ∘ₗ
      LinearMap.fst 𝕜 (E × H) F))

/-- The key step: the sum relation maps neighbourhoods of zero to neighbourhoods of zero. -/
private theorem image_sumRel_mem_nhds_zero (G : Submodule 𝕜 (E × F))
    (hG : IsSeqClosed (G : Set (E × F))) (ι : H →L[𝕜] F)
    (hsum : ∀ y : F, ∃ q ∈ G, ∃ z : H, y = q.2 + ι z) {V : Set (E × H)}
    (hV : V ∈ 𝓝 (0 : E × H)) :
    SetRel.image (sumRel G ι : Set ((E × H) × F)) V ∈ 𝓝 (0 : F) := by
  refine (sumRel G ι).image_mem_nhds_zero_of_ultrabornologicalSpace ?_ ?_ hV
  · have hcont : Continuous fun p : (E × H) × F ↦ (p.1.1, p.2 - ι p.1.2) :=
      (continuous_fst.comp continuous_fst).prodMk
        (continuous_snd.sub (ι.continuous.comp (continuous_snd.comp continuous_fst)))
    exact hG.preimage hcont.seqContinuous
  · refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨q, hq, z, hy⟩ := hsum y
    refine ⟨((q.1, z), y), ?_, rfl⟩
    change (q.1, y - ι z) ∈ G
    have : y - ι z = q.2 := by rw [hy, add_sub_cancel_right]
    rw [this]
    exact hq

variable (G : Submodule 𝕜 (E × F)) (hG : IsSeqClosed (G : Set (E × F))) (ι : H →L[𝕜] F)
  (hsum : ∀ y : F, ∃ q ∈ G, ∃ z : H, y = q.2 + ι z)
  (hdisj : ∀ q ∈ G, ∀ z : H, q.2 = ι z → ι z = 0)

include hG hsum hdisj

/-- **De Wilde's open mapping theorem for a range with a webbed complement**: the relation `G`
is open onto its range, Köthe II §35.5.(1). -/
theorem exists_nhds_inter_subset_image_of_webbed_complement {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    ∃ N ∈ 𝓝 (0 : F), N ∩ Prod.snd '' (G : Set (E × F)) ⊆ SetRel.image (G : Set (E × F)) V := by
  refine ⟨_, image_sumRel_mem_nhds_zero G hG ι hsum (prod_mem_nhds hV univ_mem), ?_⟩
  rintro y ⟨⟨⟨x, z⟩, ⟨hx, -⟩, hxz⟩, ⟨q, hq, rfl⟩⟩
  have h1 : (x, q.2 - ι z) ∈ G := hxz
  -- The difference of the two decompositions lies in the range of `G` and in that of `ι`.
  have h2 : q - (x, q.2 - ι z) ∈ G := G.sub_mem hq h1
  have h3 : ι z = 0 := hdisj _ h2 z (by simp)
  rw [h3, sub_zero] at h1
  exact ⟨x, hx, h1⟩

/-- Under the hypotheses of De Wilde's theorem the component in the complement of a point near
zero is small: this is the continuity at zero of the projection onto the complement along the
range of `G`, Köthe II §35.5.(1). -/
theorem exists_nhds_forall_decomposition_of_webbed_complement {W : Set H}
    (hW : W ∈ 𝓝 (0 : H)) :
    ∃ N ∈ 𝓝 (0 : F), ∀ y ∈ N, ∀ q ∈ G, ∀ z : H, y = q.2 + ι z → ι z ∈ ι '' W := by
  refine ⟨_, image_sumRel_mem_nhds_zero G hG ι hsum (prod_mem_nhds univ_mem hW), ?_⟩
  rintro y ⟨⟨x, z'⟩, ⟨-, hz'⟩, hxz⟩ q hq z hy
  have h1 : (x, y - ι z') ∈ G := hxz
  have h2 : (x, y - ι z') - q ∈ G := G.sub_mem h1 hq
  have h3 : ι (z - z') = 0 := hdisj _ h2 (z - z') (by
    rw [map_sub, hy]
    simp only [Prod.snd_sub]
    abel)
  rw [map_sub, sub_eq_zero] at h3
  exact ⟨z', hz', h3.symm⟩

/-- Under the hypotheses of De Wilde's theorem, if `ι` is injective then the topology of the
complement `H` is the one induced by `F`, Köthe II §35.5.(1). -/
theorem isInducing_of_webbed_complement (hι : Injective ι) : Topology.IsInducing ι := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp ι.continuous) ?_⟩
  refine IsTopologicalAddGroup.le_of_nhds_zero_le (isTopologicalAddGroup_induced ι) inferInstance
    fun W hW ↦ ?_
  obtain ⟨N, hN, h⟩ := exists_nhds_forall_decomposition_of_webbed_complement G hG ι hsum hdisj hW
  rw [nhds_induced, map_zero]
  refine mem_of_superset (preimage_mem_comap hN) fun z hz ↦ ?_
  obtain ⟨w, hw, hwz⟩ := h (ι z) hz 0 G.zero_mem z (by simp)
  exact hι hwz ▸ hw

/-- Under the hypotheses of De Wilde's theorem, if `ι` is injective and `H` is Hausdorff, then the
range of `G` is closed, Köthe II §35.5.(1). -/
theorem isClosed_snd_image_of_webbed_complement [T2Space H] (hι : Injective ι) :
    IsClosed (Prod.snd '' (G : Set (E × F))) := by
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨q, hq, z, hyq⟩ := hsum y
  -- The component `z` of `y` in the complement lies in every neighbourhood of zero.
  have hz : z = 0 := by
    by_contra hz
    obtain ⟨N, hN, h⟩ := exists_nhds_forall_decomposition_of_webbed_complement G hG ι hsum hdisj
      (compl_singleton_mem_nhds (Ne.symm hz))
    have hc : ContinuousAt (fun r : F ↦ y - r) y := by fun_prop
    have hpre : (fun r : F ↦ y - r) ⁻¹' N ∈ 𝓝 y := hc.preimage_mem_nhds (by simpa using hN)
    obtain ⟨_, hr, ⟨q', hq', rfl⟩⟩ := mem_closure_iff_nhds.mp hy _ hpre
    obtain ⟨w, hw, hwz⟩ := h (y - q'.2) hr (q - q') (G.sub_mem hq hq') z (by
      rw [hyq]
      simp only [Prod.snd_sub]
      abel)
    exact hw (hι hwz)
  rw [hyq, hz, map_zero, add_zero]
  exact ⟨q, hq, rfl⟩

end Submodule
