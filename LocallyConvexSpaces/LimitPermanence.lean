/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.ReflexivePermanence
public import LocallyConvexSpaces.MontelPermanence
public import LocallyConvexSpaces.StrictInductiveLimit
public import LocallyConvexSpaces.ProjectiveLimit

/-!
# Permanence under projective and strict inductive limits

Closed subspaces of products give semi-reflexive projective limits. A family of maps from
semi-reflexive or Montel spaces transfers the corresponding property if every bounded set
in the target is contained in the image of a bounded set in one source space. This applies
to countable strict inductive limits with closed transition ranges. Reflexivity additionally
uses barrelledness of the final locally convex topology.
The Montel bounded-cover theorem is imported from `LocallyConvexSpaces.MontelPermanence`
and works over any normed field.

These are independent proofs of the limit assertions in Schaefer–Wolff IV, Theorem 5.8
and the following discussion of Montel spaces. Mathlib's Montel convention omits barrelledness.
-/

public section

open Set Function Bornology

section BoundedCover

variable {𝕜 ι F : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
  [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, T1Space (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- Semi-reflexivity passes through a family of maps covering target bounded sets by images
of bounded sets in semi-reflexive source spaces. -/
theorem SemiReflexiveSpace.of_bounded_cover [∀ i, SemiReflexiveSpace 𝕜 (E i)]
    (f : ∀ i, E i →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ i, ∃ B : Set (E i), IsVonNBounded 𝕜 B ∧ S ⊆ f i '' B) : SemiReflexiveSpace 𝕜 F := by
  apply SemiReflexiveSpace.of_forall_isVonNBounded 𝕜 F
  intro S hS
  obtain ⟨i, B, hB, hSB⟩ := h S hS
  obtain ⟨K, hK, hBK⟩ := SemiReflexiveSpace.exists_mem_mackeyFamily_subset 𝕜 (E i) hB
  let g := WeakSpace.map (f i)
  refine ⟨g '' K, ⟨hK.1.image g.continuous,
    hK.2.1.linear_image (g.toLinearMap.restrictScalars ℝ), hK.2.2.image g.toLinearMap⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hSB hy
  exact ⟨toWeakSpace 𝕜 (E i) x, hBK ⟨x, hx, rfl⟩, rfl⟩

end BoundedCover

namespace StrictInductiveLimit

variable {𝕜 F : Type*} [RCLike 𝕜] {E : ℕ → Type*}
  [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
  [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [∀ n, IsTopologicalAddGroup (E n)] [∀ n, ContinuousSMul 𝕜 (E n)]
  [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, T1Space (E n)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  [tF : TopologicalSpace F] [ContinuousSMul 𝕜 F]
  (j : ∀ n, E n →L[𝕜] E (n + 1)) (f : ∀ n, E n →ₗ[𝕜] F)
  (hj : ∀ n, Topology.IsInducing (j n)) (hjinj : ∀ n, Injective (j n))
  (hf : ∀ n x, f (n + 1) (j n x) = f n x) (hfinj : ∀ n, Injective (f n))
  (hF : ∀ y : F, ∃ n x, f n x = y) (hjcl : ∀ n, IsClosed (range (j n)))
  (htop : tF = locallyConvexFinalTopology f)

include hj hjinj hf hfinj hF hjcl htop in
/-- Countable strict inductive limits of Hausdorff semi-reflexive locally convex spaces
with closed transition ranges are semi-reflexive. -/
theorem semiReflexiveSpace [∀ n, SemiReflexiveSpace 𝕜 (E n)] : SemiReflexiveSpace 𝕜 F := by
  let g (n : ℕ) : E n →L[𝕜] F :=
    ⟨f n, htop.symm ▸ locallyConvexFinalTopology.continuous_apply f n⟩
  apply SemiReflexiveSpace.of_bounded_cover g
  intro S hS
  obtain ⟨n, hn, hSn⟩ := exists_subset_range_and_isVonNBounded_preimage
    j f hj hjinj hf hfinj hF hjcl (htop ▸ hS)
  exact ⟨n, f n ⁻¹' S, hSn, fun y hy ↦ by
    obtain ⟨x, rfl⟩ := hn hy
    exact ⟨x, hy, rfl⟩⟩

include hj hjinj hf hfinj hF hjcl htop in
/-- Countable strict inductive limits of Hausdorff reflexive locally convex spaces with
closed transition ranges are reflexive. -/
theorem reflexiveSpace [∀ n, ReflexiveSpace 𝕜 (E n)] : ReflexiveSpace 𝕜 F := by
  let : IsTopologicalAddGroup F := htop.symm ▸ locallyConvexFinalTopology.isTopologicalAddGroup f
  let : LocallyConvexSpace ℝ F := htop.symm ▸ locallyConvexFinalTopology.locallyConvexSpace f
  let (n : ℕ) : BarrelledSpace 𝕜 (E n) :=
    (reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace.mp inferInstance).2
  exact reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace.mpr
    ⟨semiReflexiveSpace j f hj hjinj hf hfinj hF hjcl htop,
      htop.symm ▸ locallyConvexFinalTopology.barrelledSpace f⟩

omit [ContinuousSMul 𝕜 F] in
include hj hjinj hf hfinj hF hjcl htop in
/-- Countable strict inductive limits of Hausdorff Montel locally convex spaces with
closed transition ranges have the Montel property. -/
theorem montelSpace [∀ n, MontelSpace 𝕜 (E n)] : MontelSpace 𝕜 F := by
  let g (n : ℕ) : E n →L[𝕜] F :=
    ⟨f n, htop.symm ▸ locallyConvexFinalTopology.continuous_apply f n⟩
  apply MontelSpace.of_bounded_cover g
  intro S hS
  obtain ⟨n, hn, hSn⟩ := exists_subset_range_and_isVonNBounded_preimage
    j f hj hjinj hf hfinj hF hjcl (htop ▸ hS)
  exact ⟨n, f n ⁻¹' S, hSn, fun y hy ↦ by
    obtain ⟨x, rfl⟩ := hn hy
    exact ⟨x, hy, rfl⟩⟩

end StrictInductiveLimit

namespace SeminormFamily

variable {𝕜 E ι : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  (p : SeminormFamily 𝕜 E ι)

/-- The local-Banach projective limit is semi-reflexive if every factor is semi-reflexive. -/
theorem semiReflexiveSpace_projectiveLimit [∀ i, SemiReflexiveSpace 𝕜 (p i).Completion] :
    SemiReflexiveSpace 𝕜 p.projectiveLimit := by
  let (i : ι) : NormedSpace ℝ (p i).Completion := NormedSpace.restrictScalars ℝ 𝕜 _
  let (i : ι) : IsScalarTower ℝ 𝕜 (p i).Completion := IsScalarTower.restrictScalars ℝ 𝕜 _
  exact SemiReflexiveSpace.submodule p.projectiveLimit p.isClosed_projectiveLimit

/-- A projective limit with Montel local Banach factors has the Montel property. -/
theorem montelSpace_projectiveLimit [∀ i, MontelSpace 𝕜 (p i).Completion] :
    MontelSpace 𝕜 p.projectiveLimit :=
  MontelSpace.submodule p.projectiveLimit p.isClosed_projectiveLimit

end SeminormFamily
