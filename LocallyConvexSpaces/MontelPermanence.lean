/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Montel

/-!
# Permanence of the Heine–Borel property

Mathlib's `MontelSpace` means that closed von Neumann bounded sets are compact; it does not
include barrelledness. This property passes to closed subspaces, arbitrary products, and
continuous linear images when bounded sets lift up to closure. In particular it is preserved by
continuous linear equivalences and retractions. Families of maps whose bounded images cover all
bounded sets of the target also transfer the Montel property.

These proofs work over any normed field and use compactness and boundedness directly, without
local convexity. Retraction inheritance uses the closed embedding defined by a continuous
section and needs only Hausdorffness of the source.

## Main statements

* `MontelSpace.of_isClosedEmbedding`, `MontelSpace.submodule`: closed subspaces.
* `MontelSpace.of_continuousLinearEquiv`, `MontelSpace.of_rightInverse`: isomorphic spaces and
  retracts.
* `MontelSpace.of_bounded_lifting`: images under maps that lift bounded sets up to closure.
* `MontelSpace.pi`: arbitrary products.
* `MontelSpace.of_bounded_cover`: families of maps that cover the bounded sets of the target.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.8
-/

public section

open Set Function Bornology

namespace MontelSpace

section Permanence

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A closed linear embedding into a Montel space transfers the Heine–Borel property. -/
theorem of_isClosedEmbedding [MontelSpace 𝕜 F] (f : E →L[𝕜] F)
    (hf : Topology.IsClosedEmbedding f) : MontelSpace 𝕜 E := by
  constructor
  intro S hS hSb
  exact hf.isEmbedding.isCompact_iff.mpr
    (isCompact_of_isClosed_of_isVonNBounded 𝕜 (hf.isClosedMap S hS) (hSb.image f))

/-- Closed subspaces inherit Mathlib's Montel property, without a barrelledness assumption. -/
theorem submodule [MontelSpace 𝕜 E] (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) :
    MontelSpace 𝕜 M :=
  of_isClosedEmbedding M.subtypeL hM.isClosedEmbedding_subtypeVal

/-- Continuous linear equivalences preserve the Montel property. -/
theorem of_continuousLinearEquiv [MontelSpace 𝕜 E] (e : E ≃L[𝕜] F) : MontelSpace 𝕜 F :=
  of_isClosedEmbedding e.symm.toContinuousLinearMap e.symm.toHomeomorph.isClosedEmbedding

/-- A bounded-lifting image of a Montel space is Montel. Lifting up to closure suffices. -/
theorem of_bounded_lifting [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [MontelSpace 𝕜 E] [T2Space E] [T2Space F] (f : E →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ B : Set E, IsVonNBounded 𝕜 B ∧ S ⊆ closure (f '' B)) : MontelSpace 𝕜 F := by
  constructor
  intro S hS hSb
  obtain ⟨B, hB, hSB⟩ := h S hSb
  have hK := (isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure hB.closure).image
    f.continuous
  exact hK.of_isClosed_subset hS (hSB.trans (closure_minimal
    (image_mono subset_closure) hK.isClosed))

/-- Continuous linear retracts of Hausdorff Montel spaces are Montel. -/
theorem of_rightInverse [MontelSpace 𝕜 E] [T2Space E]
    (f : E →L[𝕜] F) (s : F →L[𝕜] E) (h : RightInverse s f) : MontelSpace 𝕜 F :=
  of_isClosedEmbedding s (h.isClosedEmbedding f.continuous s.continuous)

/-- Arbitrary products of Montel spaces have the Heine–Borel property. -/
instance pi {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Module 𝕜 (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)] [∀ i, ContinuousSMul 𝕜 (G i)]
    [∀ i, MontelSpace 𝕜 (G i)] [∀ i, T2Space (G i)] : MontelSpace 𝕜 (∀ i, G i) := by
  constructor
  intro S hS hSb
  have hK : ∀ i, IsCompact (closure (eval i '' S)) := fun i ↦
    isCompact_of_isClosed_of_isVonNBounded 𝕜 isClosed_closure
      ((isVonNBounded_pi_iff.mp hSb i).closure)
  exact (isCompact_pi_infinite hK).of_isClosed_subset hS (by
    intro x hx
    change ∀ i, x i ∈ closure (eval i '' S)
    intro i
    exact subset_closure ⟨x, hx, rfl⟩)

end Permanence

section BoundedCover

variable {𝕜 ι F : Type*} [NormedField 𝕜] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  [∀ i, T2Space (E i)] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The Montel property passes through a family whose bounded images cover target bounded sets. -/
theorem of_bounded_cover [∀ i, MontelSpace 𝕜 (E i)]
    (f : ∀ i, E i →L[𝕜] F)
    (h : ∀ S : Set F, IsVonNBounded 𝕜 S →
      ∃ i, ∃ B : Set (E i), IsVonNBounded 𝕜 B ∧ S ⊆ f i '' B) : MontelSpace 𝕜 F := by
  constructor
  intro S hS hSb
  obtain ⟨i, B, hB, hSB⟩ := h S hSb
  have hK := (MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜
    isClosed_closure hB.closure).image (f i).continuous
  exact hK.of_isClosed_subset hS (hSB.trans (image_mono subset_closure))

end BoundedCover

end MontelSpace
