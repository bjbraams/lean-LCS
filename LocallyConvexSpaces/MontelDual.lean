/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.QuasiBarrelled
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The strong dual of a Montel space

Polars of zero-neighbourhoods in a Hausdorff Montel space are strongly compact. Indeed,
Alaoglu–Bourbaki gives weak-* compactness, Arzelà–Ascoli identifies pointwise and compact
convergence on an equicontinuous family, and the Montel property identifies compact and strong
convergence. Consequently the strong dual of a quasi-barrelled Montel space is Montel.

Mathlib's Montel convention does not include barrelledness. The explicit quasi-barrelledness
assumption supplies equicontinuity of strongly bounded sets.

## Main statements

* `StrongDual.isCompact_polar_of_montelSpace`: polars of zero-neighbourhoods are strongly
  compact.
* `MontelSpace.strongDual`: the strong dual of a quasi-barrelled Montel space is Montel.
* `MontelSpace.barrelledSpace_strongDual`: the strong dual of a locally convex Montel space is
  barrelled.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5.9
-/

public section

open Set Function Bornology
open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [T2Space E] [MontelSpace 𝕜 E]

/-- In a Hausdorff Montel space the polar of a zero-neighbourhood is strongly compact. -/
theorem StrongDual.isCompact_polar_of_montelSpace {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (StrongDual.polar 𝕜 U) := by
  let K := StrongDual.polar 𝕜 U
  let F : K → E → 𝕜 := fun φ ↦ φ.val
  let e := ContinuousLinearEquiv.toCompactConvergenceCLM (RingHom.id 𝕜) E 𝕜
  have hind : Topology.IsInducing (UniformOnFun.ofFun {S : Set E | IsCompact S} ∘ F) :=
    (UniformConvergenceCLM.isEmbedding_coeFn (RingHom.id 𝕜) 𝕜
      {S : Set E | IsCompact S}).isInducing.comp
        (e.toHomeomorph.isInducing.comp Topology.IsInducing.subtypeVal)
  have hcover : ⋃₀ {S : Set E | IsCompact S} = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton
  have hpoint : Topology.IsInducing F :=
    (EquicontinuousOn.isInducing_uniformOnFun_iff_pi hcover (fun _ h ↦ h)
      (fun S _ ↦ (StrongDual.equicontinuous_polar hU).equicontinuousOn S)).mp hind
  rw [isCompact_iff_isCompact_univ]
  apply hpoint.isCompact_iff.mpr
  have hweak := (WeakDual.isCompact_polar_of_mem_nhds hU).image
    (show Continuous ((↑) : WeakDual 𝕜 E → E → 𝕜) from continuous_pi
      fun x ↦ WeakDual.eval_continuous x)
  convert hweak using 1
  ext f
  simp only [image_univ, mem_range, mem_image]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨StrongDual.toWeakDual φ.val, φ.property, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨⟨WeakDual.toStrongDual φ, hφ⟩, rfl⟩

/-- The strong dual of a quasi-barrelled Hausdorff Montel space is Montel.
For barrelled Montel spaces this is Schaefer–Wolff IV, Theorem 5.9; the proof
uses Mathlib's Arzelà–Ascoli theorem and the Alaoglu–Bourbaki theorem. -/
theorem MontelSpace.strongDual [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [QuasiBarrelledSpace 𝕜 E] : MontelSpace 𝕜 (StrongDual 𝕜 E) := by
  constructor
  intro H hclosed hbounded
  obtain ⟨U, hU, hHU⟩ := StrongDual.exists_mem_nhds_subset_polar
    (QuasiBarrelledSpace.equicontinuous_of_isVonNBounded hbounded)
  exact (StrongDual.isCompact_polar_of_montelSpace hU).of_isClosed_subset hclosed hHU

/-- The strong dual of a Hausdorff Montel locally convex space is barrelled.
This follows from semi-reflexivity, even without barrelledness of the original space. -/
theorem MontelSpace.barrelledSpace_strongDual [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [LocallyConvexSpace ℝ E] : BarrelledSpace 𝕜 (StrongDual 𝕜 E) := by
  let : SemiReflexiveSpace 𝕜 E := MontelSpace.semiReflexiveSpace
  exact SemiReflexiveSpace.barrelledSpace_strongDual
