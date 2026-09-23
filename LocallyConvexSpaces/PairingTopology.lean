/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.PolarTopology
public import Mathlib.Analysis.LocallyConvex.StrongTopology
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
public import TopologicalGroups.Basic

/-!
# Polar topologies for a pairing

Let `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` be a bilinear pairing and `𝔖` a family of subsets of `F`. The *polar
topology* or *`𝔖`-topology* on `E` is the topology of uniform convergence on the members of `𝔖`,
where a point `x` of `E` is regarded as the function `y ↦ B x y` on `F`. If `𝔖` is nonempty,
directed and stable under nonzero scalar multiples, the polars `{x | ∀ y ∈ S, ‖B x y‖ ≤ 1}` of the
members of `𝔖` form a basis of neighbourhoods of zero.

The topology is defined as the topology induced on `E` by the linear map `x ↦ B x ·` into Mathlib's
space `WeakBilin B.flip →Lᵤ[𝕜, 𝔖] 𝕜` of continuous linear functionals on `F` with the weak topology
`σ(F, E)`, with the topology of `𝔖`-convergence. It is a term and not an instance, like
`locallyConvexFinalTopology`. The family `𝔖` consists of subsets of `WeakBilin B.flip`, which is `F`
with the weak topology, so that weak boundedness and weak compactness of its members can be
expressed.

## Main definitions

* `LinearMap.toUniformConvergenceCLM B 𝔖`: the linear map `x ↦ B x ·`.
* `LinearMap.polarTopology B 𝔖`: the `𝔖`-topology on `E`.
* `LinearMap.polarUniformSpace B 𝔖`: the compatible uniform structure of `𝔖`-convergence.

## Main statements

* `LinearMap.polarTopology.isTopologicalAddGroup`, `.continuousSMul`, `.locallyConvexSpace`.
* `LinearMap.polarTopology.hasBasis_nhds_zero`: the basis of polars.
* `LinearMap.polarTopology_antitone`: a larger family gives a finer topology.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §3, IV §1.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §3.1, IV §1.1
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §21.1

## Tags

polar topology, pairing, uniform convergence, locally convex space
-/

public section

open Set Filter Bornology

open scoped Topology Pointwise UniformConvergenceCLM

namespace LinearMap

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip)))

/-- The linear map that sends `x : E` to the functional `y ↦ B x y` on `F` with the weak topology
`σ(F, E)`, as an element of the space of continuous linear functionals with the topology of
uniform convergence on the members of `𝔖`. -/
@[expose]
noncomputable def toUniformConvergenceCLM : E →ₗ[𝕜] (WeakBilin B.flip →Lᵤ[𝕜, 𝔖] 𝕜) where
  toFun x := WeakBilin.eval B.flip x
  map_add' x y := map_add (WeakBilin.eval B.flip) x y
  map_smul' c x := map_smul (WeakBilin.eval B.flip) c x

/-- The functional attached to `x` is `y ↦ B x y`. -/
@[simp]
theorem toUniformConvergenceCLM_apply (x : E) (y : WeakBilin B.flip) :
    B.toUniformConvergenceCLM 𝔖 x y = B x y :=
  rfl

/-- The **polar topology** on `E` for the pairing `B` and a family `𝔖` of subsets of `F`: the
topology of uniform convergence on the members of `𝔖`. -/
@[expose, instance_reducible]
noncomputable def polarTopology : TopologicalSpace E :=
  TopologicalSpace.induced (B.toUniformConvergenceCLM 𝔖) inferInstance

/-- The uniform structure of convergence on the members of a family for a bilinear pairing.
Its topology is `LinearMap.polarTopology`. Like that topology, it is a term rather than a
global instance. -/
@[expose, instance_reducible]
noncomputable def polarUniformSpace : UniformSpace E :=
  UniformSpace.comap (B.toUniformConvergenceCLM 𝔖) inferInstance

/-- The polar uniform structure induces the polar topology. -/
@[simp]
theorem polarUniformSpace_toTopologicalSpace :
    (B.polarUniformSpace 𝔖).toTopologicalSpace = B.polarTopology 𝔖 :=
  rfl

/-- Evaluation into the continuous dual with uniform convergence on the family is
uniformly inducing for the polar uniform structure. -/
theorem isUniformInducing_toUniformConvergenceCLM :
    @IsUniformInducing E _ (B.polarUniformSpace 𝔖) _ (B.toUniformConvergenceCLM 𝔖) :=
  @IsUniformInducing.mk E _ (B.polarUniformSpace 𝔖) _ _ rfl

namespace polarTopology

/-- The map `x ↦ B x ·` is inducing for the polar topology. -/
theorem isInducing :
    @Topology.IsInducing E _ (B.polarTopology 𝔖) _ (B.toUniformConvergenceCLM 𝔖) :=
  @Topology.IsInducing.mk E _ (B.polarTopology 𝔖) _ _ rfl

/-- A polar topology is a group topology. -/
theorem isTopologicalAddGroup : @IsTopologicalAddGroup E (B.polarTopology 𝔖) _ :=
  isTopologicalAddGroup_induced (B.toUniformConvergenceCLM 𝔖)

/-- Scalar multiplication is continuous for the polar topology of a family of weakly bounded
sets. -/
theorem continuousSMul (h𝔖 : ∀ S ∈ 𝔖, IsVonNBounded 𝕜 S) :
    @ContinuousSMul 𝕜 E _ _ (B.polarTopology 𝔖) := by
  have := UniformConvergenceCLM.continuousSMul (RingHom.id 𝕜) 𝕜 𝔖 h𝔖
  exact continuousSMul_induced (B.toUniformConvergenceCLM 𝔖)

/-- If `𝔖` is directed and stable under multiplication by nonzero scalars, then the polars of the
members of `𝔖` form a basis of neighbourhoods of zero for the polar topology. -/
theorem hasBasis_nhds_zero (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖)
    (h𝔖₃ : ∀ S ∈ 𝔖, ∀ c : 𝕜, c ≠ 0 → c • S ∈ 𝔖) :
    (@nhds E (B.polarTopology 𝔖) 0).HasBasis (· ∈ 𝔖) fun S ↦ B.flip.polar S := by
  rw [polarTopology, nhds_induced, map_zero]
  exact (UniformConvergenceCLM.hasBasis_nhds_zero_polar h𝔖₁ h𝔖₂ h𝔖₃).comap _

/-- The polar of a member of a directed family `𝔖` is a neighbourhood of zero for the polar
topology. -/
theorem polar_mem_nhds_zero (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖)
    {S : Set (WeakBilin B.flip)} (hS : S ∈ 𝔖) :
    B.flip.polar S ∈ @nhds E (B.polarTopology 𝔖) 0 := by
  rw [polarTopology, nhds_induced, map_zero]
  exact preimage_mem_comap (UniformConvergenceCLM.polar_mem_nhds_zero h𝔖₁ h𝔖₂ hS)

end polarTopology

/-- Polar topology is antitone in the family of sets, for Mathlib's order on topologies. -/
theorem polarTopology_antitone : Antitone B.polarTopology := fun _ _ h ↦
  induced_mono (UniformConvergenceCLM.topologicalSpace_mono (RingHom.id 𝕜) 𝕜 h)

end General

section LocallyConvex

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip)))

/-- The polar topology of a nonempty directed family is locally convex. -/
theorem polarTopology.locallyConvexSpace (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    @LocallyConvexSpace ℝ E _ _ _ _ (B.polarTopology 𝔖) := by
  have := UniformConvergenceCLM.locallyConvexSpace ℝ (σ := RingHom.id 𝕜) (F := 𝕜) 𝔖 h𝔖₁ h𝔖₂
  exact LocallyConvexSpace.induced ((B.toUniformConvergenceCLM 𝔖).restrictScalars ℝ)

end LocallyConvex

end LinearMap
