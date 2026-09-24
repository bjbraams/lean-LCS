/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TopologicalVectorSpaces.Basic

/-!
# Polar topologies on the dual

Let `E` be a topological vector space over a nontrivially normed field `𝕜` and let `𝔖` be a family
of subsets of `E`. Mathlib equips the continuous dual with the topology of uniform convergence on
the members of `𝔖` through the type synonym `E →Lᵤ[𝕜, 𝔖] 𝕜` (`UniformConvergenceCLM`). In the
literature this is the *polar topology* or `𝔖`-topology: if `𝔖` is nonempty, directed and stable
under multiplication by nonzero scalars, the polars of the members of `𝔖` form a basis of
neighbourhoods of zero. This file proves that description and specializes it to the topology of
bounded convergence (the strong dual, which is the topology carried by `StrongDual 𝕜 E`) and to the
topology of compact convergence (`E →L_c[𝕜] 𝕜`).

## Main definitions

* `UniformConvergenceCLM.polar 𝕜 𝔖 S`: the polar of `S : Set E`, as a subset of `E →Lᵤ[𝕜, 𝔖] 𝕜`.

## Main statements

* `UniformConvergenceCLM.polar_mem_nhds_zero`: the polar of a member of `𝔖` is a neighbourhood
  of zero for the `𝔖`-topology.
* `UniformConvergenceCLM.hasBasis_nhds_zero_polar`: the polars of the members of `𝔖` form a
  basis of neighbourhoods of zero.
* `UniformConvergenceCLM.convex_polar`: polars are `ℝ`-convex.
* `StrongDual.hasBasis_nhds_zero_polar`: in the strong dual the polars of the von Neumann
  bounded sets form a basis of neighbourhoods of zero.
* `CompactConvergenceCLM.hasBasis_nhds_zero_polar`: for the topology of compact convergence the
  polars of the compact sets form a basis of neighbourhoods of zero.

## Implementation notes

Only polar topologies on the dual `E'` of a topological vector space are treated, because that
is where Mathlib's `UniformConvergenceCLM` lives. Polar topologies on `E` for a general dual
pairing `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` (needed for the Mackey topology) are treated in
`LocallyConvexSpaces.PairingTopology`.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], III §3.1 and IV §1.2
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §3 and IV §1

## Tags

polar topology, uniform convergence, strong dual, compact convergence
-/

public section

open Set Filter Bornology Metric

open scoped Topology Pointwise UniformConvergenceCLM CompactConvergenceCLM

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

namespace UniformConvergenceCLM

variable (𝕜) (𝔖 : Set (Set E))

/-- The polar of a subset `S` of `E`, as a subset of the dual with the `𝔖`-topology. -/
@[expose]
def polar (S : Set E) : Set (E →Lᵤ[𝕜, 𝔖] 𝕜) :=
  {f | ∀ x ∈ S, ‖f x‖ ≤ 1}

variable {𝕜 𝔖}

/-- Membership of the polar of a set in the dual with a topology of uniform convergence. -/
@[simp]
theorem mem_polar {S : Set E} {f : E →Lᵤ[𝕜, 𝔖] 𝕜} : f ∈ polar 𝕜 𝔖 S ↔ ∀ x ∈ S, ‖f x‖ ≤ 1 :=
  Iff.rfl

/-- The sets of functionals that are bounded by `ε` on a member of `𝔖` form a basis of
neighbourhoods of zero for the `𝔖`-topology. -/
theorem hasBasis_nhds_zero_norm_le (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 (0 : E →Lᵤ[𝕜, 𝔖] 𝕜)).HasBasis (fun Sε : Set E × ℝ ↦ Sε.1 ∈ 𝔖 ∧ 0 < Sε.2)
      fun Sε ↦ {f : E →Lᵤ[𝕜, 𝔖] 𝕜 | ∀ x ∈ Sε.1, ‖f x‖ ≤ Sε.2} := by
  convert hasBasis_nhds_zero_of_basis (RingHom.id 𝕜) 𝕜 𝔖 h𝔖₁ h𝔖₂
    (Metric.nhds_basis_closedBall (x := (0 : 𝕜))) using 4
  simp

/-- The polar of a member of `𝔖` is a neighbourhood of zero for the `𝔖`-topology. -/
theorem polar_mem_nhds_zero (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {S : Set E}
    (hS : S ∈ 𝔖) : polar 𝕜 𝔖 S ∈ 𝓝 (0 : E →Lᵤ[𝕜, 𝔖] 𝕜) :=
  (hasBasis_nhds_zero_norm_le h𝔖₁ h𝔖₂).mem_of_mem (i := (S, 1)) ⟨hS, one_pos⟩

/-- If `𝔖` is nonempty, directed and stable under multiplication by nonzero scalars, then the polars
of the members of `𝔖` form a basis of neighbourhoods of zero for the `𝔖`-topology. -/
theorem hasBasis_nhds_zero_polar (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖)
    (h𝔖₃ : ∀ S ∈ 𝔖, ∀ c : 𝕜, c ≠ 0 → c • S ∈ 𝔖) :
    (𝓝 (0 : E →Lᵤ[𝕜, 𝔖] 𝕜)).HasBasis (· ∈ 𝔖) (polar 𝕜 𝔖) := by
  refine (hasBasis_nhds_zero_norm_le h𝔖₁ h𝔖₂).to_hasBasis ?_
    fun S hS ↦ ⟨(S, 1), ⟨hS, one_pos⟩, Subset.rfl⟩
  rintro ⟨S, ε⟩ ⟨hS, hε⟩
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ε⁻¹
  have hc0 : 0 < ‖c‖ := (inv_pos.2 hε).trans hc
  refine ⟨c • S, h𝔖₃ S hS c (norm_pos_iff.mp hc0), fun f hf x hx ↦ ?_⟩
  have h := hf (c • x) (smul_mem_smul_set hx)
  rw [map_smul, norm_smul] at h
  calc ‖f x‖ ≤ ‖c‖⁻¹ := by rwa [← one_div, le_div_iff₀ hc0, mul_comm]
    _ ≤ ε := inv_le_of_inv_le₀ hε hc.le

/-- Polars are `ℝ`-convex, as subsets of the dual with the `𝔖`-topology. -/
theorem convex_polar {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {𝔖 : Set (Set E)} (S : Set E) : Convex ℝ (polar 𝕜 𝔖 S) := by
  intro f hf g hg a b ha hb hab x hx
  change ‖a • f x + b • g x‖ ≤ 1
  calc ‖a • f x + b • g x‖ ≤ ‖a • f x‖ + ‖b • g x‖ := norm_add_le _ _
    _ = a * ‖f x‖ + b * ‖g x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by
      gcongr
      · exact hf x hx
      · exact hg x hx
    _ = 1 := by rw [mul_one, mul_one, hab]

end UniformConvergenceCLM

/-- In the strong dual of a topological vector space the polars of the von Neumann bounded sets
form a basis of neighbourhoods of zero. -/
theorem StrongDual.hasBasis_nhds_zero_polar [ContinuousConstSMul 𝕜 E] :
    (𝓝 (0 : StrongDual 𝕜 E)).HasBasis (IsVonNBounded 𝕜) (StrongDual.polar 𝕜) :=
  UniformConvergenceCLM.hasBasis_nhds_zero_polar (𝕜 := 𝕜) (𝔖 := {S : Set E | IsVonNBounded 𝕜 S})
    ⟨∅, isVonNBounded_empty 𝕜 E⟩ (directedOn_of_sup_mem fun _ _ ↦ IsVonNBounded.union)
    fun _ hS c _ ↦ hS.smul_set c

/-- For the topology of compact convergence on the dual of a topological vector space the polars
of the compact sets form a basis of neighbourhoods of zero. -/
theorem CompactConvergenceCLM.hasBasis_nhds_zero_polar [ContinuousConstSMul 𝕜 E] :
    (𝓝 (0 : E →L_c[𝕜] 𝕜)).HasBasis (fun S : Set E ↦ IsCompact S)
      (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S}) :=
  UniformConvergenceCLM.hasBasis_nhds_zero_polar ⟨∅, isCompact_empty⟩
    (directedOn_of_sup_mem fun _ _ ↦ IsCompact.union) fun _ hS c _ ↦ hS.smul c
