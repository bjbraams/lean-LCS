/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.FinalTopology
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The finest locally convex topology on finitely supported families

`Finsupp.finestLocallyConvexTopology 𝕜 ι` is the final locally convex topology for the
coordinate injections into `ι →₀ 𝕜`, over a real or complex scalar field. Every linear map
from this space to a locally convex space is continuous. The topology is Hausdorff, and for
infinite `ι` it has no countable neighbourhood basis at zero. For countably infinite `ι`
this is the classical space `φ`.

Its webbed-space instance and De Wilde applications are in `WebbedSpaces.DeWilde.Codimension`.

## Main statements

* `Finsupp.finestLocallyConvexTopology.continuous_linearMap`
* `Finsupp.finestLocallyConvexTopology.t2Space`
* `Finsupp.finestLocallyConvexTopology.not_isCountablyGenerated_nhds_zero`

## References

* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §35.5.(3).
-/

public section

open Set Filter Function
open scoped Topology

section Finsupp

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*)

/-- The finest locally convex topology on the space `ι →₀ 𝕜` of finitely supported families: the
final locally convex topology for the coordinate injections. For countably infinite `ι` this is the
space `φ` of Köthe. -/
@[expose, instance_reducible]
noncomputable def Finsupp.finestLocallyConvexTopology : TopologicalSpace (ι →₀ 𝕜) :=
  locallyConvexFinalTopology fun i : ι ↦ (Finsupp.lsingle i : 𝕜 →ₗ[𝕜] ι →₀ 𝕜)

namespace Finsupp.finestLocallyConvexTopology

variable {𝕜 ι}

/-- A linear map from `ι →₀ 𝕜` with its finest locally convex topology into a locally convex
space is continuous. -/
theorem continuous_linearMap {G : Type*} [AddCommGroup G] [Module 𝕜 G] [Module ℝ G]
    [IsScalarTower ℝ 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
    [LocallyConvexSpace ℝ G] (g : (ι →₀ 𝕜) →ₗ[𝕜] G) :
    @Continuous (ι →₀ 𝕜) G (Finsupp.finestLocallyConvexTopology 𝕜 ι) _ g := by
  refine (locallyConvexFinalTopology.continuous_iff _ g).mpr fun i ↦ ?_
  -- A linear map from `𝕜` is `c ↦ c • g (single i 1)`.
  have h : (g ∘ (Finsupp.lsingle i : 𝕜 →ₗ[𝕜] ι →₀ 𝕜)) =
      fun c : 𝕜 ↦ c • g (Finsupp.single i 1) := by
    funext c
    rw [Function.comp_apply, Finsupp.lsingle_apply, ← map_smul, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  rw [h]
  exact continuous_id.smul continuous_const

/-- The finest locally convex topology on `ι →₀ 𝕜` is Hausdorff. -/
theorem t2Space : @T2Space (ι →₀ 𝕜) (Finsupp.finestLocallyConvexTopology 𝕜 ι) := by
  let _ : TopologicalSpace (ι →₀ 𝕜) := Finsupp.finestLocallyConvexTopology 𝕜 ι
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra hcon
    push Not at hcon
    exact hxy (Finsupp.ext hcon)
  exact separated_by_continuous (continuous_linearMap (Finsupp.lapply i : (ι →₀ 𝕜) →ₗ[𝕜] 𝕜)) hi

/-- For infinite `ι` the finest locally convex topology on `ι →₀ 𝕜` has no countable basis of
neighbourhoods of zero; in particular Köthe's space `φ` is not metrizable. -/
theorem not_isCountablyGenerated_nhds_zero [Infinite ι] :
    ¬(@nhds (ι →₀ 𝕜) (Finsupp.finestLocallyConvexTopology 𝕜 ι) 0).IsCountablyGenerated := by
  classical
  let f := fun i : ι ↦ (Finsupp.lsingle i : 𝕜 →ₗ[𝕜] ι →₀ 𝕜)
  let _ : TopologicalSpace (ι →₀ 𝕜) := Finsupp.finestLocallyConvexTopology 𝕜 ι
  intro hcg
  obtain ⟨U, hU⟩ := (𝓝 (0 : ι →₀ 𝕜)).exists_antitone_basis
  let e : ℕ ↪ ι := Infinite.natEmbedding ι
  -- A positive multiple of the `n`-th unit vector in `U n`.
  have ht (n : ℕ) : ∃ t : ℝ, 0 < t ∧ Finsupp.single (e n) (t : 𝕜) ∈ U n := by
    have hc : Continuous (f (e n)) := locallyConvexFinalTopology.continuous_apply f (e n)
    have hpre : f (e n) ⁻¹' U n ∈ 𝓝 (0 : 𝕜) :=
      hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU.mem n)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hmem : ((r / 2 : ℝ) : 𝕜) ∈ Metric.ball (0 : 𝕜) r := by
      rw [mem_ball_zero_iff, RCLike.norm_ofReal, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    exact ⟨r / 2, half_pos hr, hball hmem⟩
  choose t htpos htU using ht
  -- A linear functional with the value two at each of these multiples.
  let a : ι → 𝕜 := Function.extend e (fun n ↦ ((2 / t n : ℝ) : 𝕜)) 0
  let φ : (ι →₀ 𝕜) →ₗ[𝕜] 𝕜 := Finsupp.linearCombination 𝕜 a
  have hφ : Continuous φ := continuous_linearMap φ
  have hval (n : ℕ) : φ (Finsupp.single (e n) (t n : 𝕜)) = 2 := by
    have ha : a (e n) = ((2 / t n : ℝ) : 𝕜) := e.injective.extend_apply _ _ n
    have h2 : t n * (2 / t n) = 2 := by
      have := (htpos n).ne'
      field_simp
    rw [Finsupp.linearCombination_single, ha, smul_eq_mul, ← RCLike.ofReal_mul, h2]
    norm_cast
  have hnhds : {c : ι →₀ 𝕜 | ‖φ c‖ < 1} ∈ 𝓝 (0 : ι →₀ 𝕜) := by
    have hc : ContinuousAt (fun c ↦ ‖φ c‖) 0 := (continuous_norm.comp hφ).continuousAt
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨n, -, hn⟩ := hU.toHasBasis.mem_iff.mp hnhds
  have h : ‖φ (Finsupp.single (e n) (t n : 𝕜))‖ < 1 := hn (htU n)
  rw [hval] at h
  norm_num at h

end Finsupp.finestLocallyConvexTopology

end Finsupp
