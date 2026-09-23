/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.Bipolar
public import LocallyConvexSpaces.CompactHull
public import LocallyConvexSpaces.PolarTopology

/-!
# The dual of the topology of compact convergence

Let `E` be a quasi-complete locally convex space over `ℝ` or `ℂ`. Every linear functional on the
dual of `E` that is continuous for the topology of compact convergence is the evaluation at a point
of `E`. In the language of dual pairs, the topology of compact convergence on `E'` is compatible
with the pairing between `E'` and `E`; this is the part of the Mackey–Arens theorem that is needed
for the Krein–Šmulian theorem.

The proof is the classical one. A functional `Λ` that is continuous for compact convergence is
bounded by one on the polar `K°` of a compact set `K`, which may be taken convex and balanced
because `E` is quasi-complete
(`IsCompact.exists_isCompact_convex_balanced_superset_of_quasiCompleteSpace`). The image of `K`
in the algebraic dual `G` of `E'` is compact for the weak topology `σ(G, E')`, hence closed, and
it is convex and balanced. By the bipolar theorem for the pairing of `G` with `E'`
(`LinearMap.flip_polar_polar_eq_self`) it is its own bipolar, and `Λ` lies in that bipolar.

## Main statements

The lemmas ending in `_of_quasiCompleteSpace` give the quasi-complete versions of the following
complete-space corollaries.

* `CompactConvergenceCLM.exists_forall_apply_eq`: a continuous linear functional on
  `E →L_c[𝕜] 𝕜` is evaluation at a point of `E`.
* `CompactConvergenceCLM.exists_pos_le_re_apply`: a convex set of functionals that misses the
  polar of a compact set is separated from zero by a point of `E`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §3.2
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], IV §1.1

## Tags

compact convergence, Mackey–Arens, dual pair, bipolar
-/

public section

open Set Filter Metric

open scoped Topology CompactConvergenceCLM

namespace CompactConvergenceCLM

section Eval

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- Evaluation at a point, as a linear map from `E` to the algebraic dual of `E →L_c[𝕜] 𝕜`. -/
@[expose]
def evalₗ : E →ₗ[𝕜] (E →L_c[𝕜] 𝕜) →ₗ[𝕜] 𝕜 where
  toFun x := { toFun := fun f ↦ f x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  map_add' x y := by
    ext f
    exact map_add f x y
  map_smul' c x := by
    ext f
    exact map_smul f c x

/-- The evaluation map applied to a functional. -/
@[simp]
theorem evalₗ_apply (x : E) (f : E →L_c[𝕜] 𝕜) : evalₗ (𝕜 := 𝕜) x f = f x :=
  rfl

end Eval

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- Let `E` be a quasi-complete locally convex space. A linear functional on the dual of `E` that is
continuous for the topology of compact convergence is the evaluation at a point of `E`. -/
theorem exists_forall_apply_eq_of_quasiCompleteSpace [QuasiCompleteSpace 𝕜 E]
    (Λ : (E →L_c[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ∃ x : E, ∀ f : E →L_c[𝕜] 𝕜, Λ f = f x := by
  -- `Λ` is bounded by one on the polar of a compact set `K`.
  have hnhds : Λ ⁻¹' closedBall (0 : 𝕜) 1 ∈ 𝓝 (0 : E →L_c[𝕜] 𝕜) :=
    Λ.continuous.continuousAt.preimage_mem_nhds (by
      rw [map_zero]
      exact closedBall_mem_nhds 0 one_pos)
  obtain ⟨K₀, hK₀, hK₀Λ⟩ := (CompactConvergenceCLM.hasBasis_nhds_zero_polar).mem_iff.mp hnhds
  -- Enlarge `K` to a compact, convex, balanced set.
  obtain ⟨K, hK₀K, hK, hKc, hKb, hK0⟩ :=
    hK₀.exists_isCompact_convex_balanced_superset_of_quasiCompleteSpace (𝕜 := 𝕜)
  have hΛ (f : E →L_c[𝕜] 𝕜) (hf : ∀ x ∈ K, ‖f x‖ ≤ 1) : ‖Λ f‖ ≤ 1 := by
    have h := hK₀Λ (UniformConvergenceCLM.mem_polar.mpr fun x hx ↦ hf x (hK₀K hx))
    simpa using h
  -- The pairing of the algebraic dual of `E'` with `E'`, and the image of `K` in it.
  let P : ((E →L_c[𝕜] 𝕜) →ₗ[𝕜] 𝕜) →ₗ[𝕜] (E →L_c[𝕜] 𝕜) →ₗ[𝕜] 𝕜 := LinearMap.id
  let ι : E → WeakBilin P := fun x ↦ evalₗ (𝕜 := 𝕜) x
  have hι : Continuous ι :=
    WeakBilin.continuous_of_continuous_eval P fun f ↦ by
      change Continuous fun x ↦ f x
      exact ContinuousLinearMap.continuous f
  have hT2 : T2Space (WeakBilin P) :=
    (WeakBilin.isEmbedding (B := P) Function.injective_id).t2Space
  let T : Set (WeakBilin P) := ι '' K
  have hTcl : IsClosed T := (hK.image hι).isClosed
  have hTc : Convex ℝ T :=
    hKc.is_linear_image ((evalₗ (𝕜 := 𝕜) (E := E)).restrictScalars ℝ).isLinear
  have hTb : Balanced 𝕜 T := by
    rintro a ha _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, hKb a ha ⟨x, hx, rfl⟩, map_smul (evalₗ (𝕜 := 𝕜) (E := E)) a x⟩
  have hTne : T.Nonempty := ⟨ι 0, 0, hK0, rfl⟩
  -- `Λ` lies in the bipolar of `T`, which is `T`.
  have hmem : (Λ : (E →L_c[𝕜] 𝕜) →ₗ[𝕜] 𝕜) ∈ P.flip.polar (P.polar T) := by
    intro f hf
    exact hΛ f fun x hx ↦ hf (ι x) ⟨x, hx, rfl⟩
  rw [P.flip_polar_polar_eq_self hTc hTb hTcl hTne] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  exact ⟨x, fun f ↦ (LinearMap.congr_fun hx f).symm⟩

/-- Let `E` be a quasi-complete locally convex space, `S` a compact subset of `E` and `T` a convex
set of continuous linear functionals that does not meet the polar of `S`. Then `T` is separated from
zero by a point of `E`: there are `x : E` and `u > 0` with `u ≤ re (f x)` for all `f ∈ T`. -/
theorem exists_pos_le_re_apply_of_quasiCompleteSpace [QuasiCompleteSpace 𝕜 E] {S : Set E}
    (hS : IsCompact S) {T : Set (E →L_c[𝕜] 𝕜)}
    (hT : Convex ℝ T)
    (hdisj : Disjoint (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S} S) T) :
    ∃ x : E, ∃ u : ℝ, 0 < u ∧ ∀ f ∈ T, u ≤ RCLike.re (f x) := by
  let s : Set (E →L_c[𝕜] 𝕜) :=
    interior (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S} S)
  have hs0 : (0 : E →L_c[𝕜] 𝕜) ∈ s :=
    mem_interior_iff_mem_nhds.mpr
      (CompactConvergenceCLM.hasBasis_nhds_zero_polar.mem_of_mem hS)
  have hpc : Convex ℝ (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S} S) :=
    UniformConvergenceCLM.convex_polar S
  have hsc : Convex ℝ s := hpc.interior
  obtain ⟨Λ, u, hΛs, hΛt⟩ := RCLike.geometric_hahn_banach_open (𝕜 := 𝕜) hsc isOpen_interior hT
    (hdisj.mono_left interior_subset)
  obtain ⟨x, hx⟩ := exists_forall_apply_eq_of_quasiCompleteSpace Λ
  refine ⟨x, u, by simpa using hΛs 0 hs0, fun f hf ↦ ?_⟩
  rw [← hx]
  exact hΛt f hf

/-- A functional continuous for compact convergence on the dual of a complete locally convex
space is evaluation at a point of the original space. -/
theorem exists_forall_apply_eq [CompleteSpace E] (Λ : (E →L_c[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ∃ x : E, ∀ f : E →L_c[𝕜] 𝕜, Λ f = f x :=
  exists_forall_apply_eq_of_quasiCompleteSpace Λ

/-- In a complete locally convex space, a convex set of functionals missing the polar of a
compact set is separated from zero by evaluation at a point. -/
theorem exists_pos_le_re_apply [CompleteSpace E] {S : Set E} (hS : IsCompact S)
    {T : Set (E →L_c[𝕜] 𝕜)} (hT : Convex ℝ T)
    (hdisj : Disjoint (UniformConvergenceCLM.polar 𝕜 {S : Set E | IsCompact S} S) T) :
    ∃ x : E, ∃ u : ℝ, 0 < u ∧ ∀ f ∈ T, u ≤ RCLike.re (f x) :=
  exists_pos_le_re_apply_of_quasiCompleteSpace hS hT hdisj

end CompactConvergenceCLM
