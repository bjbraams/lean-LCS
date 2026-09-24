/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.GrothendieckApproximation
public import LocallyConvexSpaces.PairingTopology
public import MathlibExtras.Topology.UniformConvergence

/-!
# Grothendieck's criterion for completeness of a dual

For uniform convergence on a covering directed family with cofinally many closed `ℝ`-convex
balanced members, completeness of the continuous dual is equivalent to continuity of every
linear form whose restriction to each member is continuous. Saturated covering families of
bounded sets satisfy these hypotheses. Boundedness and closure under scalar multiples are
unnecessary for the completeness equivalence itself.

The approximation lemma imported from `LocallyConvexSpaces.GrothendieckApproximation` uses
separation of the graph of a linear form restricted to a closed `ℝ`-convex balanced set. The
notation `E →Lᵤ[𝕜, 𝔖] 𝕜` denotes Mathlib's continuous dual with uniform convergence on the members
of `𝔖`; `E →ᵤ[𝔖] 𝕜` denotes all functions with the same convergence. The dual-pair formulation
uses `LinearMap.polarUniformSpace` and expresses completeness as representation of forms which are
weakly continuous on the family.

## Main statements

* `UniformConvergenceCLM.completeSpace_of_forall_continuousOn`: the sufficiency direction,
  requiring only a complete nontrivially normed scalar field and a covering family.
* `UniformConvergenceCLM.completeSpace_iff_forall_continuousOn`: the general criterion for
  real or complex locally convex spaces, with explicit family hypotheses.
* `LinearMap.completeSpace_polarUniformSpace_iff`: the representation criterion for a pairing,
  without separation assumptions.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §3 and IV §6.2.
-/

public noncomputable section

open Set Filter Function Bornology
open scoped Topology Pointwise Uniformity UniformConvergence UniformConvergenceCLM

namespace UniformConvergenceCLM

section General

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] {𝔖 : Set (Set E)}

/-- A limit, for uniform convergence on a family, of continuous linear forms is
continuous on each member of the family. -/
theorem continuousOn_of_mem_closure_range_coeFn
    {f : E →ᵤ[𝔖] 𝕜}
    (hf : f ∈ closure (range (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe :
      (E →Lᵤ[𝕜, 𝔖] 𝕜) → E →ᵤ[𝔖] 𝕜))) {S : Set E} (hS : S ∈ 𝔖) :
    ContinuousOn (UniformOnFun.toFun 𝔖 f) S := by
  apply closure_minimal (t := {f : E →ᵤ[𝔖] 𝕜 | ContinuousOn (UniformOnFun.toFun 𝔖 f) S})
    ?_ (UniformOnFun.isClosed_setOf_continuousOn hS) hf
  rintro _ ⟨g, rfl⟩
  exact g.continuous.continuousOn

/-- Uniform convergence on a covering family makes the continuous dual complete if
continuity on the members of the family detects continuity of linear forms. This direction
requires neither local convexity nor a saturation condition on the family. -/
theorem completeSpace_of_forall_continuousOn [CompleteSpace 𝕜] (h𝔖cover : ⋃₀ 𝔖 = univ)
    (h : ∀ f : E →ₗ[𝕜] 𝕜, (∀ S ∈ 𝔖, ContinuousOn f S) → Continuous f) :
    CompleteSpace (E →Lᵤ[𝕜, 𝔖] 𝕜) := by
  rw [completeSpace_iff_isComplete_range (isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 𝔖)]
  apply IsClosed.isComplete
  apply isClosed_of_closure_subset
  intro f hf
  have hlin : UniformOnFun.toFun 𝔖 f ∈ range (DFunLike.coe : (E →ₗ[𝕜] 𝕜) → E → 𝕜) := by
    apply closure_minimal (t := UniformOnFun.toFun 𝔖 ⁻¹'
      range (DFunLike.coe : (E →ₗ[𝕜] 𝕜) → E → 𝕜)) ?_
      ((LinearMap.isClosed_range_coe E 𝕜 (RingHom.id 𝕜)).preimage
        (UniformOnFun.uniformContinuous_toFun h𝔖cover).continuous) hf
    rintro _ ⟨g, rfl⟩
    exact ⟨g.toLinearMap, rfl⟩
  obtain ⟨l, hl⟩ := hlin
  have hlcont : Continuous l := h l fun S hS ↦ by
    rw [hl]
    exact continuousOn_of_mem_closure_range_coeFn hf hS
  refine ⟨⟨l, hlcont⟩, ?_⟩
  apply (UniformOnFun.toFun 𝔖).injective
  exact hl

end General

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] {𝔖 : Set (Set E)}
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- If a directed nonempty family has cofinally many closed `ℝ`-convex balanced members,
a linear form continuous on every member is approximable by continuous linear forms
for uniform convergence on the family. This is the approximation part of the general
Grothendieck criterion, following Schaefer–Wolff, IV §6.2. -/
theorem mem_closure_range_coeFn_of_continuousOn
    (h𝔖ne : 𝔖.Nonempty) (h𝔖dir : DirectedOn (· ⊆ ·) 𝔖)
    (h𝔖disk : ∀ S ∈ 𝔖, ∃ T ∈ 𝔖, S ⊆ T ∧ IsClosed T ∧ Convex ℝ T ∧ Balanced 𝕜 T)
    (f : E →ₗ[𝕜] 𝕜) (hf : ∀ S ∈ 𝔖, ContinuousOn f S) :
    UniformOnFun.ofFun 𝔖 f ∈ closure (range (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe :
      (E →Lᵤ[𝕜, 𝔖] 𝕜) → E →ᵤ[𝔖] 𝕜)) := by
  rw [mem_closure_iff_nhds_basis (UniformOnFun.hasBasis_nhds_of_basis E 𝕜 𝔖
    (UniformOnFun.ofFun 𝔖 f) h𝔖ne h𝔖dir Metric.uniformity_basis_dist_le)]
  rintro ⟨S, ε⟩ ⟨hS, hε⟩
  obtain ⟨T, hT, hST, hTcl, hTc, hTb⟩ := h𝔖disk S hS
  obtain ⟨g, hg⟩ := f.exists_strongDual_norm_sub_le_of_continuousOn
    hTcl hTc hTb (hf T hT) hε
  refine ⟨UniformOnFun.ofFun 𝔖 g, ⟨g, rfl⟩, ?_⟩
  intro x hx
  simpa only [mem_ofPred_eq, UniformOnFun.toFun_ofFun, dist_eq_norm, norm_sub_rev]
    using hg x (hST hx)

/-- If the continuous dual is complete for uniform convergence on a covering directed
family with cofinally many closed `ℝ`-convex balanced members, continuity of a linear form
on every member implies its global continuity. This is the necessity
part of Schaefer–Wolff, IV §6.2. -/
theorem continuous_of_continuousOn_of_completeSpace
    (h𝔖ne : 𝔖.Nonempty) (h𝔖dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖cover : ⋃₀ 𝔖 = univ)
    (h𝔖disk : ∀ S ∈ 𝔖, ∃ T ∈ 𝔖, S ⊆ T ∧ IsClosed T ∧ Convex ℝ T ∧ Balanced 𝕜 T)
    [CompleteSpace (E →Lᵤ[𝕜, 𝔖] 𝕜)]
    (f : E →ₗ[𝕜] 𝕜) (hf : ∀ S ∈ 𝔖, ContinuousOn f S) : Continuous f := by
  let : T2Space (E →ᵤ[𝔖] 𝕜) := UniformOnFun.t2Space_of_covering h𝔖cover
  have hclosed := (isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 𝔖).isComplete_range.isClosed
  obtain ⟨g, hg⟩ := hclosed.closure_subset
    (mem_closure_range_coeFn_of_continuousOn h𝔖ne h𝔖dir h𝔖disk f hf)
  have heq : (g : E → 𝕜) = f := congrArg (UniformOnFun.toFun 𝔖) hg
  exact heq ▸ g.continuous

/-- Grothendieck's completeness criterion for the dual with uniform convergence on a family:
the dual is complete exactly when continuity on the family detects continuity of linear
forms. A covering directed family with cofinally many closed `ℝ`-convex balanced members suffices;
in particular, this applies to saturated covering families of bounded sets. Boundedness
is unnecessary for this uniform-space statement. This is
Schaefer–Wolff, IV §6.2. -/
theorem completeSpace_iff_forall_continuousOn
    (h𝔖ne : 𝔖.Nonempty) (h𝔖dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖cover : ⋃₀ 𝔖 = univ)
    (h𝔖disk : ∀ S ∈ 𝔖, ∃ T ∈ 𝔖, S ⊆ T ∧ IsClosed T ∧ Convex ℝ T ∧ Balanced 𝕜 T) :
    CompleteSpace (E →Lᵤ[𝕜, 𝔖] 𝕜) ↔
      ∀ f : E →ₗ[𝕜] 𝕜, (∀ S ∈ 𝔖, ContinuousOn f S) → Continuous f := by
  exact ⟨fun _ ↦ continuous_of_continuousOn_of_completeSpace h𝔖ne h𝔖dir h𝔖cover h𝔖disk,
    completeSpace_of_forall_continuousOn h𝔖cover⟩

end UniformConvergenceCLM

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {𝔖 : Set (Set (WeakBilin B.flip))}

/-- Grothendieck's criterion for a polar uniform structure on a paired space: completeness
is equivalent to representation by a point of every linear form on the other space whose
restrictions to the family are weakly continuous. This applies in particular to saturated
covering families of weakly bounded sets, and does not require the pairing to separate
points. This is Schaefer–Wolff, IV §6.2 and its dual-pair formulation. -/
theorem completeSpace_polarUniformSpace_iff
    (h𝔖ne : 𝔖.Nonempty) (h𝔖dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖cover : ⋃₀ 𝔖 = univ)
    (h𝔖disk : ∀ S ∈ 𝔖, ∃ T ∈ 𝔖, S ⊆ T ∧ IsClosed T ∧ Convex ℝ T ∧ Balanced 𝕜 T) :
    @CompleteSpace E (B.polarUniformSpace 𝔖) ↔
      ∀ f : WeakBilin B.flip →ₗ[𝕜] 𝕜, (∀ S ∈ 𝔖, ContinuousOn f S) →
        ∃ x : E, ∀ y : WeakBilin B.flip, f y = B x y := by
  let _ : UniformSpace E := B.polarUniformSpace 𝔖
  have hsurj : Surjective (B.toUniformConvergenceCLM 𝔖) := B.flip.dualEmbedding_surjective
  rw [(B.isUniformInducing_toUniformConvergenceCLM 𝔖).completeSpace_congr hsurj,
    UniformConvergenceCLM.completeSpace_iff_forall_continuousOn h𝔖ne h𝔖dir h𝔖cover h𝔖disk]
  constructor
  · intro h f hf
    obtain ⟨x, hx⟩ := B.flip.dualEmbedding_surjective ⟨f, h f hf⟩
    exact ⟨x, fun y ↦ (DFunLike.congr_fun hx y).symm⟩
  · intro h f hf
    obtain ⟨x, hx⟩ := h f hf
    have heq : (f : WeakBilin B.flip → 𝕜) = WeakBilin.eval B.flip x := funext hx
    exact heq.symm ▸ (WeakBilin.eval B.flip x).continuous

end LinearMap
