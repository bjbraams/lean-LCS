/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.GrothendieckCompleteness

/-!
# The dual description of the completion

Let `E` be a locally convex space over `ℝ` or `ℂ`, with its compatible additive uniform
structure. `GrothendieckCompletion 𝕜 E` consists of the linear forms on the continuous dual of `E`
whose restrictions to zero-neighbourhood polars are weak-* continuous. These are precisely
the forms continuous on every equicontinuous subset. Extension of continuous functionals
identifies this space with `UniformSpace.Completion E`.

The uniform structure is transported along that identification. Its neighbourhood basis
is described by uniform bounds on polars, expressing uniform convergence on equicontinuous
sets. Evaluation embeds a Hausdorff `E` uniformly with dense image.

## Main statements

* `StrongDual.mem_equicontinuousDual_iff`: the defining continuity condition can be tested
  on all equicontinuous sets.
* `GrothendieckCompletion.completionEquiv`, `completionUniformEquiv`: continuous linear and
  uniform identifications with the usual completion.
* `GrothendieckCompletion.hasBasis_nhds_zero`: the polar neighbourhood basis.
* `GrothendieckCompletion.denseRange_evaluation`, `isUniformEmbedding_evaluation`: evaluation
  embeds a Hausdorff space uniformly and densely.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §6.2.
-/

public noncomputable section

open Set Filter Function
open scoped Topology Pointwise

namespace StrongDual

variable (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The linear forms on the continuous dual whose restrictions to the polars of all zero
neighbourhoods are weak-* continuous. -/
@[expose]
def equicontinuousDual : Submodule 𝕜 (StrongDual 𝕜 E →ₗ[𝕜] 𝕜) where
  carrier := {f | ∀ U ∈ 𝓝 (0 : E), ContinuousOn
    (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U)}
  zero_mem' := fun _ _ ↦ continuousOn_const
  add_mem' := fun hf hg U hU ↦ (hf U hU).add (hg U hU)
  smul_mem' := fun c _ hf U hU ↦ (hf U hU).const_smul c

variable {𝕜 E} [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- Testing weak-* continuity on zero-neighbourhood polars is equivalent to testing it on
all equicontinuous sets of continuous functionals. -/
theorem mem_equicontinuousDual_iff (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜) :
    f ∈ equicontinuousDual 𝕜 E ↔ ∀ H : Set (StrongDual 𝕜 E),
      Equicontinuous ((↑) : H → E → 𝕜) →
      ContinuousOn (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ))
        (WeakDual.toStrongDual ⁻¹' H) := by
  constructor
  · intro hf H hH
    obtain ⟨U, hU, hHU⟩ := StrongDual.exists_mem_nhds_subset_polar hH
    exact (hf U hU).mono fun φ hφ ↦ hHU hφ
  · intro hf U hU
    exact hf (StrongDual.polar 𝕜 U) (StrongDual.equicontinuous_polar hU)

end StrongDual

/-- The dual model of the completion: linear forms on the continuous dual that are weak-*
continuous on every equicontinuous set, tested on zero-neighbourhood polars. This is a type
synonym of the submodule `StrongDual.equicontinuousDual 𝕜 E`, not an `abbrev`, so that the
uniform structure transported below does not become an instance on that submodule. -/
@[expose]
def GrothendieckCompletion (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] : Type _ := StrongDual.equicontinuousDual 𝕜 E

namespace GrothendieckCompletion

section Basic

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The dual model is an additive group, as a submodule of the linear forms on the dual. -/
instance instAddCommGroup : AddCommGroup (GrothendieckCompletion 𝕜 E) :=
  inferInstanceAs (AddCommGroup (StrongDual.equicontinuousDual 𝕜 E))

/-- The dual model is a module, as a submodule of the linear forms on the dual. -/
instance instModule : Module 𝕜 (GrothendieckCompletion 𝕜 E) :=
  inferInstanceAs (Module 𝕜 (StrongDual.equicontinuousDual 𝕜 E))

/-- The dual model is a real vector space, by restriction of scalars. -/
instance instModuleReal : Module ℝ (GrothendieckCompletion 𝕜 E) :=
  inferInstanceAs (Module ℝ (StrongDual.equicontinuousDual 𝕜 E))

/-- The real and the `𝕜`-module structures of the dual model are compatible. -/
instance instIsScalarTower : IsScalarTower ℝ 𝕜 (GrothendieckCompletion 𝕜 E) :=
  inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual.equicontinuousDual 𝕜 E))

/-- The underlying linear form on the continuous dual. -/
@[expose]
def toLinearMap (f : GrothendieckCompletion 𝕜 E) : StrongDual 𝕜 E →ₗ[𝕜] 𝕜 :=
  (show StrongDual.equicontinuousDual 𝕜 E from f).1

/-- An element of the dual model is a linear form on the continuous dual. -/
instance instFunLike : FunLike (GrothendieckCompletion 𝕜 E) (StrongDual 𝕜 E) 𝕜 where
  coe f := f.toLinearMap
  coe_injective _ _ h := Subtype.ext (LinearMap.coe_injective h)

/-- The coercion to functions factors through the underlying linear form. -/
@[simp]
theorem coe_toLinearMap (f : GrothendieckCompletion 𝕜 E) : ⇑f.toLinearMap = f :=
  rfl

/-- Elements of the dual model agree if they agree on every continuous functional. -/
@[ext]
theorem ext {f g : GrothendieckCompletion 𝕜 E} (h : ∀ φ, f φ = g φ) : f = g :=
  DFunLike.ext f g h

/-- Elements of the dual model are equal if and only if they agree on every continuous
functional. -/
add_decl_doc GrothendieckCompletion.ext_iff

/-- The element of the dual model given by a linear form on the dual that is weak-*
continuous on the polars of the neighbourhoods of zero. -/
@[expose]
def mk (g : StrongDual 𝕜 E →ₗ[𝕜] 𝕜) (hg : g ∈ StrongDual.equicontinuousDual 𝕜 E) :
    GrothendieckCompletion 𝕜 E :=
  (⟨g, hg⟩ : StrongDual.equicontinuousDual 𝕜 E)

/-- The element built from a linear form evaluates as that linear form. -/
@[simp]
theorem mk_apply (g : StrongDual 𝕜 E →ₗ[𝕜] 𝕜) (hg : g ∈ StrongDual.equicontinuousDual 𝕜 E)
    (φ : StrongDual 𝕜 E) : mk g hg φ = g φ :=
  rfl

/-- The linear form underlying an element of the dual model is weak-* continuous on the polar
of every neighbourhood of zero. -/
theorem continuousOn_polar (f : GrothendieckCompletion 𝕜 E) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    ContinuousOn (fun φ : WeakDual 𝕜 E ↦ f (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U) :=
  (show StrongDual.equicontinuousDual 𝕜 E from f).2 U hU

end Basic

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [UniformContinuousConstSMul 𝕜 E] [UniformContinuousConstSMul ℝ E]

/-- Evaluation of extended functionals at a point of the completion defines a form in the
dual model. -/
@[expose]
def ofCompletion : UniformSpace.Completion E →ₗ[𝕜] GrothendieckCompletion 𝕜 E where
  toFun z := mk
    { toFun := fun φ ↦ (UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ z
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    fun U hU ↦ UniformSpace.Completion.continuousOn_extend_eval_polar z hU
  map_add' z w := by
    ext φ
    exact map_add ((UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ) z w
  map_smul' c z := by
    ext φ
    exact map_smul ((UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ) c z

omit [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] [UniformContinuousConstSMul ℝ E] in
/-- The form attached to a point of the completion evaluates the extended functionals. -/
@[simp]
theorem ofCompletion_apply (z : UniformSpace.Completion E) (φ : StrongDual 𝕜 E) :
    ofCompletion z φ = (UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ z :=
  rfl

/-- The dual model distinguishes points of the completion. -/
theorem ofCompletion_injective : Injective (ofCompletion (𝕜 := 𝕜) (E := E)) := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  intro z w h
  by_contra hne
  obtain ⟨ψ, hψ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hne
  have he := congrArg (fun f : GrothendieckCompletion 𝕜 E ↦
    f (UniformSpace.Completion.strongDualEquiv 𝕜 E ψ)) h
  have he' : ψ z = ψ w := by simpa using he
  exact (ne_of_lt hψ) (congrArg RCLike.re he')

/-- Every form in the dual model is evaluation at a point of the completion. -/
theorem ofCompletion_surjective : Surjective (ofCompletion (𝕜 := 𝕜) (E := E)) := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  intro f
  let e := UniformSpace.Completion.strongDualEquiv 𝕜 E
  let g := f.toLinearMap.comp e.toLinearMap
  have hg (V : Set (UniformSpace.Completion E)) (hV : V ∈ 𝓝 0) :
      ContinuousOn (fun ψ : WeakDual 𝕜 (UniformSpace.Completion E) ↦
        g (WeakDual.toStrongDual ψ)) (WeakDual.polar 𝕜 V) := by
    let U : Set E := ((↑) : E → UniformSpace.Completion E) ⁻¹' V
    have hU : U ∈ 𝓝 (0 : E) :=
      (UniformSpace.Completion.coeCLM 𝕜 E).continuous.continuousAt.preimage_mem_nhds hV
    have hc : Continuous (fun ψ : WeakDual 𝕜 (UniformSpace.Completion E) ↦
        StrongDual.toWeakDual (e (WeakDual.toStrongDual ψ))) :=
      WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (x :
        UniformSpace.Completion E)
    exact (f.continuousOn_polar hU).comp hc.continuousOn (fun ψ hψ x hx ↦ hψ _ hx)
  obtain ⟨z, hz⟩ := StrongDual.exists_forall_eq_apply_of_completeSpace g hg
  refine ⟨z, ext fun φ ↦ ?_⟩
  have he := hz (e.symm φ)
  simpa [g] using he.symm

/-- The linear identification of the usual completion with its dual model. -/
@[expose]
def completionLinearEquiv : UniformSpace.Completion E ≃ₗ[𝕜] GrothendieckCompletion 𝕜 E :=
  LinearEquiv.ofBijective ofCompletion ⟨ofCompletion_injective, ofCompletion_surjective⟩

/-- The uniform structure transported from the usual completion. The neighbourhood-basis
theorem below identifies it as uniform convergence on equicontinuous sets. -/
instance instUniformSpace : UniformSpace (GrothendieckCompletion 𝕜 E) :=
  UniformSpace.comap (completionLinearEquiv (𝕜 := 𝕜) (E := E)).symm inferInstance

/-- The additive uniform structure of the dual model. -/
instance instIsUniformAddGroup : IsUniformAddGroup (GrothendieckCompletion 𝕜 E) :=
  .comap (completionLinearEquiv (𝕜 := 𝕜) (E := E)).symm.toAddEquiv

/-- The uniform identification of the usual completion with its dual model. -/
@[expose]
def completionUniformEquiv : UniformSpace.Completion E ≃ᵤ GrothendieckCompletion 𝕜 E :=
  ((completionLinearEquiv (𝕜 := 𝕜) (E := E)).symm.toEquiv.toUniformEquivOfIsUniformInducing
    ⟨rfl⟩).symm

/-- The dual model is complete. -/
instance instCompleteSpace : CompleteSpace (GrothendieckCompletion 𝕜 E) :=
  (completionUniformEquiv (𝕜 := 𝕜) (E := E)).completeSpace_iff.mp inferInstance

/-- The dual model is Hausdorff. -/
instance instT2Space : T2Space (GrothendieckCompletion 𝕜 E) :=
  (completionUniformEquiv (𝕜 := 𝕜) (E := E)).symm.toHomeomorph.isEmbedding.t2Space

/-- Scalar multiplication on the dual model is jointly continuous. -/
instance instContinuousSMul : ContinuousSMul 𝕜 (GrothendieckCompletion 𝕜 E) :=
  continuousSMul_induced (completionLinearEquiv (𝕜 := 𝕜) (E := E)).symm.toLinearMap

/-- The dual model is locally convex for uniform convergence on equicontinuous sets. -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (GrothendieckCompletion 𝕜 E) := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  exact LocallyConvexSpace.induced
    ((completionLinearEquiv (𝕜 := 𝕜) (E := E)).symm.toLinearMap.restrictScalars ℝ)

/-- The continuous linear identification of the usual completion with the dual model. -/
@[expose]
def completionEquiv : UniformSpace.Completion E ≃L[𝕜] GrothendieckCompletion 𝕜 E where
  toLinearEquiv := completionLinearEquiv
  continuous_toFun := completionUniformEquiv.continuous
  continuous_invFun := completionUniformEquiv.symm.continuous

/-- Evaluation at a point of the original space as an element of the dual model. -/
@[expose]
def evaluation : E →L[𝕜] GrothendieckCompletion 𝕜 E :=
  completionEquiv.toContinuousLinearMap.comp (UniformSpace.Completion.coeCLM 𝕜 E)

/-- The canonical map into the dual model evaluates continuous functionals. -/
@[simp]
theorem evaluation_apply (x : E) (φ : StrongDual 𝕜 E) :
    evaluation (𝕜 := 𝕜) x φ = φ x :=
  UniformSpace.Completion.strongDualEquiv_symm_apply_coe φ x

/-- Evaluation is uniformly inducing, even if the original space is not Hausdorff. -/
theorem isUniformInducing_evaluation : IsUniformInducing (evaluation (𝕜 := 𝕜) (E := E)) :=
  completionUniformEquiv.isUniformInducing.comp
    (UniformSpace.Completion.isUniformInducing_coeCLM 𝕜 E)

/-- For a Hausdorff space, evaluation into the dual model is a uniform embedding. -/
theorem isUniformEmbedding_evaluation [T2Space E] :
    IsUniformEmbedding (evaluation (𝕜 := 𝕜) (E := E)) :=
  ⟨isUniformInducing_evaluation, completionEquiv.injective.comp
    (UniformSpace.Completion.coe_injective E)⟩

/-- The evaluations at points of the original space are dense in the dual model. -/
theorem denseRange_evaluation : DenseRange (evaluation (𝕜 := 𝕜) (E := E)) :=
  (completionEquiv (𝕜 := 𝕜) (E := E)).surjective.denseRange.comp
    (UniformSpace.Completion.denseRange_coeCLM 𝕜 E) completionEquiv.continuous

/-- A point of the completion lies in the closure of a `ℝ`-convex balanced neighbourhood precisely
when its associated form is bounded by one on that neighbourhood's polar. -/
theorem mem_closure_image_iff {U : Set E} (hU : U ∈ 𝓝 (0 : E))
    (hc : Convex ℝ U) (hb : Balanced 𝕜 U) (z : UniformSpace.Completion E) :
    z ∈ closure (((↑) : E → UniformSpace.Completion E) '' U) ↔
      ∀ φ ∈ StrongDual.polar 𝕜 U, ‖ofCompletion z φ‖ ≤ 1 := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let c := UniformSpace.Completion.coeCLM 𝕜 E
  let V := closure (c '' U)
  have hVc : Convex ℝ V := (hc.is_linear_image (c.restrictScalars ℝ).toLinearMap.isLinear).closure
  have hVb : Balanced 𝕜 V := (hb.image c.toLinearMap).closure
  have hV0 : (0 : UniformSpace.Completion E) ∈ V :=
    subset_closure ⟨0, mem_of_mem_nhds hU, map_zero c⟩
  change z ∈ V ↔ _
  rw [← StrongDual.bipolar_eq_self (𝕜 := 𝕜) hVc hVb isClosed_closure ⟨0, hV0⟩]
  constructor
  · intro hz φ hφ
    exact hz ((UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ)
      ((UniformSpace.Completion.mem_polar_closure_image_iff
        (StrongDual.toWeakDual ((UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ))).mpr
          (by
            change ∀ x ∈ U, ‖(UniformSpace.Completion.strongDualEquiv 𝕜 E
              ((UniformSpace.Completion.strongDualEquiv 𝕜 E).symm φ)) x‖ ≤ 1
            rw [LinearEquiv.apply_symm_apply]
            exact hφ))
  · intro hz ψ hψ
    have hp := (UniformSpace.Completion.mem_polar_closure_image_iff
      (StrongDual.toWeakDual ψ)).mp hψ
    simpa using hz (UniformSpace.Completion.strongDualEquiv 𝕜 E ψ) hp

/-- A basis of zero neighbourhoods in the dual model consists of uniform bounds by one on
polars of `ℝ`-convex balanced zero neighbourhoods of the original space. Thus the transported
topology is the topology of uniform convergence on equicontinuous sets. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : GrothendieckCompletion 𝕜 E)).HasBasis
      (fun U : Set E ↦ U ∈ 𝓝 (0 : E) ∧ Convex ℝ U ∧ Balanced 𝕜 U)
      (fun U ↦ {f | ∀ φ ∈ StrongDual.polar 𝕜 U, ‖f φ‖ ≤ 1}) := by
  have hbase : (𝓝 (0 : UniformSpace.Completion E)).HasBasis
      (fun U : Set E ↦ U ∈ 𝓝 (0 : E) ∧ Convex ℝ U ∧ Balanced 𝕜 U)
      (fun U ↦ closure (((↑) : E → UniformSpace.Completion E) '' U)) := by
    refine UniformSpace.Completion.hasBasis_nhds_zero_closure_image.to_hasBasis
      (fun U hU ↦ ?_) (fun U hU ↦ ⟨U, hU.1, Subset.rfl⟩)
    obtain ⟨V, hV, hVU⟩ := (nhds_zero_hasBasis_convex_balanced 𝕜 E).mem_iff.mp hU
    exact ⟨V, hV, closure_mono (image_mono hVU)⟩
  have hm := hbase.map (completionEquiv (𝕜 := 𝕜) (E := E))
  have heq : Filter.map (completionEquiv (𝕜 := 𝕜) (E := E)) (𝓝 0) = 𝓝 0 := by
    exact ((completionEquiv (𝕜 := 𝕜) (E := E)).toHomeomorph.map_nhds_eq 0).trans
      (congrArg nhds (map_zero (completionEquiv (𝕜 := 𝕜) (E := E))))
  rw [heq] at hm
  refine hm.congr (fun _ ↦ Iff.rfl) fun U hU ↦ ?_
  ext f
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_closure_image_iff hU.1 hU.2.1 hU.2.2 z).mp hz
  · intro hf
    obtain ⟨z, rfl⟩ := completionEquiv.surjective f
    exact ⟨z, (mem_closure_image_iff hU.1 hU.2.1 hU.2.2 z).mpr hf, rfl⟩

end GrothendieckCompletion
