/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Group.SeparationQuotient

/-!
# The Banach space associated with a seminorm

For a seminorm `p`, `p.Completion` is the separated completion of the space with seminorm `p`,
equivalently the completion of the normed quotient by its kernel. The canonical map has dense
range and norm `p x`. Domination of seminorms gives contraction maps between the completions.
More generally, a linear map bounded with respect to two seminorms induces a unique
continuous linear map between their completions, with the same bound. These maps preserve
identities and composition. Mutually dominating seminorms have continuously linearly
equivalent completions. Bounds are recorded by nonnegative real constants.
These are the local Banach spaces used in the projective representation of a locally convex
space (Casselman, *Introduction to topological vector spaces*, §5). The construction and
proofs here independently use Mathlib's completion and extension theorems.
-/

@[expose] public noncomputable section

open UniformSpace Function
open scoped Topology NNReal

namespace Seminorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The underlying module equipped with the topology and uniformity of one seminorm. -/
def Space (_p : Seminorm 𝕜 E) := E

/-- The seminormed structure defined by the chosen seminorm. -/
instance (p : Seminorm 𝕜 E) : SeminormedAddCommGroup p.Space :=
  p.toSeminormedAddCommGroup

/-- The scalar action on the space of a seminorm. -/
instance (p : Seminorm 𝕜 E) : Module 𝕜 p.Space := inferInstanceAs (Module 𝕜 E)

/-- The chosen seminorm is homogeneous for the original scalar action. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.Space where
  toModule := (inferInstance : Module 𝕜 p.Space)
  norm_smul_le a x := (map_smul_eq_mul p a x).le

/-- The canonical linear identification with the space carrying just one seminorm. -/
def toSpace (p : Seminorm 𝕜 E) : E ≃ₗ[𝕜] p.Space := LinearEquiv.refl 𝕜 E

/-- The norm of the canonical image is the original seminorm. -/
@[simp] theorem norm_toSpace (p : Seminorm 𝕜 E) (x : E) : ‖p.toSpace x‖ = p x := rfl

/-- The local Banach space of a seminorm: the completion of its separated quotient. -/
def Completion (p : Seminorm 𝕜 E) := UniformSpace.Completion p.Space

/-- The normed quotient by the zero set of a seminorm, realized as its separated quotient. -/
def NormedQuotient (p : Seminorm 𝕜 E) := SeparationQuotient p.Space

/-- The quotient of a seminormed space by its zero seminorm vectors is normed. -/
instance (p : Seminorm 𝕜 E) : NormedAddCommGroup p.NormedQuotient :=
  inferInstanceAs (NormedAddCommGroup (SeparationQuotient p.Space))

/-- The normed quotient retains the original scalar action. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.NormedQuotient :=
  inferInstanceAs (NormedSpace 𝕜 (SeparationQuotient p.Space))

/-- The canonical surjection to the normed quotient of a seminorm. -/
def toNormedQuotient (p : Seminorm 𝕜 E) : E →ₗ[𝕜] p.NormedQuotient :=
  (SeparationQuotient.mkCLM 𝕜 p.Space).toLinearMap.comp p.toSpace.toLinearMap

/-- The quotient norm is precisely the original seminorm. -/
@[simp] theorem norm_toNormedQuotient (p : Seminorm 𝕜 E) (x : E) :
    ‖p.toNormedQuotient x‖ = p x := SeparationQuotient.norm_mk _

/-- The normed quotient kills exactly the zero set of the seminorm. -/
theorem toNormedQuotient_eq_zero_iff (p : Seminorm 𝕜 E) (x : E) :
    p.toNormedQuotient x = 0 ↔ p x = 0 := by rw [← norm_eq_zero, norm_toNormedQuotient]

/-- Every point of the normed quotient has a representative in the original module. -/
theorem surjective_toNormedQuotient (p : Seminorm 𝕜 E) : Surjective p.toNormedQuotient :=
  @SeparationQuotient.surjective_mk p.Space _

/-- The local completion is a normed additive group. -/
instance (p : Seminorm 𝕜 E) : NormedAddCommGroup p.Completion :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion p.Space))

/-- The local completion is a normed space. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.Completion :=
  inferInstanceAs (NormedSpace 𝕜 (UniformSpace.Completion p.Space))

/-- The local completion is complete. -/
instance (p : Seminorm 𝕜 E) : CompleteSpace p.Completion :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion p.Space))

/-- The canonical map into the local Banach space. -/
def toCompletion (p : Seminorm 𝕜 E) : E →ₗ[𝕜] p.Completion where
  toFun x := (p.toSpace x : UniformSpace.Completion p.Space)
  map_add' x y := by rw [map_add, UniformSpace.Completion.coe_add]; rfl
  map_smul' a x := by rw [map_smul, UniformSpace.Completion.coe_smul]; rfl

/-- The canonical map into the local completion preserves the seminorm. -/
@[simp] theorem norm_toCompletion (p : Seminorm 𝕜 E) (x : E) :
    ‖p.toCompletion x‖ = p x := UniformSpace.Completion.norm_coe _

/-- The canonical map identifies exactly the kernel of the seminorm. -/
theorem toCompletion_eq_zero_iff (p : Seminorm 𝕜 E) (x : E) :
    p.toCompletion x = 0 ↔ p x = 0 := by rw [← norm_eq_zero, norm_toCompletion]

/-- The image of the original module is dense in its local Banach space. -/
theorem denseRange_toCompletion (p : Seminorm 𝕜 E) : DenseRange p.toCompletion :=
  @UniformSpace.Completion.denseRange_coe p.Space _

/-- Domination of seminorms gives a contraction between their seminormed spaces. -/
def mapSpace {p q : Seminorm 𝕜 E} (h : p ≤ q) : q.Space →L[𝕜] p.Space :=
  (p.toSpace.toLinearMap.comp q.toSpace.symm.toLinearMap).mkContinuous 1
    (fun x ↦ by change p x ≤ 1 * q x; simpa using h x)

/-- Domination of seminorms gives a contraction between the local Banach spaces. -/
def completionMap {p q : Seminorm 𝕜 E} (h : p ≤ q) :
    q.Completion →L[𝕜] p.Completion := (mapSpace h).completion

/-- The connecting maps commute with the maps from the original module. -/
@[simp] theorem completionMap_toCompletion {p q : Seminorm 𝕜 E} (h : p ≤ q) (x : E) :
    completionMap h (q.toCompletion x) = p.toCompletion x :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- The identity inequality induces the identity connecting map. -/
@[simp] theorem completionMap_refl (p : Seminorm 𝕜 E) : completionMap (le_refl p) = .id 𝕜 _ := by
  ext x
  exact p.denseRange_toCompletion.induction_on x
    (isClosed_eq (completionMap _).continuous continuous_id) (by simp)

/-- Connecting maps compose according to transitivity of domination. -/
theorem completionMap_comp {p q r : Seminorm 𝕜 E} (hpq : p ≤ q) (hqr : q ≤ r) :
    (completionMap hpq).comp (completionMap hqr) = completionMap (hpq.trans hqr) := by
  ext x
  exact r.denseRange_toCompletion.induction_on x
    (isClosed_eq ((completionMap hpq).comp (completionMap hqr)).continuous
      (completionMap _).continuous) (by simp)

/-- Connecting maps are contractions. -/
theorem norm_completionMap_le {p q : Seminorm 𝕜 E} (h : p ≤ q) (x : q.Completion) :
    ‖completionMap h x‖ ≤ ‖x‖ := by
  refine q.denseRange_toCompletion.induction ?_
    (isClosed_le (completionMap h).continuous.norm continuous_norm) x
  rintro _ ⟨y, rfl⟩
  simpa using h y

section Maps

variable {F G : Type*} [AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G]

/-- A linear map bounded with respect to two seminorms, as a continuous linear map between
their seminormed spaces. -/
def mapSpaceOfBound (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) : p.Space →L[𝕜] q.Space :=
  (q.toSpace.toLinearMap.comp (f.comp p.toSpace.symm.toLinearMap)).mkContinuous C h

/-- A seminorm-bounded linear map induces a continuous linear map between the associated
completions. -/
def mapCompletion (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) : p.Completion →L[𝕜] q.Completion :=
  (mapSpaceOfBound p q f C h).completion

/-- The induced map on completions agrees with the original map on canonical images. -/
@[simp] theorem mapCompletion_toCompletion (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) (x : E) :
    mapCompletion p q f C h (p.toCompletion x) = q.toCompletion (f x) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- A continuous linear map between seminorm completions is determined by its values on
the canonical image of the source. -/
theorem mapCompletion_unique (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x)
    (g : p.Completion →L[𝕜] q.Completion)
    (hg : ∀ x, g (p.toCompletion x) = q.toCompletion (f x)) :
    g = mapCompletion p q f C h := by
  ext z
  exact p.denseRange_toCompletion.induction_on z
    (isClosed_eq g.continuous (mapCompletion p q f C h).continuous)
    (fun x ↦ by rw [hg, mapCompletion_toCompletion])

/-- The map induced on completions is independent of the chosen bound. -/
theorem mapCompletion_eq (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C D : ℝ≥0) (hC : ∀ x, q (f x) ≤ C * p x) (hD : ∀ x, q (f x) ≤ D * p x) :
    mapCompletion p q f C hC = mapCompletion p q f D hD := by
  apply mapCompletion_unique
  exact mapCompletion_toCompletion p q f C hC

/-- The seminorm bound is preserved on the completions. -/
theorem norm_mapCompletion_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) (z : p.Completion) :
    ‖mapCompletion p q f C h z‖ ≤ C * ‖z‖ := by
  refine p.denseRange_toCompletion.induction_on z
    (isClosed_le (mapCompletion p q f C h).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro x
  simpa only [mapCompletion_toCompletion, norm_toCompletion] using h x

/-- The operator norm of the induced map is bounded by the original seminorm bound. -/
theorem opNorm_mapCompletion_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) :
    ‖mapCompletion p q f C h‖ ≤ C :=
  (mapCompletion p q f C h).opNorm_le_bound C.coe_nonneg
    (norm_mapCompletion_le p q f C h)

/-- The identity linear map induces the identity on a seminorm completion. -/
@[simp] theorem mapCompletion_id (p : Seminorm 𝕜 E) :
    mapCompletion p p (LinearMap.id) 1 (by intro x; simp) = .id 𝕜 _ := by
  symm
  apply mapCompletion_unique
  intro x
  rfl

/-- Induced maps on seminorm completions preserve composition. -/
theorem mapCompletion_comp (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (r : Seminorm 𝕜 G)
    (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] G) (C D : ℝ≥0)
    (hf : ∀ x, q (f x) ≤ C * p x) (hg : ∀ y, r (g y) ≤ D * q y) :
    (mapCompletion q r g D hg).comp (mapCompletion p q f C hf) =
      mapCompletion p r (g.comp f) (D * C) (fun x ↦ by
        calc r (g (f x)) ≤ D * q (f x) := hg (f x)
          _ ≤ D * (C * p x) := mul_le_mul_of_nonneg_left (hf x) D.coe_nonneg
          _ = (↑(D * C) : ℝ) * p x := by rw [NNReal.coe_mul, mul_assoc]) := by
  apply mapCompletion_unique
  intro x
  simp

/-- The original contraction connecting two dominated seminorms is the induced completion
map of the identity linear map. -/
theorem completionMap_eq_mapCompletion {p q : Seminorm 𝕜 E} (h : p ≤ q) :
    completionMap h = mapCompletion q p (LinearMap.id) 1
      (fun x ↦ by simpa using h x) := by
  apply mapCompletion_unique
  exact completionMap_toCompletion h

/-- Mutually dominating seminorms have continuously linearly equivalent completions;
the equivalence extends the identity on the original module. -/
def completionEquivOfBounds (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) :
    p.Completion ≃L[𝕜] q.Completion := by
  let f := mapCompletion p q (LinearMap.id) C hpq
  let g := mapCompletion q p (LinearMap.id) D hqp
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · intro z
    exact p.denseRange_toCompletion.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id)
      (fun x ↦ by simp [f, g])
  · intro z
    exact q.denseRange_toCompletion.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id)
      (fun x ↦ by simp [f, g])

/-- The equivalence of completions of mutually dominating seminorms preserves canonical
images of the original module. -/
@[simp] theorem completionEquivOfBounds_toCompletion (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) (x : E) :
    completionEquivOfBounds p q C D hpq hqp (p.toCompletion x) = q.toCompletion x :=
  mapCompletion_toCompletion p q (LinearMap.id) C hpq x

/-- The inverse equivalence also preserves canonical images. -/
@[simp] theorem completionEquivOfBounds_symm_toCompletion (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) (x : E) :
    (completionEquivOfBounds p q C D hpq hqp).symm (q.toCompletion x) = p.toCompletion x :=
  mapCompletion_toCompletion q p (LinearMap.id) D hqp x

end Maps

end Seminorm
