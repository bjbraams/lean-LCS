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

For a seminorm `p` on `E`, the local space `p.LocalSpace` is `E` with the single seminorm `p`,
the local normed space `p.LocalNormedSpace` is its quotient by the kernel of `p`, and the local
Banach space `p.LocalBanachSpace` is its separated completion. These local Banach spaces are used
in the projective representation of a locally convex space. Bounds are recorded by nonnegative
real constants.

## Main definitions

* `Seminorm.LocalSpace p`, `Seminorm.LocalNormedSpace p`, `Seminorm.LocalBanachSpace p`: the
  space with the single seminorm `p`, its normed quotient, and its completion.
* `Seminorm.toLocalBanachSpace p`: the canonical map, with dense range and norm `p x`.
* `Seminorm.LocalBanachSpace.mapOfLE`: the contraction between local Banach spaces for dominated
  seminorms.
* `Seminorm.LocalBanachSpace.map`: the continuous linear map between local Banach spaces induced
  by a linear map bounded with respect to two seminorms.
* `Seminorm.LocalBanachSpace.equivOfBounds`: the local Banach spaces of mutually dominating
  seminorms are isomorphic.

## Main statements

* `Seminorm.LocalBanachSpace.map_unique`, `Seminorm.LocalBanachSpace.map_id`,
  `Seminorm.LocalBanachSpace.map_comp`: functoriality.
* `Seminorm.LocalBanachSpace.opNorm_map_le`: the seminorm bound is preserved.

## References

* [B. Casselman, *Introduction to Topological Vector Spaces*][casselman2016], §5
-/

@[expose] public noncomputable section

open UniformSpace Function
open scoped Topology NNReal

namespace Seminorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The underlying module equipped with the topology and uniformity of one seminorm. -/
def LocalSpace (_p : Seminorm 𝕜 E) := E

/-- The seminormed structure defined by the chosen seminorm. -/
instance (p : Seminorm 𝕜 E) : SeminormedAddCommGroup p.LocalSpace :=
  p.toSeminormedAddCommGroup

/-- The scalar action on the space of a seminorm. -/
instance (p : Seminorm 𝕜 E) : Module 𝕜 p.LocalSpace := inferInstanceAs (Module 𝕜 E)

/-- The chosen seminorm is homogeneous for the original scalar action. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.LocalSpace where
  toModule := (inferInstance : Module 𝕜 p.LocalSpace)
  norm_smul_le a x := (map_smul_eq_mul p a x).le

/-- The canonical linear identification with the space carrying just one seminorm. -/
def toLocalSpace (p : Seminorm 𝕜 E) : E ≃ₗ[𝕜] p.LocalSpace := LinearEquiv.refl 𝕜 E

/-- The norm of the canonical image is the original seminorm. -/
@[simp] theorem norm_toLocalSpace (p : Seminorm 𝕜 E) (x : E) : ‖p.toLocalSpace x‖ = p x := rfl

/-- The local Banach space of a seminorm: the completion of its separated quotient. -/
def LocalBanachSpace (p : Seminorm 𝕜 E) := UniformSpace.Completion p.LocalSpace

/-- The normed quotient by the zero set of a seminorm, realized as its separated quotient. -/
def LocalNormedSpace (p : Seminorm 𝕜 E) := SeparationQuotient p.LocalSpace

/-- The quotient of a seminormed space by its zero seminorm vectors is normed. -/
instance (p : Seminorm 𝕜 E) : NormedAddCommGroup p.LocalNormedSpace :=
  inferInstanceAs (NormedAddCommGroup (SeparationQuotient p.LocalSpace))

/-- The normed quotient retains the original scalar action. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.LocalNormedSpace :=
  inferInstanceAs (NormedSpace 𝕜 (SeparationQuotient p.LocalSpace))

/-- The canonical surjection to the normed quotient of a seminorm. -/
def toLocalNormedSpace (p : Seminorm 𝕜 E) : E →ₗ[𝕜] p.LocalNormedSpace :=
  (SeparationQuotient.mkCLM 𝕜 p.LocalSpace).toLinearMap.comp p.toLocalSpace.toLinearMap

/-- The quotient norm is precisely the original seminorm. -/
@[simp] theorem norm_toLocalNormedSpace (p : Seminorm 𝕜 E) (x : E) :
    ‖p.toLocalNormedSpace x‖ = p x := SeparationQuotient.norm_mk _

/-- The normed quotient kills exactly the zero set of the seminorm. -/
theorem toLocalNormedSpace_eq_zero_iff (p : Seminorm 𝕜 E) (x : E) :
    p.toLocalNormedSpace x = 0 ↔ p x = 0 := by rw [← norm_eq_zero, norm_toLocalNormedSpace]

/-- Every point of the normed quotient has a representative in the original module. -/
theorem surjective_toLocalNormedSpace (p : Seminorm 𝕜 E) : Surjective p.toLocalNormedSpace :=
  @SeparationQuotient.surjective_mk p.LocalSpace _

/-- The local completion is a normed additive group. -/
instance (p : Seminorm 𝕜 E) : NormedAddCommGroup p.LocalBanachSpace :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion p.LocalSpace))

/-- The local completion is a normed space. -/
instance (p : Seminorm 𝕜 E) : NormedSpace 𝕜 p.LocalBanachSpace :=
  inferInstanceAs (NormedSpace 𝕜 (UniformSpace.Completion p.LocalSpace))

/-- The local completion is complete. -/
instance (p : Seminorm 𝕜 E) : CompleteSpace p.LocalBanachSpace :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion p.LocalSpace))

/-- The canonical map into the local Banach space. -/
def toLocalBanachSpace (p : Seminorm 𝕜 E) : E →ₗ[𝕜] p.LocalBanachSpace where
  toFun x := (p.toLocalSpace x : UniformSpace.Completion p.LocalSpace)
  map_add' x y := by rw [map_add, UniformSpace.Completion.coe_add]; rfl
  map_smul' a x := by rw [map_smul, UniformSpace.Completion.coe_smul]; rfl

/-- The canonical map into the local completion preserves the seminorm. -/
@[simp] theorem norm_toLocalBanachSpace (p : Seminorm 𝕜 E) (x : E) :
    ‖p.toLocalBanachSpace x‖ = p x := UniformSpace.Completion.norm_coe _

/-- The canonical map identifies exactly the kernel of the seminorm. -/
theorem toLocalBanachSpace_eq_zero_iff (p : Seminorm 𝕜 E) (x : E) :
    p.toLocalBanachSpace x = 0 ↔ p x = 0 := by rw [← norm_eq_zero, norm_toLocalBanachSpace]

/-- The image of the original module is dense in its local Banach space. -/
theorem denseRange_toLocalBanachSpace (p : Seminorm 𝕜 E) : DenseRange p.toLocalBanachSpace :=
  @UniformSpace.Completion.denseRange_coe p.LocalSpace _

/-- Domination of seminorms gives a contraction between their seminormed spaces. -/
def LocalSpace.mapOfLE {p q : Seminorm 𝕜 E} (h : p ≤ q) : q.LocalSpace →L[𝕜] p.LocalSpace :=
  (p.toLocalSpace.toLinearMap.comp q.toLocalSpace.symm.toLinearMap).mkContinuous 1
    (fun x ↦ by change p x ≤ 1 * q x; simpa using h x)

section Maps

variable {F G : Type*} [AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G]

/-- A linear map bounded with respect to two seminorms, as a continuous linear map between
their seminormed spaces. -/
def LocalSpace.map (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) : p.LocalSpace →L[𝕜] q.LocalSpace :=
  (q.toLocalSpace.toLinearMap.comp (f.comp p.toLocalSpace.symm.toLinearMap)).mkContinuous C h

end Maps

namespace LocalBanachSpace

/-- Domination of seminorms gives a contraction between the local Banach spaces. -/
def mapOfLE {p q : Seminorm 𝕜 E} (h : p ≤ q) :
    q.LocalBanachSpace →L[𝕜] p.LocalBanachSpace := (LocalSpace.mapOfLE h).completion

/-- The connecting maps commute with the maps from the original module. -/
@[simp] theorem mapOfLE_toLocalBanachSpace {p q : Seminorm 𝕜 E} (h : p ≤ q) (x : E) :
    mapOfLE h (q.toLocalBanachSpace x) = p.toLocalBanachSpace x :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- The identity inequality induces the identity connecting map. -/
@[simp] theorem mapOfLE_refl (p : Seminorm 𝕜 E) : mapOfLE (le_refl p) = .id 𝕜 _ := by
  ext x
  exact p.denseRange_toLocalBanachSpace.induction_on x
    (isClosed_eq (mapOfLE _).continuous continuous_id) (by simp)

/-- Connecting maps compose according to transitivity of domination. -/
theorem mapOfLE_comp {p q r : Seminorm 𝕜 E} (hpq : p ≤ q) (hqr : q ≤ r) :
    (mapOfLE hpq).comp (mapOfLE hqr) = mapOfLE (hpq.trans hqr) := by
  ext x
  exact r.denseRange_toLocalBanachSpace.induction_on x
    (isClosed_eq ((mapOfLE hpq).comp (mapOfLE hqr)).continuous
      (mapOfLE _).continuous) (by simp)

/-- Connecting maps are contractions. -/
theorem norm_mapOfLE_le {p q : Seminorm 𝕜 E} (h : p ≤ q) (x : q.LocalBanachSpace) :
    ‖mapOfLE h x‖ ≤ ‖x‖ := by
  refine q.denseRange_toLocalBanachSpace.induction ?_
    (isClosed_le (mapOfLE h).continuous.norm continuous_norm) x
  rintro _ ⟨y, rfl⟩
  simpa using h y

variable {F G : Type*} [AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G]

/-- A seminorm-bounded linear map induces a continuous linear map between the associated
completions. -/
def map (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) : p.LocalBanachSpace →L[𝕜] q.LocalBanachSpace :=
  (LocalSpace.map p q f C h).completion

/-- The induced map on completions agrees with the original map on canonical images. -/
@[simp] theorem map_toLocalBanachSpace (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) (x : E) :
    map p q f C h (p.toLocalBanachSpace x) = q.toLocalBanachSpace (f x) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- A continuous linear map between seminorm completions is determined by its values on
the canonical image of the source. -/
theorem map_unique (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x)
    (g : p.LocalBanachSpace →L[𝕜] q.LocalBanachSpace)
    (hg : ∀ x, g (p.toLocalBanachSpace x) = q.toLocalBanachSpace (f x)) :
    g = map p q f C h := by
  ext z
  exact p.denseRange_toLocalBanachSpace.induction_on z
    (isClosed_eq g.continuous (map p q f C h).continuous)
    (fun x ↦ by rw [hg, map_toLocalBanachSpace])

/-- The map induced on completions is independent of the chosen bound. -/
theorem map_eq (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F)
    (C D : ℝ≥0) (hC : ∀ x, q (f x) ≤ C * p x) (hD : ∀ x, q (f x) ≤ D * p x) :
    map p q f C hC = map p q f D hD := by
  apply map_unique
  exact map_toLocalBanachSpace p q f C hC

/-- The seminorm bound is preserved on the completions. -/
theorem norm_map_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) (z : p.LocalBanachSpace) :
    ‖map p q f C h z‖ ≤ C * ‖z‖ := by
  refine p.denseRange_toLocalBanachSpace.induction_on z
    (isClosed_le (map p q f C h).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro x
  simpa only [map_toLocalBanachSpace, norm_toLocalBanachSpace] using h x

/-- The operator norm of the induced map is bounded by the original seminorm bound. -/
theorem opNorm_map_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (f : E →ₗ[𝕜] F) (C : ℝ≥0) (h : ∀ x, q (f x) ≤ C * p x) :
    ‖map p q f C h‖ ≤ C :=
  (map p q f C h).opNorm_le_bound C.coe_nonneg
    (norm_map_le p q f C h)

/-- The identity linear map induces the identity on a seminorm completion. -/
@[simp] theorem map_id (p : Seminorm 𝕜 E) :
    map p p (LinearMap.id) 1 (by intro x; simp) = .id 𝕜 _ := by
  symm
  apply map_unique
  intro x
  rfl

/-- Induced maps on seminorm completions preserve composition. -/
theorem map_comp (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (r : Seminorm 𝕜 G)
    (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] G) (C D : ℝ≥0)
    (hf : ∀ x, q (f x) ≤ C * p x) (hg : ∀ y, r (g y) ≤ D * q y) :
    (map q r g D hg).comp (map p q f C hf) =
      map p r (g.comp f) (D * C) (fun x ↦ by
        calc r (g (f x)) ≤ D * q (f x) := hg (f x)
          _ ≤ D * (C * p x) := mul_le_mul_of_nonneg_left (hf x) D.coe_nonneg
          _ = (↑(D * C) : ℝ) * p x := by rw [NNReal.coe_mul, mul_assoc]) := by
  apply map_unique
  intro x
  simp

/-- The original contraction connecting two dominated seminorms is the induced completion
map of the identity linear map. -/
theorem mapOfLE_eq_map {p q : Seminorm 𝕜 E} (h : p ≤ q) :
    mapOfLE h = map q p (LinearMap.id) 1
      (fun x ↦ by simpa using h x) := by
  apply map_unique
  exact mapOfLE_toLocalBanachSpace h

/-- Mutually dominating seminorms have continuously linearly equivalent completions;
the equivalence extends the identity on the original module. -/
def equivOfBounds (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) :
    p.LocalBanachSpace ≃L[𝕜] q.LocalBanachSpace := by
  let f := map p q (LinearMap.id) C hpq
  let g := map q p (LinearMap.id) D hqp
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · intro z
    exact p.denseRange_toLocalBanachSpace.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id)
      (fun x ↦ by simp [f, g])
  · intro z
    exact q.denseRange_toLocalBanachSpace.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id)
      (fun x ↦ by simp [f, g])

/-- The equivalence of completions of mutually dominating seminorms preserves canonical
images of the original module. -/
@[simp] theorem equivOfBounds_toLocalBanachSpace (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) (x : E) :
    equivOfBounds p q C D hpq hqp (p.toLocalBanachSpace x) = q.toLocalBanachSpace x :=
  map_toLocalBanachSpace p q (LinearMap.id) C hpq x

/-- The inverse equivalence also preserves canonical images. -/
@[simp] theorem equivOfBounds_symm_toLocalBanachSpace (p q : Seminorm 𝕜 E) (C D : ℝ≥0)
    (hpq : ∀ x, q x ≤ C * p x) (hqp : ∀ x, p x ≤ D * q x) (x : E) :
    (equivOfBounds p q C D hpq hqp).symm (q.toLocalBanachSpace x) = p.toLocalBanachSpace x :=
  map_toLocalBanachSpace q p (LinearMap.id) D hqp x

end LocalBanachSpace

end Seminorm
