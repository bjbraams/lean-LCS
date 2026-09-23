/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Rel
public import Mathlib.LinearAlgebra.Prod

/-!
# Images under linear relations

A submodule of `F × E` acts as a relation from `F` to `E`; `SetRel.image G S` consists of
points related to a point of `S`. Relation images preserve convexity, symmetry and balancedness,
and commute with scalar multiplication up to inclusion. A relation with full range sends
absorbent sets to absorbent sets. No topology on either module is needed.

## Main statements

* `Submodule.convex_relImage`, `Submodule.neg_mem_relImage`, `Submodule.balanced_relImage`
* `Submodule.smul_relImage_subset`, `Submodule.absorbent_relImage`

Convexity and scalar multiplication allow a scalar tower; symmetry is stated over a ring,
balancedness over a normed field, and absorbency over a nontrivially normed field.
-/

public section

open Set Filter
open scoped Pointwise

section ScalarTower

variable {R 𝕜 E F : Type*} [Semiring R] [PartialOrder R] [Ring 𝕜] [SMul R 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module R E] [IsScalarTower R 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [Module R F] [IsScalarTower R 𝕜 F]
  (G : Submodule 𝕜 (F × E))

/-- The image of a convex set under a linear relation is convex. -/
theorem Submodule.convex_relImage {S : Set F} (hS : Convex R S) :
    Convex R (SetRel.image (G : Set (F × E)) S) := by
  rintro y₁ ⟨x₁, hx₁, h₁⟩ y₂ ⟨x₂, hx₂, h₂⟩ a b ha hb hab
  refine ⟨a • x₁ + b • x₂, hS hx₁ hx₂ ha hb hab, ?_⟩
  exact G.add_mem (G.smul_of_tower_mem a h₁) (G.smul_of_tower_mem b h₂)

omit [PartialOrder R] in
/-- Scalar multiples of images under a linear relation are contained in the images of the
corresponding scalar multiples. -/
theorem Submodule.smul_relImage_subset (c : R) (S : Set F) :
    c • SetRel.image (G : Set (F × E)) S ⊆ SetRel.image (G : Set (F × E)) (c • S) := by
  rintro _ ⟨y, ⟨x, hx, h⟩, rfl⟩
  exact ⟨c • x, smul_mem_smul_set hx, G.smul_of_tower_mem c h⟩

end ScalarTower

section Ring

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] (G : Submodule 𝕜 (F × E))

/-- The image of a symmetric set under a linear relation is symmetric. -/
theorem Submodule.neg_mem_relImage {S : Set F} (hS : ∀ x ∈ S, -x ∈ S) :
    ∀ y ∈ SetRel.image (G : Set (F × E)) S, -y ∈ SetRel.image (G : Set (F × E)) S := by
  rintro y ⟨x, hx, h⟩
  exact ⟨-x, hS x hx, G.neg_mem h⟩

end Ring

section NormedField

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] (G : Submodule 𝕜 (F × E))

/-- The image of a balanced set under a linear relation is balanced. -/
theorem Submodule.balanced_relImage {S : Set F} (hS : Balanced 𝕜 S) :
    Balanced 𝕜 (SetRel.image (G : Set (F × E)) S) := by
  rintro c hc _ ⟨y, ⟨x, hx, h⟩, rfl⟩
  exact ⟨c • x, hS c hc (smul_mem_smul_set hx), G.smul_mem c h⟩

end NormedField

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] (G : Submodule 𝕜 (F × E))

/-- The image of an absorbent set under a linear relation with full range is absorbent. -/
theorem Submodule.absorbent_relImage {S : Set F} (hS : Absorbent 𝕜 S)
    (hG : Prod.snd '' (G : Set (F × E)) = univ) :
    Absorbent 𝕜 (SetRel.image (G : Set (F × E)) S) := by
  intro y
  obtain ⟨q, hq, rfl⟩ : y ∈ Prod.snd '' (G : Set (F × E)) := hG ▸ mem_univ y
  filter_upwards [hS q.1, Bornology.eventually_ne_cobounded (0 : 𝕜)] with c hc hc0
  obtain ⟨v, hv, hvx⟩ := hc (mem_singleton q.1)
  have hvx' : c • v = q.1 := hvx
  refine singleton_subset_iff.mpr ⟨c⁻¹ • q.2, ⟨v, hv, ?_⟩, by simp only; rw [smul_inv_smul₀ hc0]⟩
  have h := G.smul_mem c⁻¹ hq
  rw [Prod.smul_def, ← hvx', inv_smul_smul₀ hc0] at h
  exact h

end NontriviallyNormedField
