/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Continuity of complex scalar multiplication from the real action

The proof uses the decomposition of a scalar into real and imaginary parts. No local convexity,
separation, or norm on the vector space is needed.

## Main statements

* `RCLike.continuousSMul_iff_continuous_smul_I`: on a real topological vector space with a
  compatible `RCLike` module structure, the scalar action is jointly continuous if and only if
  multiplication by the imaginary unit is continuous.
-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- A compatible real or complex scalar action is jointly continuous if multiplication
by its imaginary unit is continuous. -/
theorem RCLike.continuousSMul_of_continuous_smul_I
    (hI : Continuous fun x : E ↦ (RCLike.I : 𝕜) • x) : ContinuousSMul 𝕜 E := by
  constructor
  have h := ((RCLike.continuous_re.comp continuous_fst).smul
    (continuous_snd : Continuous (Prod.snd : 𝕜 × E → E))).add
    ((RCLike.continuous_im.comp continuous_fst).smul (hI.comp continuous_snd))
  convert h using 1
  funext p
  change p.1 • p.2 = RCLike.re p.1 • p.2 + RCLike.im p.1 • ((RCLike.I : 𝕜) • p.2)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), ← mul_smul, ← add_smul, RCLike.re_add_im]

/-- For a compatible extension of a continuous real scalar action, joint continuity is
equivalent to continuity of multiplication by the imaginary unit. -/
theorem RCLike.continuousSMul_iff_continuous_smul_I :
    ContinuousSMul 𝕜 E ↔ Continuous (fun x : E ↦ (RCLike.I : 𝕜) • x) :=
  ⟨fun _ ↦ continuous_const_smul _, RCLike.continuousSMul_of_continuous_smul_I⟩
