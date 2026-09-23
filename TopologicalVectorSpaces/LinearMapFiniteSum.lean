/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences
public import MathlibExtras.LinearAlgebra.LinearMapFiniteSum

/-!
# Sequential continuity of finite coordinate sums

The algebraic construction is in `MathlibExtras.LinearAlgebra.LinearMapFiniteSum`.

## Main statements

* `LinearMap.seqContinuous_finsetSumProj`: a finite sum of sequentially continuous coordinate
  maps is sequentially continuous.
-/

public section

open Set Filter

open scoped Topology Pointwise

section Span

variable {R : Type*} [Semiring R] {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] [AddCommMonoid F] [Module R F]

/-- The map `x ↦ ∑ i ∈ s, f i (x i)` is sequentially continuous if all `f i` are. -/
theorem LinearMap.seqContinuous_finsetSumProj [∀ i, TopologicalSpace (E i)] [TopologicalSpace F]
    [ContinuousAdd F] {f : ∀ i, E i →ₗ[R] F} (hf : ∀ i, SeqContinuous (f i)) (s : Finset ι) :
    SeqContinuous (LinearMap.finsetSumProj f s) := by
  intro x p hx
  have h : Tendsto (fun n ↦ ∑ i ∈ s, f i (x n i)) atTop (𝓝 (∑ i ∈ s, f i (p i))) :=
    tendsto_finsetSum s fun i _ ↦ hf i ((tendsto_pi_nhds.mp hx) i)
  rw [LinearMap.finsetSumProj_apply]
  exact h.congr fun n ↦ (LinearMap.finsetSumProj_apply f s (x n)).symm

end Span
