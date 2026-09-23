/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.QuasiBarrelled
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Functionals on products

Strongly bounded families of functionals on a product have a common finite set of active
coordinates. Each functional is the sum of its coordinate restrictions. These results
support permanence of semi-reflexivity and reflexivity under arbitrary products.
The decomposition of a functional known to vanish on the other coordinate axes works
over any nontrivially normed field; the strongly bounded family results use `RCLike`.
-/

public section

open Set Function Filter Bornology
open scoped Topology BigOperators

namespace StrongDual

section General

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]

/-- If a functional vanishes on the other coordinate axes, it is a finite sum of restrictions. -/
theorem apply_eq_sum_of_single_eq_zero (φ : StrongDual 𝕜 (∀ i, E i)) (s : Finset ι)
    (h : ∀ i ∉ s, ∀ x : E i, φ (Pi.single i x) = 0) (x : ∀ i, E i) :
    φ x = ∑ i ∈ s, φ (Pi.single i (x i)) := by
  classical
  have hx : HasSum (fun i ↦ Pi.single i (x i)) x := by
    apply Pi.hasSum.mpr
    intro i
    simpa using (hasSum_single (f := fun j ↦ Pi.single j (x j) i) i
      (fun j hji ↦ Pi.single_eq_of_ne hji.symm (x j)))
  exact (hx.map φ.toAddMonoidHom φ.continuous).unique
    (hasSum_sum_of_ne_finset_zero fun i hi ↦ h i hi (x i))

end General

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι] {E : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]

omit [∀ i, IsTopologicalAddGroup (E i)] in
/-- A strongly bounded family of functionals on a product uses only finitely many coordinates. -/
theorem finite_setOf_exists_apply_single_ne_zero {H : Set (StrongDual 𝕜 (∀ i, E i))}
    (hH : IsVonNBounded 𝕜 H) :
    {i | ∃ φ ∈ H, ∃ x : E i, φ (Pi.single i x) ≠ 0}.Finite := by
  classical
  by_contra hfin
  let a := Set.Infinite.natEmbedding _ hfin
  have hai : Injective (fun n ↦ (a n).val) := Subtype.val_injective.comp a.injective
  choose φ hφ x hx using fun n ↦ (a n).property
  let y (n : ℕ) : ∀ i, E i :=
    (((n + 1 : ℕ) : 𝕜) / φ n (Pi.single (a n).val (x n))) • Pi.single (a n).val (x n)
  have hy (n : ℕ) : φ n (y n) = (n + 1 : ℕ) := by
    simp only [y, map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ (hx n)
  have hB : IsVonNBounded 𝕜 (range y) := by
    rw [isVonNBounded_pi_iff]
    intro i
    by_cases hi : ∃ n, (a n).val = i
    · obtain ⟨n, rfl⟩ := hi
      apply (Set.toFinite ({0, y n (a n).val} : Set (E (a n).val))).isVonNBounded.subset
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      by_cases hmn : m = n
      · subst m; simp
      · have hne : (a m).val ≠ (a n).val := fun h ↦ hmn (hai h)
        simp [y, Pi.single_eq_of_ne hne.symm]
    · apply (isVonNBounded_singleton (𝕜 := 𝕜) (0 : E i)).subset
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      have hne : (a n).val ≠ i := fun h ↦ hi ⟨n, h⟩
      simp [y, Pi.single_eq_of_ne hne.symm]
  obtain ⟨R, hR⟩ := absorbs_iff_norm.mp
    (StrongDual.isBornivorous_polar_of_isVonNBounded hH _ hB)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 R
  obtain ⟨n, hn⟩ := exists_nat_gt ‖c‖
  obtain ⟨z, hz, heq⟩ := hR c hc.le (mem_range_self n)
  have hle : ‖φ n (y n)‖ ≤ ‖c‖ := by
    rw [← heq, map_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hz _ (hφ n)) (norm_nonneg c)).trans_eq (mul_one _)
  rw [hy] at hle
  norm_num only [RCLike.norm_natCast] at hle
  have : (n : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
  linarith

omit [∀ i, IsTopologicalAddGroup (E i)] in
/-- A bounded family of product functionals has a common finite coordinate decomposition. -/
theorem exists_finset_apply_eq_sum {H : Set (StrongDual 𝕜 (∀ i, E i))}
    (hH : IsVonNBounded 𝕜 H) : ∃ s : Finset ι, ∀ φ ∈ H, ∀ x,
      φ x = ∑ i ∈ s, φ (Pi.single i (x i)) := by
  classical
  let s := (finite_setOf_exists_apply_single_ne_zero hH).toFinset
  refine ⟨s, fun φ hφ x ↦ φ.apply_eq_sum_of_single_eq_zero s ?_ x⟩
  intro i hi y
  by_contra hne
  exact hi ((finite_setOf_exists_apply_single_ne_zero hH).mem_toFinset.mpr ⟨φ, hφ, y, hne⟩)

/-- On a product of quasi-barrelled spaces, strongly bounded families of
functionals are equicontinuous. -/
theorem equicontinuous_of_isVonNBounded_pi
    [∀ i, Module ℝ (E i)] [∀ i, IsScalarTower ℝ 𝕜 (E i)]
    [∀ i, QuasiBarrelledSpace 𝕜 (E i)]
    {H : Set (StrongDual 𝕜 (∀ i, E i))} (hH : IsVonNBounded 𝕜 H) :
    Equicontinuous ((↑) : H → (∀ i, E i) → 𝕜) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_apply_eq_sum hH
  have hc (i : ι) : Continuous (fun x : ∀ i, E i ↦
      UniformFun.ofFun (fun φ : H ↦ φ.val (Pi.single i (x i)))) := by
    let r := (ContinuousLinearMap.single 𝕜 E i).transpose
    have he := QuasiBarrelledSpace.equicontinuous_of_isVonNBounded (hH.image r)
    have he' := he.comp (fun φ : H ↦ (⟨r φ.val, ⟨φ.val, φ.property, rfl⟩⟩ : r '' H))
    exact (equicontinuous_iff_continuous.mp he').comp (continuous_apply i)
  rw [equicontinuous_iff_continuous]
  convert continuous_finsetSum s (fun i _ ↦ hc i) using 1
  funext x
  change UniformFun.ofFun (fun φ : H ↦ φ.val x) = _
  calc
    _ = UniformFun.ofFun (∑ i ∈ s, fun φ : H ↦ φ.val (Pi.single i (x i))) := by
      apply congrArg UniformFun.ofFun
      funext φ
      simpa only [Finset.sum_apply] using hs φ.val φ.property x
    _ = _ := UniformFun.ofFun_sum s

end StrongDual

/-- Arbitrary products of quasi-barrelled locally convex spaces are quasi-barrelled. -/
instance QuasiBarrelledSpace.pi {𝕜 ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, QuasiBarrelledSpace 𝕜 (E i)] :
    QuasiBarrelledSpace 𝕜 (∀ i, E i) := by
  classical
  exact QuasiBarrelledSpace.of_forall_equicontinuous
    (fun _ h ↦ StrongDual.equicontinuous_of_isVonNBounded_pi h)
