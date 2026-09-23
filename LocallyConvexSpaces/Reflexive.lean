/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LocallyConvexSpaces.MackeyArens
public import LocallyConvexSpaces.PolarTopology
public import LocallyConvexSpaces.Transpose
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The bidual, semi-reflexive and reflexive spaces

The *bidual* of a topological vector space `E` is the dual of its strong dual. Every point of
`E` defines an element of the bidual by evaluation. The space `E` is *semi-reflexive* if this
canonical map is surjective, and *reflexive* if moreover it induces the topology of `E` from
the strong topology of the bidual. For a Hausdorff locally convex space the canonical map is
also injective, so this is equivalent to being a homeomorphism onto the bidual.

Semi-reflexivity is a statement about the pairing of `E'` and `E`: it says that the strong
topology `β(E', E)` on the dual is compatible with this pairing. By the Mackey–Arens theorem this
holds if and only if the strong topology is coarser than the Mackey topology `τ(E', E)`.

## Main definitions

* `StrongDual.inclusionInDoubleDual 𝕜 E` (also named `inclusionInBidual`): the canonical linear map
  of `E` into its bidual.
* `SemiReflexiveSpace 𝕜 E`, `ReflexiveSpace 𝕜 E`.

## Main statements

* `StrongDual.inclusionInDoubleDual_injective_of_separatingDual`: injectivity when the
  continuous dual separates points, over a nontrivially normed field.
* `StrongDual.inclusionInDoubleDual_injective`: the canonical map is injective for a Hausdorff
  locally convex space.
* `ReflexiveSpace.continuous_inclusionInDoubleDual`: the canonical bidual map is continuous
  under reflexivity.
* `SemiReflexiveSpace.strongDual_of_continuous_inclusionInDoubleDual`: semi-reflexivity and
  continuity of the bidual map imply semi-reflexivity of the strong dual.
* `semiReflexiveSpace_iff_isCompatible`, `semiReflexiveSpace_iff_mackeyTopology_le`.
* `semiReflexiveSpace_iff_forall_isVonNBounded`: a Hausdorff locally convex space is
  semi-reflexive if and only if every bounded set lies in a weakly compact convex balanced set.

The characterizations of reflexive spaces (semi-reflexive and barrelled; barrelled Montel
spaces) are in `LocallyConvexSpaces.QuasiBarrelled`.

The reflexivity of the strong dual is proved in `LocallyConvexSpaces.QuasiBarrelled`.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], IV §5
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987], IV §2.2–2.3
* [G. Köthe, *Topological Vector Spaces I*][kothe1983], §23.3, §23.5

## Tags

bidual, semi-reflexive, reflexive, Mackey topology
-/

public section

open Set Function Filter

open scoped Topology

section Defs

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- The canonical linear map of a topological vector space into its bidual: a point `x` is sent
to the evaluation `φ ↦ φ x`, which is continuous on the strong dual. -/
@[expose]
def StrongDual.inclusionInDoubleDual : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) where
  toFun x :=
    { toFun := fun φ ↦ φ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_eval_const x }
  map_add' x y := ContinuousLinearMap.ext fun φ ↦ map_add φ x y
  map_smul' c x := ContinuousLinearMap.ext fun φ ↦ map_smul φ c x

/-- Compatibility name for `StrongDual.inclusionInDoubleDual`. -/
abbrev StrongDual.inclusionInBidual := StrongDual.inclusionInDoubleDual 𝕜 E

variable {𝕜 E} in
/-- The canonical map into the bidual is evaluation. -/
@[simp]
theorem StrongDual.inclusionInDoubleDual_apply (x : E) (φ : StrongDual 𝕜 E) :
    StrongDual.inclusionInDoubleDual 𝕜 E x φ = φ x :=
  rfl

/-- Compatibility name for the evaluation formula of the canonical bidual map. -/
alias StrongDual.inclusionInBidual_apply := StrongDual.inclusionInDoubleDual_apply

/-- The canonical bidual map is injective whenever the continuous dual separates points. -/
theorem StrongDual.inclusionInDoubleDual_injective_of_separatingDual [SeparatingDual 𝕜 E] :
    Injective (StrongDual.inclusionInDoubleDual 𝕜 E) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun φ ↦
    congrArg (fun ψ : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ ψ φ) hx

/-- A topological vector space is **semi-reflexive** if every continuous linear functional on
its strong dual is the evaluation at a point of the space. -/
class SemiReflexiveSpace : Prop where
  /-- The canonical map into the bidual is surjective. -/
  surjective_inclusionInDoubleDual : Surjective (StrongDual.inclusionInDoubleDual 𝕜 E)

/-- A topological vector space is **reflexive** if it is semi-reflexive and the canonical map
into the bidual, with its strong topology, is inducing. -/
class ReflexiveSpace : Prop extends SemiReflexiveSpace 𝕜 E where
  /-- The canonical map into the bidual is inducing. -/
  isInducing_inclusionInDoubleDual : Topology.IsInducing (StrongDual.inclusionInDoubleDual 𝕜 E)

/-- A reflexive space is semi-reflexive. -/
add_decl_doc ReflexiveSpace.toSemiReflexiveSpace

/-- Compatibility accessor for surjectivity of the canonical bidual map. -/
alias SemiReflexiveSpace.surjective_inclusionInBidual :=
  SemiReflexiveSpace.surjective_inclusionInDoubleDual

/-- Compatibility accessor for the inducing property of the canonical bidual map. -/
alias ReflexiveSpace.isInducing_inclusionInBidual :=
  ReflexiveSpace.isInducing_inclusionInDoubleDual

/-- The canonical map of a reflexive space into its strong bidual is continuous. -/
theorem ReflexiveSpace.continuous_inclusionInDoubleDual [ReflexiveSpace 𝕜 E] :
    Continuous (StrongDual.inclusionInDoubleDual 𝕜 E) :=
  ReflexiveSpace.isInducing_inclusionInDoubleDual.continuous

/-- If a semi-reflexive space has a continuous canonical bidual map, its strong dual is
semi-reflexive. The proof evaluates a functional on the triple dual along the bidual map. -/
theorem SemiReflexiveSpace.strongDual_of_continuous_inclusionInDoubleDual
    [SemiReflexiveSpace 𝕜 E] (h : Continuous (StrongDual.inclusionInDoubleDual 𝕜 E)) :
    SemiReflexiveSpace 𝕜 (StrongDual 𝕜 E) := by
  let J : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
    { StrongDual.inclusionInDoubleDual 𝕜 E with cont := h }
  refine ⟨fun Ψ ↦ ⟨Ψ.comp J, ?_⟩⟩
  ext ψ
  obtain ⟨x, rfl⟩ := SemiReflexiveSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := E) ψ
  rfl

end Defs

/-- On a seminormed space the general bidual map is the underlying linear map of Mathlib's
bounded inclusion in the double dual. -/
theorem StrongDual.inclusionInDoubleDual_eq_normedSpace (𝕜 E : Type*)
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    StrongDual.inclusionInDoubleDual 𝕜 E = (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap := by
  ext x φ
  rfl


variable (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousSMul 𝕜 E]

/-- The canonical map of a Hausdorff locally convex space into its bidual is injective. -/
theorem StrongDual.inclusionInDoubleDual_injective [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T1Space E] :
    Injective (StrongDual.inclusionInDoubleDual 𝕜 E) := by
  let : SeparatingDual 𝕜 E := SeparatingDual.of_locallyConvexSpace_real 𝕜 E
  exact StrongDual.inclusionInDoubleDual_injective_of_separatingDual 𝕜 E

/-- Compatibility name for injectivity of the bidual map on a Hausdorff locally convex space. -/
alias StrongDual.inclusionInBidual_injective := StrongDual.inclusionInDoubleDual_injective

/-- A space is semi-reflexive if and only if the strong topology on its dual is compatible with
the pairing of the dual and the space. -/
theorem semiReflexiveSpace_iff_isCompatible :
    SemiReflexiveSpace 𝕜 E ↔ (topDualPairing 𝕜 E).IsCompatible := by
  constructor
  · intro h f
    refine ⟨fun hf ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
    · obtain ⟨x, hx⟩ := h.surjective_inclusionInDoubleDual ⟨f, hf⟩
      exact ⟨x, fun φ ↦ (congrArg (fun ψ : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ ψ φ) hx).symm⟩
    · have hfx : (f : StrongDual 𝕜 E → 𝕜) = fun φ ↦ φ x := funext hx
      rw [hfx]
      exact continuous_eval_const x
  · intro h
    refine ⟨fun ψ ↦ ?_⟩
    obtain ⟨x, hx⟩ := (h ψ.toLinearMap).mp ψ.continuous
    exact ⟨x, ContinuousLinearMap.ext fun φ ↦ (hx φ).symm⟩

/-- A space is semi-reflexive if and only if the strong topology `β(E', E)` on its dual is
coarser than the Mackey topology `τ(E', E)`; this is the Mackey–Arens theorem for the pairing of
the dual and the space. -/
theorem semiReflexiveSpace_iff_mackeyTopology_le [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    SemiReflexiveSpace 𝕜 E ↔ (topDualPairing 𝕜 E).mackeyTopology ≤
      (inferInstance : TopologicalSpace (StrongDual 𝕜 E)) := by
  rw [semiReflexiveSpace_iff_isCompatible, LinearMap.isCompatible_iff_mackeyTopology_le]
  exact and_iff_right fun x ↦ continuous_eval_const x

section Bounded

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]

omit [IsTopologicalAddGroup E] in
/-- If every bounded subset of `E` lies in a weakly compact, convex, balanced set, then `E` is
semi-reflexive. -/
theorem SemiReflexiveSpace.of_forall_isVonNBounded
    (h : ∀ S : Set E, Bornology.IsVonNBounded 𝕜 S →
      ∃ K ∈ (topDualPairing 𝕜 E).mackeyFamily, toWeakSpace 𝕜 E '' S ⊆ K) :
    SemiReflexiveSpace 𝕜 E := by
  rw [semiReflexiveSpace_iff_mackeyTopology_le]
  refine TopologicalSpace.le_of_nhds_zero_le
    (LinearMap.polarTopology.isTopologicalAddGroup _ _) inferInstance fun U hU ↦ ?_
  obtain ⟨S, hS, hSU⟩ := StrongDual.hasBasis_nhds_zero_polar.mem_iff.mp hU
  obtain ⟨K, hK, hSK⟩ := h S hS
  refine mem_of_superset (LinearMap.polarTopology.polar_mem_nhds_zero _ _
    (LinearMap.mackeyFamily_nonempty _) (LinearMap.directedOn_mackeyFamily _) hK)
    (Subset.trans ?_ hSU)
  exact fun φ hφ x hx ↦ hφ _ (hSK ⟨x, hx, rfl⟩)

variable [LocallyConvexSpace ℝ E] [T1Space E]

/-- In a semi-reflexive Hausdorff locally convex space every bounded set lies in a weakly
compact, convex, balanced set. -/
theorem SemiReflexiveSpace.exists_mem_mackeyFamily_subset [SemiReflexiveSpace 𝕜 E] {S : Set E}
    (hS : Bornology.IsVonNBounded 𝕜 S) :
    ∃ K ∈ (topDualPairing 𝕜 E).mackeyFamily, toWeakSpace 𝕜 E '' S ⊆ K := by
  have hle := (semiReflexiveSpace_iff_mackeyTopology_le 𝕜 E).mp inferInstance
  -- The polar of `S` is a neighbourhood of zero for the Mackey topology of the dual.
  have hpolar : StrongDual.polar 𝕜 S ∈ @nhds _ (topDualPairing 𝕜 E).mackeyTopology 0 :=
    nhds_mono hle (StrongDual.hasBasis_nhds_zero_polar.mem_of_mem hS)
  obtain ⟨K₀, hK₀, hK₀S⟩ :=
    (LinearMap.mackeyTopology_hasBasis_nhds_zero _).mem_iff.mp hpolar
  obtain ⟨K, hK, hK₀K, h0K⟩ := LinearMap.directedOn_mackeyFamily _ K₀ hK₀ {0}
    ⟨isCompact_singleton, convex_singleton 0, balanced_zero⟩
  refine ⟨K, hK, ?_⟩
  -- The weak topology is Hausdorff, so `K` is weakly closed and equal to its bipolar.
  have hinj : Injective (topDualPairing 𝕜 E).flip := fun x y hxy ↦
    StrongDual.inclusionInDoubleDual_injective 𝕜 E (ContinuousLinearMap.ext fun φ ↦
      LinearMap.congr_fun hxy φ)
  have : T2Space (WeakBilin (topDualPairing 𝕜 E).flip) := (WeakBilin.isEmbedding hinj).t2Space
  have hbip := (topDualPairing 𝕜 E).flip.flip_polar_polar_subset (s := K) Subset.rfl hK.2.1
    hK.2.2 hK.1.isClosed ⟨0, h0K rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  refine hbip fun φ hφ ↦ ?_
  have hφS : φ ∈ StrongDual.polar 𝕜 S :=
    hK₀S ((topDualPairing 𝕜 E).flip.polar_antitone hK₀K hφ)
  exact hφS x hx

/-- A Hausdorff locally convex space is **semi-reflexive if and only if every bounded set lies
in a weakly compact, convex, balanced set**; in particular if and only if its bounded sets are
relatively weakly compact. -/
theorem semiReflexiveSpace_iff_forall_isVonNBounded :
    SemiReflexiveSpace 𝕜 E ↔ ∀ S : Set E, Bornology.IsVonNBounded 𝕜 S →
      ∃ K ∈ (topDualPairing 𝕜 E).mackeyFamily, toWeakSpace 𝕜 E '' S ⊆ K :=
  ⟨fun _ _ hS ↦ SemiReflexiveSpace.exists_mem_mackeyFamily_subset 𝕜 E hS,
    SemiReflexiveSpace.of_forall_isVonNBounded 𝕜 E⟩

end Bounded
