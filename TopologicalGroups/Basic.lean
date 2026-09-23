/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Baire.Lemmas

/-!
# General lemmas on topological groups

Lemmas on topological groups that are used in this library and belong with existing files of
Mathlib.

## Main statements

* `TopologicalSpace.le_of_nhds_zero_le`: two group topologies are comparable as soon as their
  neighbourhood filters of zero are.
* `IsTopologicalAddGroup.firstCountableTopology_of_isCountablyGenerated_nhds_zero`: a topological
  group is first-countable as soon as the neighbourhood filter of zero is countably generated;
  `IsTopologicalAddGroup.firstCountableTopology_iff` is the equivalence.

* `exists_mem_closure_image_div_mem_nhds_one` and its additive form: a non-meagre set
  has a translate whose closure is a neighbourhood of the identity.

## Tags

topological group
-/

public section

open Filter

open scoped Topology

/-- Two group topologies are comparable as soon as their neighbourhood filters of the identity are.
-/
@[to_additive TopologicalSpace.le_of_nhds_zero_le /-- Two group topologies are comparable as soon as
their neighbourhood filters of zero are. -/]
theorem TopologicalSpace.le_of_nhds_one_le {G : Type*} [Group G] {t₁ t₂ : TopologicalSpace G}
    (h₁ : @IsTopologicalGroup G t₁ _) (h₂ : @IsTopologicalGroup G t₂ _)
    (h : @nhds G t₁ 1 ≤ @nhds G t₂ 1) : t₁ ≤ t₂ :=
  continuous_id_iff_le.mp (@continuous_of_continuousAt_one G t₁ _ h₁ G (G →* G) _ t₂
    h₂.toContinuousMul _ _ (MonoidHom.id G) (tendsto_id'.mpr h))

/-- A topological group in which the neighbourhood filter of the identity is countably generated
is first-countable. -/
@[to_additive /-- A topological additive group in which the neighbourhood filter of zero is
countably generated is first-countable. -/]
theorem IsTopologicalGroup.firstCountableTopology_of_isCountablyGenerated_nhds_one {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : (𝓝 (1 : G)).IsCountablyGenerated) :
    FirstCountableTopology G :=
  ⟨fun x ↦ map_mul_left_nhds_one x ▸ inferInstance⟩

/-- A topological group is first-countable if and only if the neighbourhood filter of the
identity is countably generated. -/
@[to_additive /-- A topological additive group is first-countable if and only if the
neighbourhood filter of zero is countably generated. -/]
theorem IsTopologicalGroup.firstCountableTopology_iff {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    FirstCountableTopology G ↔ (𝓝 (1 : G)).IsCountablyGenerated :=
  ⟨fun _ ↦ inferInstance,
    IsTopologicalGroup.firstCountableTopology_of_isCountablyGenerated_nhds_one⟩

section Baire

open Set

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

/-- A non-meagre subset `S` of a topological group contains a point `a` such that the closure
of the translate `S / a` is a neighbourhood of the identity. -/
@[to_additive /-- A non-meagre subset `S` of a topological group contains a point `a` such that the
closure of the translate `S - a` is a neighbourhood of zero. -/]
theorem exists_mem_closure_image_div_mem_nhds_one {S : Set E} (hS : ¬IsMeagre S) :
    ∃ a ∈ S, closure ((fun w ↦ w / a) '' S) ∈ 𝓝 (1 : E) := by
  have hne : (interior (closure S)).Nonempty := by
    by_contra h
    exact hS (IsNowhereDense.isMeagre (not_nonempty_iff_eq_empty.mp h))
  obtain ⟨x, hx⟩ := hne
  -- The open set `interior (closure S)` meets `S`.
  obtain ⟨a, haint, haS⟩ :=
    mem_closure_iff.mp (interior_subset hx) _ isOpen_interior hx
  refine ⟨a, haS, ?_⟩
  have hc : ContinuousAt (fun v : E ↦ v * a) 1 := by fun_prop
  have hpre : (fun v : E ↦ v * a) ⁻¹' closure S ∈ 𝓝 (1 : E) :=
    hc.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.mp haint)
  refine mem_of_superset hpre fun v hv ↦ ?_
  have hsub : Continuous fun w : E ↦ w / a := by fun_prop
  exact image_closure_subset_closure_image hsub ⟨v * a, hv, mul_div_cancel_right v a⟩

end Baire
