/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Group.Graph
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import TopologicalGroups.Series

/-!
# Nearly open relations and maps on complete first-countable groups

This file contains the successive approximation argument that underlies the open mapping and
closed graph theorems, in a form that does not refer to scalar multiplication, to a Baire
category argument, or to convexity. It concerns commutative topological groups only.

Let `G` be a complete, first-countable commutative topological group, `H` a commutative topological
group, and `R` a closed subgroup of `G × H`, viewed as a relation. Say that `R` is *nearly open* if
for every neighbourhood `U` of the identity in `G` the closure of the image `R[U]` is a
neighbourhood of the identity in `H`. The main result says that then `R[U]` itself is a
neighbourhood of the identity, for every such `U`. No separation, completeness or countability
assumption is made on `H`.

Applied to the graph of a homomorphism `f : G →* H` this says that a nearly open homomorphism
with closed graph is open. Applied to the transposed graph of a homomorphism `g : H →* G` it
says that a nearly continuous homomorphism with closed graph is continuous. The second form is
the one that is needed for closed graph theorems in which the domain is not complete, such as
the closed graph theorem for a barrelled domain.

## Main statements

* `Subgroup.closure_image_subset_image`: the quantitative form, for a basis `V n` of
  neighbourhoods of the identity with `V (n + 1) * V (n + 1) ⊆ V n` and `closure (V (n + 1)) ⊆ V n`:
  `closure (R[V (n + 2)]) ⊆ R[V n]`.
* `Subgroup.image_mem_nhds_one`: a closed nearly open relation is open at the identity.
* `MonoidHom.isOpenMap_of_isClosed_graph_of_nearlyOpen`: a nearly open homomorphism with closed
  graph, defined on a complete first-countable group, is an open map.
* `MonoidHom.isOpenMap_of_continuous_of_nearlyOpen`: the same for a continuous homomorphism into a
  Hausdorff group.
* `MonoidHom.continuous_of_isClosed_graph_of_nearlyContinuous`: a nearly continuous homomorphism
  with closed graph, with values in a complete first-countable group, is continuous.

## Implementation notes

The primary statements are multiplicative and commutative; `to_additive` generates their
additive counterparts for applications to topological vector spaces. Extending the proof to
noncommutative groups would require a separate ordered-product argument.

## Relation to work outside Mathlib

Mathlib PR #41166 (K. H. Wilson, draft, "generalize the open mapping theorem"), new file
`Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, proves the open mapping theorem
`ContinuousLinearMap.isOpenMap` for complete first-countable topological vector spaces. The
successive approximation in its proof is the same classical argument as in
`Subgroup.closure_image_subset_image` below, specialized to the graph of a continuous linear
map into a Hausdorff space, and with near openness derived from the Baire property. The proof
below was written with that proof at hand and follows its organization (the recursive
definition of the residuals and the telescoping of the partial products). What is added here is
the formulation for closed relations, which replaces "continuous into a Hausdorff space" by
"closed graph" and yields the closed graph form, and the separation of near openness as a
hypothesis. The two auxiliary lemmas in the first section are copies of lemmas of PRs #40983
and #41166; see the notes at those lemmas.

## References

* [J. L. Kelley and I. Namioka, *Linear Topological Spaces*][kelley1963], 11.3
* [G. Köthe, *Topological Vector Spaces II*][kothe1979], §34
* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], III §2

## Tags

open mapping theorem, closed graph theorem, nearly open, nearly continuous
-/

public section

open Set Filter Function

open scoped Topology Uniformity Pointwise SetRel

section Duplicates

/-- An antitone basis of neighbourhoods of the identity in a topological group has an antitone
subbasis `w` with `w (n + 1) * w (n + 1) ⊆ w n` and `closure (w (n + 1)) ⊆ w n`.

Duplicate: this is `Filter.HasAntitoneBasis.exists_subbasis_mul_closure_subset` of Mathlib PR #40983
(K. H. Wilson), file `Mathlib/Topology/Algebra/Group/Pointwise.lean`. Statement and proof are copied
from that PR. Delete this copy once that PR is in the pinned Mathlib. -/
@[to_additive /-- An antitone basis of neighbourhoods of zero in a topological group has an antitone
subbasis `w` with `w (n + 1) + w (n + 1) ⊆ w n` and `closure (w (n + 1)) ⊆ w n`.

Duplicate: this is the additive form of `Filter.HasAntitoneBasis.exists_subbasis_mul_closure_subset`
of Mathlib PR #40983 (K. H. Wilson), file `Mathlib/Topology/Algebra/Group/Pointwise.lean`. Statement
and proof are copied from that PR. Delete this copy once that PR is in the pinned Mathlib. -/]
theorem Filter.HasAntitoneBasis.exists_subbasis_mul_closure_subset {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {v : ℕ → Set G}
    (hv : (𝓝 (1 : G)).HasAntitoneBasis v) :
    ∃ φ : ℕ → ℕ, (𝓝 (1 : G)).HasAntitoneBasis (v ∘ φ) ∧
      ∀ n, (v ∘ φ) (n + 1) * (v ∘ φ) (n + 1) ⊆ (v ∘ φ) n ∧
        closure ((v ∘ φ) (n + 1)) ⊆ (v ∘ φ) n := by
  obtain ⟨φ, -, hφ_add, hφ_basis⟩ := hv.subbasis_with_rel
    (r := fun i j ↦ v j * v j ⊆ v i) fun m ↦ by
      obtain ⟨W, hW_open, hW_zero, hW_add⟩ := exists_open_nhds_one_mul_subset (hv.mem m)
      obtain ⟨N, hN⟩ := hv.mem_iff.mp (hW_open.mem_nhds hW_zero)
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      exact (mul_subset_mul ((hv.antitone hM).trans hN) ((hv.antitone hM).trans hN)).trans hW_add
  exact ⟨φ, hφ_basis, fun n ↦ ⟨hφ_add n.lt_succ_self,
    (closure_subset_mul_self_of_mem_nhds_one (hφ_basis.mem (n + 1))).trans
      (hφ_add n.lt_succ_self)⟩⟩

/-- If the uniformity has an antitone basis `s` with `s (n + 1) ○ s (n + 1) ⊆ s n`, then a
sequence `u` with `(u n, u (n + 1)) ∈ s (n + 1)` for all `n` is a Cauchy sequence.

Duplicate: this is `Filter.HasAntitoneBasis.cauchySeq_of_succ` of Mathlib PR #41166
(K. H. Wilson), file `Mathlib/Topology/UniformSpace/Cauchy.lean`. Statement and proof are
copied from that PR. Delete this copy once that PR is in the pinned Mathlib. -/
theorem Filter.HasAntitoneBasis.cauchySeq_of_succ {α : Type*} [UniformSpace α]
    {s : ℕ → SetRel α α} (h : (𝓤 α).HasAntitoneBasis s)
    (hcomp : ∀ n, s (n + 1) ○ s (n + 1) ⊆ s n) {u : ℕ → α}
    (hu : ∀ n, (u n, u (n + 1)) ∈ s (n + 1)) : CauchySeq u := by
  have key : ∀ m n, m ≤ n → (u m, u n) ∈ s m := fun m n hmn ↦
    Nat.decreasingInduction' (fun k _ _ hk ↦ hcomp k ⟨u (k + 1), hu k, hk⟩) hmn
      (refl_mem_uniformity (h.mem n))
  rw [h.toHasBasis.cauchySeq_iff]
  intro i _
  obtain ⟨t, ht_mem, ht_symm, ht_comp⟩ := comp_symm_of_uniformity (h.mem i)
  have ht_sub : t ⊆ s i := fun p hp ↦ ht_comp ⟨p.1, refl_mem_uniformity ht_mem, hp⟩
  obtain ⟨j, hj⟩ := h.mem_iff.1 ht_mem
  refine ⟨max i j, fun m hm n hn ↦ ?_⟩
  rcases le_total m n with hmn | hnm
  · exact h.antitone ((le_max_left i j).trans hm) (key m n hmn)
  · exact ht_sub (ht_symm (hj (h.antitone ((le_max_right i j).trans hn) (key n m hnm))))

end Duplicates

variable {G H : Type*} [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [UniformSpace G] [IsUniformGroup G] [CompleteSpace G] in
/-- The approximation step of the open mapping and closed graph theorems. Let `R` be a subgroup
of `G × H` and let the closure of `R[T]` be a neighbourhood of the identity. Then a point `w` of the
closure of `R[S]` is approximated by some `z` with `(x, z) ∈ R` and `x ∈ S` in such a way that
the residual `w / z` lies in the closure of `R[T]`. -/
@[to_additive /-- The approximation step of the open mapping and closed graph theorems. Let `R` be a
subgroup of `G × H` and let the closure of `R[T]` be a neighbourhood of zero. Then a point `w` of
the closure of `R[S]` is approximated by some `z` with `(x, z) ∈ R` and `x ∈ S` in such a way that
the residual `w - z` lies in the closure of `R[T]`. -/]
private theorem Subgroup.exists_div_mem_closure_image (R : Subgroup (G × H)) {S T : Set G}
    (hT : _root_.closure (SetRel.image (R : Set (G × H)) T) ∈ 𝓝 (1 : H)) {w : H}
    (hw : w ∈ _root_.closure (SetRel.image (R : Set (G × H)) S)) :
    ∃ x z, x ∈ S ∧ (x, z) ∈ R ∧ w / z ∈ _root_.closure (SetRel.image (R : Set (G × H)) T) := by
  have : {p : H | w / p ∈ _root_.closure (SetRel.image (R : Set (G × H)) T)} ∈ 𝓝 w := by
    apply ContinuousAt.preimage_mem_nhds (by fun_prop)
    simpa using hT
  obtain ⟨p, hp, x, hx, hxp⟩ := mem_closure_iff_nhds.mp hw _ this
  exact ⟨x, p, hx, hxp, hp⟩

/-- The successive approximation argument of the open mapping and closed graph theorems.

Let `R` be a closed subgroup of `G × H`, with `G` complete, and let `V` be an antitone basis of
neighbourhoods of the identity in `G` with `V (n + 1) * V (n + 1) ⊆ V n` and
`closure (V (n + 1)) ⊆ V n`. If the closure of each image `R[V n]` is a neighbourhood of the
identity then `closure (R[V (n + 2)]) ⊆ R[V n]`.

The organization of the proof follows that of `ContinuousLinearMap.isOpenMap` in Mathlib PR #41166
(K. H. Wilson), file `Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, which is the special case
in which `R` is the graph of a continuous linear map into a Hausdorff space. The proof is adapted
from that source. Delete this adapted proof once the PR is in pinned Mathlib. Preserve the stronger
relation theorem by migrating it upstream or replacing its proof using the general upstream
infrastructure; the specialized open mapping theorem alone does not imply this relation theorem. -/
@[to_additive /-- The successive approximation argument of the open mapping and closed graph
theorems.

Let `R` be a closed subgroup of `G × H`, with `G` complete, and let `V` be an antitone basis of
neighbourhoods of zero in `G` with `V (n + 1) + V (n + 1) ⊆ V n` and `closure (V (n + 1)) ⊆ V n`. If
the closure of each image `R[V n]` is a neighbourhood of zero then
`closure (R[V (n + 2)]) ⊆ R[V n]`.

The organization of the proof follows that of `ContinuousLinearMap.isOpenMap` in Mathlib PR #41166
(K. H. Wilson), file `Mathlib/Analysis/Normed/Operator/OpenMapping.lean`, which is the special case
in which `R` is the graph of a continuous linear map into a Hausdorff space. The proof is adapted
from that source. Delete this adapted proof once the PR is in pinned Mathlib. Preserve the stronger
relation theorem by migrating it upstream or replacing its proof using the general upstream
infrastructure; the specialized open mapping theorem alone does not imply this relation theorem. -/]
theorem Subgroup.closure_image_subset_image (R : Subgroup (G × H))
    (hR : IsClosed (R : Set (G × H))) {V : ℕ → Set G} (hV : (𝓝 (1 : G)).HasAntitoneBasis V)
    (hadd : ∀ n, V (n + 1) * V (n + 1) ⊆ V n) (hcl : ∀ n, _root_.closure (V (n + 1)) ⊆ V n)
    (near : ∀ n, _root_.closure (SetRel.image (R : Set (G × H)) (V n)) ∈ 𝓝 (1 : H)) (n : ℕ) :
    _root_.closure (SetRel.image (R : Set (G × H)) (V (n + 2))) ⊆
      SetRel.image (R : Set (G × H)) (V n) := by
  -- Step 1: the approximation step `Subgroup.exists_div_mem_closure_image`.
  have step (m : ℕ) (w : H) (hw : w ∈ _root_.closure (SetRel.image (R : Set (G × H)) (V m))) :
      ∃ x z, x ∈ V m ∧ (x, z) ∈ R ∧
        w / z ∈ _root_.closure (SetRel.image (R : Set (G × H)) (V (m + 1))) :=
    R.exists_div_mem_closure_image (near (m + 1)) hw
  intro y hy
  -- Step 2: iterate. `yᵢ` are the residuals, `xᵢ` the corrections, `sᵢ` their partial products.
  choose! xg zg hxg hRg hres using step
  let yᵢ : ℕ → H := fun k ↦ k.recOn y (fun m ym ↦ ym / zg (n + 2 + m) ym)
  let xᵢ : ℕ → G := fun m ↦ xg (n + 2 + m) (yᵢ m)
  let sᵢ : ℕ → G := fun m ↦ (Finset.range m).prod xᵢ
  have hyᵢ (k : ℕ) : yᵢ k ∈ _root_.closure (SetRel.image (R : Set (G × H)) (V (n + 2 + k))) := by
    induction k with
    | zero => exact hy
    | succ k ih => exact hres (n + 2 + k) (yᵢ k) ih
  have hxᵢ (k : ℕ) : xᵢ k ∈ V (n + 2 + k) := hxg (n + 2 + k) (yᵢ k) (hyᵢ k)
  -- The partial products are related to `y` minus the residual.
  have hsR (m : ℕ) : (sᵢ m, y / yᵢ m) ∈ R := by
    induction m with
    | zero =>
      have h0 : (sᵢ 0, y / yᵢ 0) = (1 : G × H) := by simp [sᵢ, yᵢ]
      rw [h0]
      exact R.one_mem
    | succ m ih =>
      have h := R.mul_mem ih (hRg (n + 2 + m) (yᵢ m) (hyᵢ m))
      have e : y / yᵢ (m + 1) = y / yᵢ m * zg (n + 2 + m) (yᵢ m) := by
        change y / (yᵢ m / zg (n + 2 + m) (yᵢ m)) = _
        simp only [div_div_eq_mul_div, div_mul_eq_mul_div]
      rw [e]
      simpa [sᵢ, xᵢ, Finset.prod_range_succ] using h
  -- Step 3: the partial products form a Cauchy sequence, hence converge to some `x`.
  have hcauchy : CauchySeq sᵢ := by
    have hunif : (𝓤 G).HasAntitoneBasis fun i ↦ {p : G × G | p.2 / p.1 ∈ V i} :=
      ⟨hV.toHasBasis.uniformity_of_nhds_one, fun _ _ hij _ hp ↦ hV.antitone hij hp⟩
    refine hunif.cauchySeq_of_succ (fun k ↦ ?_) (fun k ↦ ?_)
    · intro ⟨a, c⟩ ⟨b, hab, hbc⟩
      simpa using hadd k (Set.mul_mem_mul hbc hab)
    · simpa [sᵢ, Finset.prod_range_succ] using hV.antitone (by lia) (hxᵢ k)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- Step 4: `x ∈ V n`, because all partial products lie in `V (n + 1)`.
  have hxV : x ∈ V n := by
    refine hcl n (mem_closure_of_tendsto hx (Eventually.of_forall fun m ↦ ?_))
    have h := Finset.prod_range_add_mem_of_mul_subset (V := fun k ↦ V (n + 1 + k))
      (fun k ↦ mem_of_mem_nhds (hV.mem _)) (fun k ↦ hadd _) (x := xᵢ)
      (fun k ↦ hV.antitone (by lia) (hxᵢ k)) m 0
    simpa using h
  -- Step 5: `(x, y) ∈ R`, because `R` is closed. Every neighbourhood of `(x, y)` contains a
  -- point `(sᵢ m * u, y / yᵢ m * p)` of `R`, with `u` small and `p` close to `yᵢ m`.
  refine ⟨x, hxV, ?_⟩
  change (x, y) ∈ (R : Set (G × H))
  rw [← hR.closure_eq, mem_closure_iff_nhds]
  intro N hN
  obtain ⟨S, hS, T, hT, hST⟩ := mem_nhds_prod_iff.mp hN
  -- Split `S` as `S' + B` with `S'` a neighbourhood of `x` and `B` a neighbourhood of the identity.
  have hadd_mem : (fun q : G × G ↦ q.1 * q.2) ⁻¹' S ∈ 𝓝 ((x, 1) : G × G) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simpa using hS)
  obtain ⟨S', hS', B, hB, hS'B⟩ := mem_nhds_prod_iff.mp hadd_mem
  obtain ⟨j, hj⟩ := hV.mem_iff.mp hB
  obtain ⟨m, hmS', hmj⟩ := ((hx.eventually hS').and (eventually_ge_atTop j)).exists
  -- Approximate the residual `yᵢ m` by some `p` related to a small `u`.
  have hW : {p : H | y / (yᵢ m / p) ∈ T} ∈ 𝓝 (yᵢ m) := by
    apply ContinuousAt.preimage_mem_nhds (by fun_prop)
    simpa using hT
  obtain ⟨p, hp, u, hu, hup⟩ := mem_closure_iff_nhds.mp (hyᵢ m) _ hW
  refine ⟨(sᵢ m * u, y / yᵢ m * p), hST ⟨?_, ?_⟩, R.mul_mem (hsR m) hup⟩
  · exact hS'B (show (sᵢ m, u) ∈ S' ×ˢ B from ⟨hmS', hj (hV.antitone (by lia) hu)⟩)
  · have e : y / yᵢ m * p = y / (yᵢ m / p) := by
      simp only [div_div_eq_mul_div, div_mul_eq_mul_div]
    change y / yᵢ m * p ∈ T
    rw [e]
    exact hp

variable [FirstCountableTopology G]

/-- A closed subgroup `R` of `G × H`, with `G` complete and first countable, that is nearly
open is open at the identity: if the closure of `R[U]` is a neighbourhood of the identity for every
neighbourhood `U` of zero, then so is `R[U]` itself. -/
@[to_additive /-- A closed subgroup `R` of `G × H`, with `G` complete and first countable, that is
nearly open is open at zero: if the closure of `R[U]` is a neighbourhood of zero for every
neighbourhood `U` of zero, then so is `R[U]` itself. -/]
theorem Subgroup.image_mem_nhds_one (R : Subgroup (G × H)) (hR : IsClosed (R : Set (G × H)))
    (near : ∀ U ∈ 𝓝 (1 : G), _root_.closure (SetRel.image (R : Set (G × H)) U) ∈ 𝓝 (1 : H))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : SetRel.image (R : Set (G × H)) U ∈ 𝓝 (1 : H) := by
  obtain ⟨v, -, hv⟩ := (nhds_basis_opens (1 : G)).exists_antitone_subbasis
  obtain ⟨φ, hφ, hφ'⟩ := hv.exists_subbasis_mul_closure_subset
  obtain ⟨n, hn⟩ := hφ.mem_iff.mp hU
  have h := R.closure_image_subset_image hR hφ (fun k ↦ (hφ' k).1) (fun k ↦ (hφ' k).2)
    (fun k ↦ near _ (hφ.mem k)) n
  refine mem_of_superset (near _ (hφ.mem (n + 2))) (h.trans ?_)
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, hn hx, hxy⟩

/-- A homomorphism `f : G →* H` with closed graph, defined on a complete first-countable group,
that is nearly open is an open map. Here nearly open means that the closure of `f '' U` is a
neighbourhood of the identity for every neighbourhood `U` of zero. -/
@[to_additive /-- A homomorphism `f : G →+ H` with closed graph, defined on a complete
first-countable group, that is nearly open is an open map. Here nearly open means that the closure
of `f '' U` is a neighbourhood of zero for every neighbourhood `U` of zero. -/]
theorem MonoidHom.isOpenMap_of_isClosed_graph_of_nearlyOpen (f : G →* H)
    (hf : IsClosed (f.graph : Set (G × H)))
    (near : ∀ U ∈ 𝓝 (1 : G), closure (f '' U) ∈ 𝓝 (1 : H)) : IsOpenMap f := by
  have himage (U : Set G) : SetRel.image (f.graph : Set (G × H)) U = f '' U := by
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨x, hx, hxy⟩, fun ⟨x, hx, hxy⟩ ↦ ⟨x, hx, hxy⟩⟩
  rw [IsTopologicalGroup.isOpenMap_iff_nhds_one]
  intro s hs
  have h := f.graph.image_mem_nhds_one hf (fun U hU ↦ by simpa only [himage] using near U hU)
    (mem_map.mp hs)
  rw [himage] at h
  exact mem_of_superset h (image_preimage_subset f s)

/-- A continuous homomorphism `f : G →* H` from a complete first-countable group to a Hausdorff
group that is nearly open is an open map. -/
@[to_additive /-- A continuous homomorphism `f : G →+ H` from a complete first-countable group to a
Hausdorff group that is nearly open is an open map. -/]
theorem MonoidHom.isOpenMap_of_continuous_of_nearlyOpen [T2Space H] (f : G →* H) (hf : Continuous f)
    (near : ∀ U ∈ 𝓝 (1 : G), closure (f '' U) ∈ 𝓝 (1 : H)) : IsOpenMap f :=
  f.isOpenMap_of_isClosed_graph_of_nearlyOpen
    (isClosed_eq (hf.comp continuous_fst) continuous_snd) near

/-- A homomorphism `g : H →* G` with closed graph, with values in a complete first-countable
group, that is nearly continuous is continuous. Here nearly continuous means that the closure
of `g ⁻¹' V` is a neighbourhood of the identity for every neighbourhood `V` of zero. -/
@[to_additive /-- A homomorphism `g : H →+ G` with closed graph, with values in a complete
first-countable group, that is nearly continuous is continuous. Here nearly continuous means that
the closure of `g ⁻¹' V` is a neighbourhood of zero for every neighbourhood `V` of zero. -/]
theorem MonoidHom.continuous_of_isClosed_graph_of_nearlyContinuous (g : H →* G)
    (hg : IsClosed (g.graph : Set (H × G)))
    (near : ∀ V ∈ 𝓝 (1 : G), closure (g ⁻¹' V) ∈ 𝓝 (1 : H)) : Continuous g := by
  -- The transposed graph, a closed subgroup of `G × H`.
  let R : Subgroup (G × H) := g.graph.comap (MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom
  have hR : IsClosed (R : Set (G × H)) := hg.preimage continuous_swap
  have himage (V : Set G) : SetRel.image (R : Set (G × H)) V = g ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have : g y = x := hxy
      simpa [this] using hx
    · intro hy
      exact ⟨g y, hy, (rfl : g y = g y)⟩
  refine continuous_of_continuousAt_one g fun V hV ↦ ?_
  rw [map_one] at hV
  have h := R.image_mem_nhds_one hR (fun U hU ↦ by simpa only [himage] using near U hU) hV
  rwa [himage] at h
