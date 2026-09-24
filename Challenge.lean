import Mathlib

/-!
# Challenge: the theory of locally convex spaces

This file is the statement surface of the Palomar submission for `lean-LCS`. It imports only
Mathlib. It defines the notions of the theory of locally convex spaces that Mathlib does not
provide, and states the principal theorems of the library about them, each with `sorry`. The
file `Solution.lean` proves every statement from the library.

Conventions. The scalar field is `ℝ` or `ℂ` (`RCLike 𝕜`) unless stated otherwise. Local
convexity is expressed as `LocallyConvexSpace ℝ E`, with `E` a real vector space through
`IsScalarTower ℝ 𝕜 E`. `StrongDual 𝕜 E` is the continuous dual with the topology of uniform
convergence on bounded sets, and `WeakDual 𝕜 E` is the same space with the weak-* topology. A
Fréchet space is a Hausdorff, complete, first-countable locally convex space. Results without
Hausdorffness are stated for complete, first-countable locally convex spaces.
-/

open Set Filter Function Bornology PiNat

open scoped Topology Pointwise Cardinal UniformConvergenceCLM

universe u

/-! ## Definitions

The definitions below are copied verbatim from the library, under the same names, so that the
Comparator can check that they coincide with the library's definitions.

When Lean elaborates a definition it moves proofs nested in its value into auxiliary lemmas
`_proof_n`, and it reuses such a lemma for a later definition of the same file. The library
defines these notions in separate modules, each of which starts with an empty cache of auxiliary
lemmas. The command `clear_aux_lemma_cache` empties the cache at each such module boundary, so
that each copy below is elaborated exactly as its original. It has no other effect. -/

/-- Empty Lean's cache of auxiliary proof lemmas, as at the start of a new module. -/
elab "clear_aux_lemma_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}

section Barrel

variable {𝕜 E : Type*}

variable (𝕜) [SeminormedRing 𝕜] [AddCommMonoid E] [SMul 𝕜 E] [Module ℝ E] [TopologicalSpace E]

/-- A set is a **barrel** if it is closed, convex over `ℝ`, and balanced and absorbent over `𝕜`. -/
structure IsBarrel (s : Set E) : Prop where
  /-- A barrel is closed. -/
  isClosed : IsClosed s
  /-- A barrel is `ℝ`-convex. -/
  convex : Convex ℝ s
  /-- A barrel is balanced. -/
  balanced : Balanced 𝕜 s
  /-- A barrel is absorbent. -/
  absorbent : Absorbent 𝕜 s

end Barrel

clear_aux_lemma_cache

section FinalTopology

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]

/-- The final locally convex topology on `F` for a family of linear maps `f i : E i →ₗ[𝕜] F`:
the finest locally convex vector space topology on `F` for which all `f i` are continuous. It is
the topology of locally convex inductive limits, direct sums and hulls. -/
@[instance_reducible]
def locallyConvexFinalTopology (f : ∀ i, E i →ₗ[𝕜] F) : TopologicalSpace F :=
  sInf {t : TopologicalSpace F | @IsTopologicalAddGroup F t _ ∧ @ContinuousSMul 𝕜 F _ _ t ∧
    @LocallyConvexSpace ℝ F _ _ _ _ t ∧ ∀ i, @Continuous (E i) F _ t (f i)}

end FinalTopology

clear_aux_lemma_cache

namespace StrongDual

section Defs

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A set `C` of continuous linear functionals on `E` is *almost weak-\* closed* if its
intersection with the polar of every neighbourhood of zero in `E` is weak-\* closed. -/
def IsAlmostWeakStarClosed (C : Set (StrongDual 𝕜 E)) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), IsClosed (WeakDual.toStrongDual ⁻¹' (C ∩ polar 𝕜 U))

end Defs

end StrongDual

clear_aux_lemma_cache

section Ptak

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A topological vector space is a **Pták space** (is `B`-complete) if every almost weak-\*
closed subspace of its dual is weak-\* closed. -/
class PtakSpace : Prop where
  /-- In the dual of a Pták space every almost weak-\* closed subspace is weak-\* closed. -/
  isClosed_of_isAlmostWeakStarClosed : ∀ Q : Submodule 𝕜 (StrongDual 𝕜 E),
    StrongDual.IsAlmostWeakStarClosed (Q : Set (StrongDual 𝕜 E)) →
      IsClosed (WeakDual.toStrongDual ⁻¹' (Q : Set (StrongDual 𝕜 E)))

/-- A topological vector space is an **infra-Pták space** (is `B_r`-complete) if every weak-\*
dense, almost weak-\* closed subspace of its dual is the whole dual. -/
class InfraPtakSpace : Prop where
  /-- In the dual of an infra-Pták space every weak-\* dense, almost weak-\* closed subspace is
  the whole dual. -/
  eq_top_of_dense : ∀ Q : Submodule 𝕜 (StrongDual 𝕜 E),
    StrongDual.IsAlmostWeakStarClosed (Q : Set (StrongDual 𝕜 E)) →
      Dense (WeakDual.toStrongDual ⁻¹' (Q : Set (StrongDual 𝕜 E))) → Q = ⊤

end Ptak

clear_aux_lemma_cache

namespace LinearMap

section PolarTopology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip)))

/-- The linear map that sends `x : E` to the functional `y ↦ B x y` on `F` with the weak topology
`σ(F, E)`, as an element of the space of continuous linear functionals with the topology of
uniform convergence on the members of `𝔖`. -/
noncomputable def toUniformConvergenceCLM : E →ₗ[𝕜] (WeakBilin B.flip →Lᵤ[𝕜, 𝔖] 𝕜) where
  toFun x := WeakBilin.eval B.flip x
  map_add' x y := map_add (WeakBilin.eval B.flip) x y
  map_smul' c x := map_smul (WeakBilin.eval B.flip) c x

/-- The **polar topology** on `E` for the pairing `B` and a family `𝔖` of subsets of `F`: the
topology of uniform convergence on the members of `𝔖`. -/
@[instance_reducible]
noncomputable def polarTopology : TopologicalSpace E :=
  TopologicalSpace.induced (B.toUniformConvergenceCLM 𝔖) inferInstance

end PolarTopology

clear_aux_lemma_cache

section Mackey

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The family of `σ(F, E)`-compact, `ℝ`-convex, balanced subsets of `F`, which defines the Mackey
topology on `E`. -/
def mackeyFamily : Set (Set (WeakBilin B.flip)) :=
  {K | IsCompact K ∧ Convex ℝ K ∧ Balanced 𝕜 K}

/-- The **Mackey topology** `τ(E, F)` on `E` for a pairing `B`: the topology of uniform
convergence on the `σ(F, E)`-compact, `ℝ`-convex, balanced subsets of `F`. -/
@[instance_reducible]
noncomputable def mackeyTopology : TopologicalSpace E :=
  B.polarTopology B.mackeyFamily

/-- A topology on `E` is **compatible** with the pairing `B` if its continuous linear functionals
are exactly the functionals `x ↦ B x y` with `y : F`. -/
def IsCompatibleTopology [TopologicalSpace E] : Prop :=
  ∀ f : E →ₗ[𝕜] 𝕜, Continuous f ↔ ∃ y : F, ∀ x, f x = B x y

end Mackey

end LinearMap

clear_aux_lemma_cache

section Bornivorous

variable (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A set is **bornivorous** if it absorbs every von Neumann bounded set. -/
def Bornology.IsBornivorous (s : Set E) : Prop :=
  ∀ t : Set E, IsVonNBounded 𝕜 t → Absorbs 𝕜 s t

end Bornivorous

section Bornological

variable (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] [TopologicalSpace E]

/-- A topological vector space is **bornological** if every seminorm that is bounded on the von
Neumann bounded sets is continuous. For real or complex spaces this is equivalent to the classical
condition that every `ℝ`-convex, balanced, bornivorous set is a neighbourhood of zero (see
`bornologicalSpace_iff_forall_mem_nhds_zero` below). -/
class BornologicalSpace : Prop where
  /-- In a bornological space every seminorm that is bounded on the bounded sets is
  continuous. -/
  continuous_of_bddAbove : ∀ p : Seminorm 𝕜 E,
    (∀ s : Set E, IsVonNBounded 𝕜 s → BddAbove (p '' s)) → Continuous p

/-- A topological vector space is **quasi-barrelled** if every lower semicontinuous seminorm
that is bounded on the von Neumann bounded sets is continuous. For real or complex spaces this is
equivalent to the classical condition that every bornivorous barrel is a neighbourhood of
zero. -/
class QuasiBarrelledSpace : Prop where
  /-- In a quasi-barrelled space every lower semicontinuous seminorm that is bounded on the
  bounded sets is continuous. -/
  continuous_of_lowerSemicontinuous_of_bddAbove : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p →
    (∀ s : Set E, IsVonNBounded 𝕜 s → BddAbove (p '' s)) → Continuous p

end Bornological

clear_aux_lemma_cache

section Ultrabornological

variable (𝕜 : Type*) (E : Type u) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A topological vector space `E` is **ultrabornological** if every seminorm on `E` whose
composition with every continuous linear map from a complete seminormed space into `E` is
continuous, is itself continuous. The test spaces are taken in the universe of `E`, as for
Mathlib's `CompactlyGeneratedSpace`. For a real or complex locally convex space this says that
the topology is the final locally convex topology of the continuous linear maps from Banach
spaces. -/
class UltrabornologicalSpace : Prop where
  /-- In an ultrabornological space a seminorm is continuous as soon as its compositions with
  the continuous linear maps from complete seminormed spaces are continuous. -/
  continuous_of_forall_continuous_comp : ∀ p : Seminorm 𝕜 E,
    (∀ (X : Type u) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
      (f : X →L[𝕜] E), Continuous fun x ↦ p (f x)) → Continuous p

end Ultrabornological

clear_aux_lemma_cache

section Reflexive

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- The canonical linear map of a topological vector space into its bidual: a point `x` is sent
to the evaluation `φ ↦ φ x`, which is continuous on the strong dual. -/
def StrongDual.inclusionInDoubleDual : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) where
  toFun x :=
    { toFun := fun φ ↦ φ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_eval_const x }
  map_add' x y := ContinuousLinearMap.ext fun φ ↦ map_add φ x y
  map_smul' c x := ContinuousLinearMap.ext fun φ ↦ map_smul φ c x

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

end Reflexive

clear_aux_lemma_cache

section StrictInductiveLimit

variable {𝕜 : Type*} [Semiring 𝕜] {E : ℕ → Type*} {F : Type*}
  [∀ n, AddCommMonoid (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
  [AddCommMonoid F] [Module 𝕜 F]

/-- A **strict inductive sequence** with limit space `F`: continuous linear maps
`j n : E n →L[𝕜] E (n + 1)` that are topological embeddings, together with injective linear maps
`f n : E n →ₗ[𝕜] F` that are compatible with the maps `j n` and whose ranges cover `F`. The
*strict inductive limit* is `F` with the final locally convex topology
`locallyConvexFinalTopology f`; that topology is not part of this structure. -/
structure IsStrictInductiveLimit (j : ∀ n, E n →L[𝕜] E (n + 1)) (f : ∀ n, E n →ₗ[𝕜] F) :
    Prop where
  /-- Every step is topologically embedded in the next one. -/
  isEmbedding_step : ∀ n, Topology.IsEmbedding (j n)
  /-- The maps into `F` are compatible with the steps. -/
  apply_step : ∀ n x, f (n + 1) (j n x) = f n x
  /-- The maps into `F` are injective. -/
  injective : ∀ n, Injective (f n)
  /-- The ranges of the maps into `F` cover `F`. -/
  exists_apply_eq : ∀ y : F, ∃ n x, f n x = y

end StrictInductiveLimit

clear_aux_lemma_cache

section Webs

variable {E : Type*}

/-- A **web** on `E`: a family of subsets indexed by finite sequences of natural numbers, with
`C [] = univ`, such that every set is the union of its successors `C (n :: l)`. -/
structure IsWeb (C : List ℕ → Set E) : Prop where
  /-- The root of a web is the whole space. -/
  nil : C [] = univ
  /-- Every set of a web is the union of its successors. -/
  iUnion_cons : ∀ l : List ℕ, ⋃ n, C (n :: l) = C l

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A web is **completing** (a `𝒞`-web) if along every strand `σ` there are numbers `ρ k > 0`
such that the series `∑ λ k • x k` converges whenever `x k ∈ C (res σ (k + 1))` and
`0 ≤ λ k ≤ ρ k` for all `k`. Here `res σ k` is the list of the first `k` terms of `σ`, in
reverse order. -/
structure IsCompletingWeb (C : List ℕ → Set E) : Prop extends IsWeb C where
  /-- Along every strand there is a sequence of radii for which the associated series
  converge. -/
  exists_radius : ∀ σ : ℕ → ℕ, ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧
    ∀ (x : ℕ → E) (c : ℕ → ℝ), (∀ k, x k ∈ C (res σ (k + 1))) → (∀ k, 0 ≤ c k ∧ c k ≤ ρ k) →
      ∃ s : E, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c k • x k) atTop (𝓝 s)

/-- The underlying web of a completing web. -/
add_decl_doc IsCompletingWeb.toIsWeb

/-- A web is **strict** if its sets are `ℝ`-convex and `𝕜`-balanced and along every strand `σ` there
are numbers `ρ k > 0` such that for `x k ∈ C (res σ (k + 1))` and `0 ≤ λ k ≤ ρ k` the series
`∑ λ k • x k` converges and each of its tails `∑_{k ≥ k₀} λ k • x k` lies in
`C (res σ (k₀ + 1))`. -/
structure IsStrictWeb (𝕜 : Type*) [NormedField 𝕜] [Module 𝕜 E] (C : List ℕ → Set E) :
    Prop extends IsWeb C where
  /-- The sets of a strict web are `ℝ`-convex. -/
  convex : ∀ l, Convex ℝ (C l)
  /-- The sets of a strict web are balanced over `𝕜`. -/
  balanced : ∀ l, Balanced 𝕜 (C l)
  /-- Along every strand there is a sequence of radii for which the associated series converge
  and their tails stay in the sets of the strand. -/
  exists_radius : ∀ σ : ℕ → ℕ, ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧
    ∀ (x : ℕ → E) (c : ℕ → ℝ), (∀ k, x k ∈ C (res σ (k + 1))) → (∀ k, 0 ≤ c k ∧ c k ≤ ρ k) →
      ∀ k₀, ∃ s ∈ C (res σ (k₀ + 1)),
        Tendsto (fun N ↦ ∑ k ∈ Finset.range N, c (k₀ + k) • x (k₀ + k)) atTop (𝓝 s)

/-- The underlying web of a strict web. -/
add_decl_doc IsStrictWeb.toIsWeb

variable (E) in
/-- A topological vector space is **webbed** if it has a completing web. -/
class WebbedSpace : Prop where
  /-- A webbed space has a completing web. -/
  exists_isCompletingWeb : ∃ C : List ℕ → Set E, IsCompletingWeb C

/-- A topological vector space is **strictly webbed** if it has a strict web. -/
class StrictlyWebbedSpace (𝕜 F : Type*) [NormedField 𝕜] [AddCommGroup F] [Module ℝ F]
    [Module 𝕜 F] [TopologicalSpace F] : Prop where
  /-- A strictly webbed space has a strict web. -/
  exists_isStrictWeb : ∃ C : List ℕ → Set F, IsStrictWeb 𝕜 C

end Webs

/-! ## Theorems -/

namespace LeanLCS

/-! ### Barrelled spaces: closed graph and open mapping theorems -/

/-- A topological vector space over `ℝ` or `ℂ` is barrelled if and only if every barrel is a
neighbourhood of zero. -/
theorem barrelledSpace_iff_forall_isBarrel_mem_nhds {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [ContinuousSMul ℝ E] :
    BarrelledSpace 𝕜 E ↔ ∀ (s : Set E), IsBarrel 𝕜 s → s ∈ 𝓝 0 := by
  sorry

/-- **Characterization of barrelled spaces**: a locally convex space is barrelled if and only if
every pointwise bounded (that is, weak-* bounded) subset of its dual is equicontinuous. -/
theorem barrelledSpace_iff_forall_equicontinuous {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] :
    BarrelledSpace 𝕜 E ↔ ∀ (H : Set (StrongDual 𝕜 E)), (∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜
      E ↦ φ x) '' H)) → Equicontinuous ((↑) : H → E → 𝕜) := by
  sorry

/-- The **closed graph theorem** for a barrelled domain: a linear map with closed graph from a
barrelled space to a complete, first-countable, locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [BarrelledSpace 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [CompleteSpace F] [FirstCountableTopology F]
    (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g := by
  sorry

/-- The **open mapping theorem** for a barrelled codomain: a continuous linear map from a complete,
first-countable, locally convex space onto a barrelled Hausdorff space is an open map. -/
theorem ContinuousLinearMap.isOpenMap_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [BarrelledSpace 𝕜 F]
    [T2Space F] (f : E →L[𝕜] F) (hsurj : Function.Surjective f) :
    IsOpenMap f := by
  sorry

/-- A continuous linear bijection from a complete, first-countable, locally convex space onto a
barrelled Hausdorff space has a continuous inverse. -/
theorem LinearEquiv.continuous_symm_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [BarrelledSpace 𝕜 F]
    [T2Space F] (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    Continuous e.symm := by
  sorry

/-- The final locally convex topology for a family of maps from barrelled spaces is barrelled. In
particular locally convex direct sums and inductive limits of barrelled spaces are barrelled. -/
theorem locallyConvexFinalTopology.barrelledSpace {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type*}
    {F : Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] (f : ∀ i, E i →ₗ[𝕜] F) [IsScalarTower ℝ 𝕜 F]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, BarrelledSpace 𝕜 (E i)] :
    @BarrelledSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) := by
  sorry

/-- A quotient of a barrelled module over a seminormed ring is barrelled. -/
theorem Submodule.Quotient.instBarrelledSpace {𝕜 : Type*} {E : Type*} [SeminormedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (N : Submodule 𝕜 E) :
    BarrelledSpace 𝕜 (E ⧸ N) := by
  sorry

/-! ### Pták theory -/

/-- A complete, first-countable, locally convex space is a Pták space. -/
theorem PtakSpace.of_completeSpace_firstCountableTopology {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] :
    PtakSpace 𝕜 E := by
  sorry

/-- **Pták's closed graph theorem**: a linear map with closed graph from a barrelled locally convex
space to an infra-Pták (`B_r`-complete) locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] [LocallyConvexSpace ℝ E] [BarrelledSpace 𝕜 E] [InfraPtakSpace 𝕜 F]
    (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g := by
  sorry

/-- **Pták's open mapping theorem**: a continuous linear map from a Pták (`B`-complete) locally
convex space onto a barrelled Hausdorff locally convex space is an open map. -/
theorem ContinuousLinearMap.isOpenMap_of_ptakSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ E] [PtakSpace 𝕜 E] [LocallyConvexSpace ℝ F] [BarrelledSpace 𝕜 F]
    [T2Space F] (f : E →L[𝕜] F) (hf : Function.Surjective f) :
    IsOpenMap f := by
  sorry

/-! ### Duality -/

/-- The **bipolar theorem** for a locally convex space `E` and its continuous dual: a nonempty,
closed, `ℝ`-convex, balanced set is its own bipolar. -/
theorem StrongDual.bipolar_eq_self {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set E} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) :
    (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 s) = s := by
  sorry

/-- The **bipolar theorem** for a bilinear pairing: a nonempty, weakly closed, `ℝ`-convex, balanced
set is its own bipolar. -/
theorem LinearMap.flip_polar_polar_eq_self {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {s : Set (WeakBilin B)} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) :
    B.flip.polar (B.polar s) = s := by
  sorry

/-- The **Alaoglu–Bourbaki theorem**: the polar of a neighbourhood of zero in a topological vector
space `E` over a proper nontrivially normed field is a compact subset of `WeakDual 𝕜 E`. For normed
spaces this is `WeakDual.isCompact_polar`. -/
theorem WeakDual.isCompact_polar_of_mem_nhds {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [ProperSpace 𝕜] {U : Set E} (hU : U ∈ 𝓝 0) :
    IsCompact (WeakDual.polar 𝕜 U) := by
  sorry

/-- A subset of a locally convex space is von Neumann bounded if and only if every continuous linear
functional is bounded on it. -/
theorem Bornology.isVonNBounded_iff_forall_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] {A : Set E} :
    IsVonNBounded 𝕜 A ↔ ∀ (φ : StrongDual 𝕜 E), ∃ C, ∀ x ∈ A, ‖φ x‖ ≤ C := by
  sorry

/-- The **Mackey–Arens theorem**: a locally convex vector space topology on `E` is compatible with a
pairing `B` of `E` and `F` if and only if the functionals `x ↦ B x y` are continuous, which says
that the topology is finer than the weak topology `σ(E, F)`, and the topology is coarser than the
Mackey topology `τ(E, F)`. -/
theorem LinearMap.isCompatibleTopology_iff_mackeyTopology_le {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    B.IsCompatibleTopology ↔ (∀ y, Continuous fun x ↦ (B x) y) ∧ B.mackeyTopology ≤ (inferInstance :
      TopologicalSpace E) := by
  sorry

/-- The **Banach–Dieudonné theorem**. Let `E` be a first-countable topological vector space and let
`W` be a set of continuous linear functionals that contains zero and whose complement is almost
weak-\* closed. Then `W` contains the polar of a compact subset of `E`. -/
theorem StrongDual.exists_isCompact_polar_subset {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] {W : Set (StrongDual 𝕜 E)} (hW0 : 0 ∈ W)
    (hW : StrongDual.IsAlmostWeakStarClosed Wᶜ) :
    ∃ S, IsCompact S ∧ StrongDual.polar 𝕜 S ⊆ W := by
  sorry

/-- The **Krein–Šmulian theorem**. In the dual of a complete, first-countable, locally convex space
every `ℝ`-convex almost weak-\* closed set is weak-\* closed. -/
theorem StrongDual.isClosed_of_isAlmostWeakStarClosed {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] {C : Set (StrongDual 𝕜 E)} (hC : Convex ℝ C)
    (h : StrongDual.IsAlmostWeakStarClosed C) :
    IsClosed (WeakDual.toStrongDual ⁻¹' C) := by
  sorry

/-- A locally convex space is complete if and only if every linear form on its dual that is weak-*
continuous on each zero-neighbourhood polar is evaluation at a point. -/
theorem StrongDual.completeSpace_iff_forall_exists_eq_apply {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    CompleteSpace E ↔ ∀ (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜), (∀ U ∈ 𝓝 0, ContinuousOn (fun φ ↦ f
      (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U)) → ∃ x, ∀ (φ : StrongDual 𝕜 E), f φ = φ x := by
  sorry

/-- A functional continuous for compact convergence on the dual of a complete locally convex space
is evaluation at a point of the original space. -/
theorem CompactConvergenceCLM.exists_forall_apply_eq {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    (Λ : CompactConvergenceCLM (RingHom.id 𝕜) E 𝕜 →L[𝕜] 𝕜) :
    ∃ x, ∀ (f : CompactConvergenceCLM (RingHom.id 𝕜) E 𝕜), Λ f = f x := by
  sorry

/-- In a complete locally convex space every compact set lies in a compact `ℝ`-convex balanced set
containing zero. -/
theorem IsCompact.exists_isCompact_convex_balanced_superset {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) :
    ∃ K', K ⊆ K' ∧ IsCompact K' ∧ Convex ℝ K' ∧ Balanced 𝕜 K' ∧ 0 ∈ K' := by
  sorry

/-- **Milman's converse**: the extreme points of a compact closed `ℝ`-convex hull belong to the
closure of the generating set. -/
theorem IsCompact.extremePoints_closure_convexHull_subset_closure {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hC : IsCompact (closure (convexHull ℝ s))) :
    Set.extremePoints ℝ (closure (convexHull ℝ s)) ⊆ closure s := by
  sorry

/-! ### Bornological and ultrabornological spaces -/

/-- A real or complex topological vector space is bornological if and only if every `ℝ`-convex,
balanced, bornivorous set is a neighbourhood of zero. -/
theorem bornologicalSpace_iff_forall_mem_nhds_zero {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] :
    BornologicalSpace 𝕜 E ↔ ∀ (s : Set E), Convex ℝ s → Balanced 𝕜 s → IsBornivorous 𝕜 s → s ∈ 𝓝 0 := by
  sorry

/-- A linear map from a bornological space to a polynormable space, in particular to a locally
convex space, that maps bounded sets to bounded sets is continuous. -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [BornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] [PolynormableSpace 𝕜 F] (f : E →ₗ[𝕜] F)
    (hf : ∀ (t : Set E), IsVonNBounded 𝕜 t → IsVonNBounded 𝕜 (f '' t)) :
    Continuous f := by
  sorry

/-- A first-countable topological vector space is bornological. In particular metrizable locally
convex spaces and normed spaces are bornological. -/
theorem BornologicalSpace.of_firstCountableTopology {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FirstCountableTopology E] :
    BornologicalSpace 𝕜 E := by
  sorry

/-- A complete, first-countable, Hausdorff locally convex space (a Fréchet space) is
ultrabornological: its topology is the final locally convex topology for the maps `lp.tsumSMulCLM x
hx : ℓ¹(ℕ, 𝕜) → E`, where `x` ranges over the sequences in `E` that tend to zero. -/
theorem UltrabornologicalSpace.of_completeSpace_firstCountableTopology {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [T2Space E] :
    UltrabornologicalSpace 𝕜 E := by
  sorry

/-- An ultrabornological space is barrelled: a lower semicontinuous seminorm is continuous on every
complete seminormed space, which is barrelled by Baire's theorem. -/
theorem UltrabornologicalSpace.toBarrelledSpace {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [UltrabornologicalSpace 𝕜 E] :
    BarrelledSpace 𝕜 E := by
  sorry

/-- **A quasi-complete Hausdorff bornological locally convex space is ultrabornological.** In such a
space the closed bounded disks are Banach disks. -/
theorem UltrabornologicalSpace.of_bornologicalSpace_of_quasiCompleteSpace {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    [BornologicalSpace 𝕜 E] [QuasiCompleteSpace 𝕜 E] :
    UltrabornologicalSpace 𝕜 E := by
  sorry

/-- The final locally convex topology for a family of maps from ultrabornological spaces is
ultrabornological. In particular inductive limits of ultrabornological spaces, such as LF spaces,
are ultrabornological. The spaces are taken in one universe. -/
theorem locallyConvexFinalTopology.ultrabornologicalSpace {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {E : ι → Type u} {F : Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [∀ i, UltrabornologicalSpace 𝕜 (E i)] (f : ∀ i, E i →ₗ[𝕜] F) :
    @UltrabornologicalSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) := by
  sorry

/-! ### Quasi-barrelled, reflexive and Montel spaces -/

/-- A locally convex space is quasi-barrelled if and only if every strongly bounded subset of its
dual is equicontinuous. -/
theorem quasiBarrelledSpace_iff_forall_equicontinuous {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    QuasiBarrelledSpace 𝕜 E ↔ ∀ (H : Set (StrongDual 𝕜 E)), IsVonNBounded 𝕜 H → Equicontinuous ((↑)
      : H → E → 𝕜) := by
  sorry

/-- A locally convex space is **reflexive if and only if it is semi-reflexive and barrelled**. -/
theorem reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    ReflexiveSpace 𝕜 E ↔ SemiReflexiveSpace 𝕜 E ∧ BarrelledSpace 𝕜 E := by
  sorry

/-- A Hausdorff locally convex space is **semi-reflexive if and only if every bounded set lies in a
weakly compact, `ℝ`-convex, balanced set**; in particular if and only if its bounded sets are
relatively weakly compact. -/
theorem semiReflexiveSpace_iff_forall_isVonNBounded (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] :
    SemiReflexiveSpace 𝕜 E ↔ ∀ (S : Set E), IsVonNBounded 𝕜 S → ∃ K ∈ (topDualPairing 𝕜
      E).mackeyFamily, toWeakSpace 𝕜 E '' S ⊆ K := by
  sorry

/-- A space is semi-reflexive if and only if the strong topology `β(E', E)` on its dual is coarser
than the Mackey topology `τ(E', E)`; this is the Mackey–Arens theorem for the pairing of the dual
and the space. -/
theorem semiReflexiveSpace_iff_mackeyTopology_le (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    SemiReflexiveSpace 𝕜 E ↔ (topDualPairing 𝕜 E).mackeyTopology ≤ (inferInstance : TopologicalSpace
      (StrongDual 𝕜 E)) := by
  sorry

/-- The strong dual of a reflexive locally convex space is reflexive, including under the
non-Hausdorff convention used here. This is Schaefer–Wolff, IV §5.6, Corollary 1, using
semi-reflexivity and barrelledness of the strong dual. -/
theorem ReflexiveSpace.strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [ReflexiveSpace 𝕜 E] :
    ReflexiveSpace 𝕜 (StrongDual 𝕜 E) := by
  sorry

/-- A barrelled locally convex Montel space is reflexive. -/
theorem MontelSpace.reflexiveSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E] [MontelSpace 𝕜 E] [BarrelledSpace 𝕜 E] :
    ReflexiveSpace 𝕜 E := by
  sorry

/-- The strong dual of a quasi-barrelled Hausdorff Montel space is Montel. -/
theorem MontelSpace.strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [MontelSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [QuasiBarrelledSpace 𝕜 E] :
    MontelSpace 𝕜 (StrongDual 𝕜 E) := by
  sorry

/-- The strong dual of a Hausdorff Montel locally convex space is barrelled. This follows from
semi-reflexivity, even without barrelledness of the original space. -/
theorem MontelSpace.barrelledSpace_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [MontelSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] :
    BarrelledSpace 𝕜 (StrongDual 𝕜 E) := by
  sorry

/-- A closed subspace of a semi-reflexive space is reflexive if it is quasi-barrelled. -/
theorem ReflexiveSpace.submodule_of_quasiBarrelledSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [SemiReflexiveSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) [QuasiBarrelledSpace 𝕜 M] :
    ReflexiveSpace 𝕜 M := by
  sorry

/-- Arbitrary products of semi-reflexive spaces are semi-reflexive. -/
theorem SemiReflexiveSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, SemiReflexiveSpace 𝕜 (E i)] :
    SemiReflexiveSpace 𝕜 (∀ i, E i) := by
  sorry

/-- Arbitrary products of reflexive locally convex spaces are reflexive. -/
theorem ReflexiveSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, ReflexiveSpace 𝕜 (E i)] :
    ReflexiveSpace 𝕜 (∀ i, E i) := by
  sorry

/-- Arbitrary products of Montel spaces have the Heine–Borel property. -/
theorem MontelSpace.pi {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)] [∀ i, ContinuousSMul 𝕜 (G i)] [∀ i, MontelSpace 𝕜 (G i)]
    [∀ i, T2Space (G i)] :
    MontelSpace 𝕜 (∀ i, G i) := by
  sorry

/-- Arbitrary products of quasi-barrelled locally convex spaces are quasi-barrelled. -/
theorem QuasiBarrelledSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [∀ i, QuasiBarrelledSpace 𝕜 (E i)] :
    QuasiBarrelledSpace 𝕜 (∀ i, E i) := by
  sorry

/-! ### Completeness of strong duals -/

/-- The strong dual of a bornological space over a complete nontrivially normed field is complete,
without metrizability or completeness assumptions on the original space. -/
theorem BornologicalSpace.completeSpace_strongDual {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [BornologicalSpace 𝕜 E] :
    CompleteSpace (StrongDual 𝕜 E) := by
  sorry

/-- The strong dual of a quasi-barrelled space is quasi-complete. In particular this applies to
barrelled spaces. -/
theorem QuasiBarrelledSpace.quasiCompleteSpace_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [QuasiBarrelledSpace 𝕜 E] :
    QuasiCompleteSpace 𝕜 (StrongDual 𝕜 E) := by
  sorry

/-- The strong dual of Schwartz space is complete, over either the real or complex scalars. No
completeness assumption on the target of the Schwartz functions is needed. -/
theorem SchwartzMap.instCompleteSpaceStrongDual {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] :
    CompleteSpace (StrongDual 𝕜 (SchwartzMap E F)) := by
  sorry

/-- Test-function spaces are bornological: their topology is final for the bornological spaces of
functions supported in fixed compact subsets. -/
theorem TestFunction.instBornologicalSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {Ω : TopologicalSpace.Opens E} {n : ℕ∞} :
    BornologicalSpace 𝕜 (TestFunction Ω F n) := by
  sorry

/-- The real or complex strong dual of test-function space is complete for uniform convergence on
bounded sets, even when the normed target of the test functions is incomplete. -/
theorem TestFunction.instCompleteSpaceStrongDual {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {Ω : TopologicalSpace.Opens E} {n : ℕ∞} :
    CompleteSpace (StrongDual 𝕜 (TestFunction Ω F n)) := by
  sorry

/-! ### Strict inductive limits -/

/-- The **Dieudonné–Schwartz theorem**: in a strict inductive limit in which every step is closed in
the next one, every bounded set is contained in a step. -/
theorem IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded {𝕜 : Type*} [RCLike 𝕜]
    {E : ℕ → Type*} {F : Type*} [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)]
    [∀ n, Module ℝ (E n)] [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)]
    [∀ n, IsTopologicalAddGroup (E n)] [∀ n, ContinuousSMul 𝕜 (E n)]
    [∀ n, LocallyConvexSpace ℝ (E n)] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F}
    (h : IsStrictInductiveLimit j f) (hjcl : ∀ n, IsClosed (Set.range (j n))) {B : Set F}
    (hB : @IsVonNBounded 𝕜 F _ _ _ (locallyConvexFinalTopology f) B) :
    ∃ n, B ⊆ Set.range (f n) := by
  sorry

/-- A countable strict inductive limit of complete locally convex spaces is complete. -/
theorem IsStrictInductiveLimit.completeSpace {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
    [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
    [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, UniformSpace (E n)] [∀ n, IsUniformAddGroup (E n)]
    [∀ n, ContinuousSMul 𝕜 (E n)] [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [uF : UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul 𝕜 F] {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F}
    (h : IsStrictInductiveLimit j f) (hFtop : uF.toTopologicalSpace = locallyConvexFinalTopology f) :
    CompleteSpace F := by
  sorry

/-- Countable strict inductive limits of Hausdorff reflexive locally convex spaces with closed
transition ranges are reflexive. -/
theorem IsStrictInductiveLimit.reflexiveSpace {𝕜 : Type*} {F : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
    [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)] [∀ n, IsTopologicalAddGroup (E n)]
    [∀ n, ContinuousSMul 𝕜 (E n)] [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, T2Space (E n)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [tF : TopologicalSpace F]
    [ContinuousSMul 𝕜 F] {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F}
    (h : IsStrictInductiveLimit j f) (hjcl : ∀ n, IsClosed (Set.range (j n)))
    (htop : tF = locallyConvexFinalTopology f) [∀ n, ReflexiveSpace 𝕜 (E n)] :
    ReflexiveSpace 𝕜 F := by
  sorry

/-- Countable strict inductive limits of Hausdorff Montel locally convex spaces with closed
transition ranges have the Montel property. -/
theorem IsStrictInductiveLimit.montelSpace {𝕜 : Type*} {F : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
    [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, TopologicalSpace (E n)] [∀ n, IsTopologicalAddGroup (E n)]
    [∀ n, ContinuousSMul 𝕜 (E n)] [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, T2Space (E n)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [tF : TopologicalSpace F]
    {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F} (h : IsStrictInductiveLimit j f)
    (hjcl : ∀ n, IsClosed (Set.range (j n))) (htop : tF = locallyConvexFinalTopology f)
    [∀ n, MontelSpace 𝕜 (E n)] :
    MontelSpace 𝕜 F := by
  sorry

/-! ### Webbed spaces and De Wilde's theorems -/

/-- **De Wilde's closed graph theorem**: a linear map with sequentially closed graph from an
ultrabornological space into a webbed locally convex space is continuous, Köthe II §35.2.(2). Banach
spaces, Fréchet spaces and LF spaces are ultrabornological. -/
theorem LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} {F : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [UltrabornologicalSpace 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F] (A : E →ₗ[𝕜] F)
    (hA : IsSeqClosed (A.graph : Set (E × F))) :
    Continuous A := by
  sorry

/-- **De Wilde's open mapping theorem**: a linear map with sequentially closed graph from a webbed
locally convex space onto an ultrabornological space is open, Köthe II §35.3.(5). -/
theorem LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} {F : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [UltrabornologicalSpace 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F] (A : F →ₗ[𝕜] E)
    (hA : IsSeqClosed (A.graph : Set (F × E))) (hsurj : Function.Surjective A) :
    IsOpenMap A := by
  sorry

end LeanLCS
