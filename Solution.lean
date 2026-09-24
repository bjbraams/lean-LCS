import LeanLCS

/-!
# Solution: proofs of the Challenge statements

Each theorem restates the corresponding theorem of `Challenge.lean` verbatim and proves it by the
theorem of the library with the same name outside the namespace `LeanLCS`. The definitions used
in the statements are those of the library, which `Challenge.lean` copies verbatim.
-/

open Set Filter Function Bornology PiNat
open scoped Topology Pointwise Cardinal UniformConvergenceCLM

universe u

namespace LeanLCS

/-! ### Barrelled spaces: closed graph and open mapping theorems -/

/-- A topological vector space over `ℝ` or `ℂ` is barrelled if and only if every barrel is a
neighbourhood of zero. -/
theorem barrelledSpace_iff_forall_isBarrel_mem_nhds {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [ContinuousSMul ℝ E] :
    BarrelledSpace 𝕜 E ↔ ∀ (s : Set E), IsBarrel 𝕜 s → s ∈ 𝓝 0 :=
  _root_.barrelledSpace_iff_forall_isBarrel_mem_nhds

/-- **Characterization of barrelled spaces**: a locally convex space is barrelled if and only if
every pointwise bounded (that is, weak-* bounded) subset of its dual is equicontinuous. -/
theorem barrelledSpace_iff_forall_equicontinuous {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] :
    BarrelledSpace 𝕜 E ↔ ∀ (H : Set (StrongDual 𝕜 E)), (∀ x, IsVonNBounded 𝕜 ((fun φ : StrongDual 𝕜
      E ↦ φ x) '' H)) → Equicontinuous ((↑) : H → E → 𝕜) :=
  _root_.barrelledSpace_iff_forall_equicontinuous

/-- The **closed graph theorem** for a barrelled domain: a linear map with closed graph from a
barrelled space to a complete, first-countable, locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [BarrelledSpace 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [CompleteSpace F] [FirstCountableTopology F]
    (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g :=
  _root_.LinearMap.continuous_of_isClosed_graph_of_barrelledSpace g hg

/-- The **open mapping theorem** for a barrelled codomain: a continuous linear map from a complete,
first-countable, locally convex space onto a barrelled Hausdorff space is an open map. -/
theorem ContinuousLinearMap.isOpenMap_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [BarrelledSpace 𝕜 F]
    [T2Space F] (f : E →L[𝕜] F) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  _root_.ContinuousLinearMap.isOpenMap_of_barrelledSpace f hsurj

/-- A continuous linear bijection from a complete, first-countable, locally convex space onto a
barrelled Hausdorff space has a continuous inverse. -/
theorem LinearEquiv.continuous_symm_of_barrelledSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [BarrelledSpace 𝕜 F]
    [T2Space F] (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    Continuous e.symm :=
  _root_.LinearEquiv.continuous_symm_of_barrelledSpace e h

/-- The final locally convex topology for a family of maps from barrelled spaces is barrelled. In
particular locally convex direct sums and inductive limits of barrelled spaces are barrelled. -/
theorem locallyConvexFinalTopology.barrelledSpace {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : ι → Type*}
    {F : Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] (f : ∀ i, E i →ₗ[𝕜] F) [IsScalarTower ℝ 𝕜 F]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, BarrelledSpace 𝕜 (E i)] :
    @BarrelledSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) :=
  _root_.locallyConvexFinalTopology.barrelledSpace f

/-- A quotient of a barrelled module over a seminormed ring is barrelled. -/
theorem Submodule.Quotient.instBarrelledSpace {𝕜 : Type*} {E : Type*} [SeminormedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (N : Submodule 𝕜 E) :
    BarrelledSpace 𝕜 (E ⧸ N) :=
  _root_.Submodule.Quotient.instBarrelledSpace N

/-! ### Pták theory -/

/-- A complete, first-countable, locally convex space is a Pták space. -/
theorem PtakSpace.of_completeSpace_firstCountableTopology {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] :
    PtakSpace 𝕜 E :=
  _root_.PtakSpace.of_completeSpace_firstCountableTopology

/-- **Pták's closed graph theorem**: a linear map with closed graph from a barrelled locally convex
space to an infra-Pták (`B_r`-complete) locally convex space is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ F] [LocallyConvexSpace ℝ E] [BarrelledSpace 𝕜 E] [InfraPtakSpace 𝕜 F]
    (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g :=
  _root_.LinearMap.continuous_of_isClosed_graph_of_infraPtakSpace g hg

/-- **Pták's open mapping theorem**: a continuous linear map from a Pták (`B`-complete) locally
convex space onto a barrelled Hausdorff locally convex space is an open map. -/
theorem ContinuousLinearMap.isOpenMap_of_ptakSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [LocallyConvexSpace ℝ E] [PtakSpace 𝕜 E] [LocallyConvexSpace ℝ F] [BarrelledSpace 𝕜 F]
    [T2Space F] (f : E →L[𝕜] F) (hf : Function.Surjective f) :
    IsOpenMap f :=
  _root_.ContinuousLinearMap.isOpenMap_of_ptakSpace f hf

/-! ### Duality -/

/-- The **bipolar theorem** for a locally convex space `E` and its continuous dual: a nonempty,
closed, `ℝ`-convex, balanced set is its own bipolar. -/
theorem StrongDual.bipolar_eq_self {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set E} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) :
    (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 s) = s :=
  _root_.StrongDual.bipolar_eq_self hc hb hcl hne

/-- The **bipolar theorem** for a bilinear pairing: a nonempty, weakly closed, `ℝ`-convex, balanced
set is its own bipolar. -/
theorem LinearMap.flip_polar_polar_eq_self {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {s : Set (WeakBilin B)} (hc : Convex ℝ s) (hb : Balanced 𝕜 s)
    (hcl : IsClosed s) (hne : s.Nonempty) :
    B.flip.polar (B.polar s) = s :=
  _root_.LinearMap.flip_polar_polar_eq_self B hc hb hcl hne

/-- The **Alaoglu–Bourbaki theorem**: the polar of a neighbourhood of zero in a topological vector
space `E` over a proper nontrivially normed field is a compact subset of `WeakDual 𝕜 E`. For normed
spaces this is `WeakDual.isCompact_polar`. -/
theorem WeakDual.isCompact_polar_of_mem_nhds {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [ProperSpace 𝕜] {U : Set E} (hU : U ∈ 𝓝 0) :
    IsCompact (WeakDual.polar 𝕜 U) :=
  _root_.WeakDual.isCompact_polar_of_mem_nhds hU

/-- A subset of a locally convex space is von Neumann bounded if and only if every continuous linear
functional is bounded on it. -/
theorem Bornology.isVonNBounded_iff_forall_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] {A : Set E} :
    IsVonNBounded 𝕜 A ↔ ∀ (φ : StrongDual 𝕜 E), ∃ C, ∀ x ∈ A, ‖φ x‖ ≤ C :=
  _root_.Bornology.isVonNBounded_iff_forall_strongDual

/-- The **Mackey–Arens theorem**: a locally convex vector space topology on `E` is compatible with a
pairing `B` of `E` and `F` if and only if the functionals `x ↦ B x y` are continuous, which says
that the topology is finer than the weak topology `σ(E, F)`, and the topology is coarser than the
Mackey topology `τ(E, F)`. -/
theorem LinearMap.isCompatibleTopology_iff_mackeyTopology_le {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    B.IsCompatibleTopology ↔ (∀ y, Continuous fun x ↦ (B x) y) ∧ B.mackeyTopology ≤ (inferInstance :
      TopologicalSpace E) :=
  _root_.LinearMap.isCompatibleTopology_iff_mackeyTopology_le B

/-- The **Banach–Dieudonné theorem**. Let `E` be a first-countable topological vector space and let
`W` be a set of continuous linear functionals that contains zero and whose complement is almost
weak-\* closed. Then `W` contains the polar of a compact subset of `E`. -/
theorem StrongDual.exists_isCompact_polar_subset {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] {W : Set (StrongDual 𝕜 E)} (hW0 : 0 ∈ W)
    (hW : StrongDual.IsAlmostWeakStarClosed Wᶜ) :
    ∃ S, IsCompact S ∧ StrongDual.polar 𝕜 S ⊆ W :=
  _root_.StrongDual.exists_isCompact_polar_subset hW0 hW

/-- The **Krein–Šmulian theorem**. In the dual of a complete, first-countable, locally convex space
every `ℝ`-convex almost weak-\* closed set is weak-\* closed. -/
theorem StrongDual.isClosed_of_isAlmostWeakStarClosed {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] {C : Set (StrongDual 𝕜 E)} (hC : Convex ℝ C)
    (h : StrongDual.IsAlmostWeakStarClosed C) :
    IsClosed (WeakDual.toStrongDual ⁻¹' C) :=
  _root_.StrongDual.isClosed_of_isAlmostWeakStarClosed hC h

/-- A locally convex space is complete if and only if every linear form on its dual that is weak-*
continuous on each zero-neighbourhood polar is evaluation at a point. -/
theorem StrongDual.completeSpace_iff_forall_exists_eq_apply {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    CompleteSpace E ↔ ∀ (f : StrongDual 𝕜 E →ₗ[𝕜] 𝕜), (∀ U ∈ 𝓝 0, ContinuousOn (fun φ ↦ f
      (WeakDual.toStrongDual φ)) (WeakDual.polar 𝕜 U)) → ∃ x, ∀ (φ : StrongDual 𝕜 E), f φ = φ x :=
  _root_.StrongDual.completeSpace_iff_forall_exists_eq_apply

/-- A functional continuous for compact convergence on the dual of a complete locally convex space
is evaluation at a point of the original space. -/
theorem CompactConvergenceCLM.exists_forall_apply_eq {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    (Λ : CompactConvergenceCLM (RingHom.id 𝕜) E 𝕜 →L[𝕜] 𝕜) :
    ∃ x, ∀ (f : CompactConvergenceCLM (RingHom.id 𝕜) E 𝕜), Λ f = f x :=
  _root_.CompactConvergenceCLM.exists_forall_apply_eq Λ

/-- In a complete locally convex space every compact set lies in a compact `ℝ`-convex balanced set
containing zero. -/
theorem IsCompact.exists_isCompact_convex_balanced_superset {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) :
    ∃ K', K ⊆ K' ∧ IsCompact K' ∧ Convex ℝ K' ∧ Balanced 𝕜 K' ∧ 0 ∈ K' :=
  _root_.IsCompact.exists_isCompact_convex_balanced_superset hK

/-- **Milman's converse**: the extreme points of a compact closed `ℝ`-convex hull belong to the
closure of the generating set. -/
theorem IsCompact.extremePoints_closure_convexHull_subset_closure {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hC : IsCompact (closure (convexHull ℝ s))) :
    Set.extremePoints ℝ (closure (convexHull ℝ s)) ⊆ closure s :=
  _root_.IsCompact.extremePoints_closure_convexHull_subset_closure hC

/-! ### Bornological and ultrabornological spaces -/

/-- A real or complex topological vector space is bornological if and only if every `ℝ`-convex,
balanced, bornivorous set is a neighbourhood of zero. -/
theorem bornologicalSpace_iff_forall_mem_nhds_zero {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] :
    BornologicalSpace 𝕜 E ↔ ∀ (s : Set E), Convex ℝ s → Balanced 𝕜 s → IsBornivorous 𝕜 s → s ∈ 𝓝 0 :=
  _root_.bornologicalSpace_iff_forall_mem_nhds_zero

/-- A linear map from a bornological space to a polynormable space, in particular to a locally
convex space, that maps bounded sets to bounded sets is continuous. -/
theorem LinearMap.continuous_of_forall_isVonNBounded_image {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [BornologicalSpace 𝕜 E] {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] [PolynormableSpace 𝕜 F] (f : E →ₗ[𝕜] F)
    (hf : ∀ (t : Set E), IsVonNBounded 𝕜 t → IsVonNBounded 𝕜 (f '' t)) :
    Continuous f :=
  _root_.LinearMap.continuous_of_forall_isVonNBounded_image f hf

/-- A first-countable topological vector space is bornological. In particular metrizable locally
convex spaces and normed spaces are bornological. -/
theorem BornologicalSpace.of_firstCountableTopology {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FirstCountableTopology E] :
    BornologicalSpace 𝕜 E :=
  _root_.BornologicalSpace.of_firstCountableTopology

/-- A complete, first-countable, Hausdorff locally convex space (a Fréchet space) is
ultrabornological: its topology is the final locally convex topology for the maps `lp.tsumSMulCLM x
hx : ℓ¹(ℕ, 𝕜) → E`, where `x` ranges over the sequences in `E` that tend to zero. -/
theorem UltrabornologicalSpace.of_completeSpace_firstCountableTopology {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E] [T2Space E] :
    UltrabornologicalSpace 𝕜 E :=
  _root_.UltrabornologicalSpace.of_completeSpace_firstCountableTopology

/-- An ultrabornological space is barrelled: a lower semicontinuous seminorm is continuous on every
complete seminormed space, which is barrelled by Baire's theorem. -/
theorem UltrabornologicalSpace.toBarrelledSpace {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [UltrabornologicalSpace 𝕜 E] :
    BarrelledSpace 𝕜 E :=
  _root_.UltrabornologicalSpace.toBarrelledSpace

/-- **A quasi-complete Hausdorff bornological locally convex space is ultrabornological.** In such a
space the closed bounded disks are Banach disks. -/
theorem UltrabornologicalSpace.of_bornologicalSpace_of_quasiCompleteSpace {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    [BornologicalSpace 𝕜 E] [QuasiCompleteSpace 𝕜 E] :
    UltrabornologicalSpace 𝕜 E :=
  _root_.UltrabornologicalSpace.of_bornologicalSpace_of_quasiCompleteSpace

/-- The final locally convex topology for a family of maps from ultrabornological spaces is
ultrabornological. In particular inductive limits of ultrabornological spaces, such as LF spaces,
are ultrabornological. The spaces are taken in one universe. -/
theorem locallyConvexFinalTopology.ultrabornologicalSpace {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {E : ι → Type u} {F : Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    [∀ i, UltrabornologicalSpace 𝕜 (E i)] (f : ∀ i, E i →ₗ[𝕜] F) :
    @UltrabornologicalSpace 𝕜 F _ _ _ (locallyConvexFinalTopology f) :=
  _root_.locallyConvexFinalTopology.ultrabornologicalSpace f

/-! ### Quasi-barrelled, reflexive and Montel spaces -/

/-- A locally convex space is quasi-barrelled if and only if every strongly bounded subset of its
dual is equicontinuous. -/
theorem quasiBarrelledSpace_iff_forall_equicontinuous {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    QuasiBarrelledSpace 𝕜 E ↔ ∀ (H : Set (StrongDual 𝕜 E)), IsVonNBounded 𝕜 H → Equicontinuous ((↑)
      : H → E → 𝕜) :=
  _root_.quasiBarrelledSpace_iff_forall_equicontinuous

/-- A locally convex space is **reflexive if and only if it is semi-reflexive and barrelled**. -/
theorem reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] :
    ReflexiveSpace 𝕜 E ↔ SemiReflexiveSpace 𝕜 E ∧ BarrelledSpace 𝕜 E :=
  _root_.reflexiveSpace_iff_semiReflexiveSpace_and_barrelledSpace

/-- A Hausdorff locally convex space is **semi-reflexive if and only if every bounded set lies in a
weakly compact, `ℝ`-convex, balanced set**; in particular if and only if its bounded sets are
relatively weakly compact. -/
theorem semiReflexiveSpace_iff_forall_isVonNBounded (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] :
    SemiReflexiveSpace 𝕜 E ↔ ∀ (S : Set E), IsVonNBounded 𝕜 S → ∃ K ∈ (topDualPairing 𝕜
      E).mackeyFamily, toWeakSpace 𝕜 E '' S ⊆ K :=
  _root_.semiReflexiveSpace_iff_forall_isVonNBounded 𝕜 E

/-- A space is semi-reflexive if and only if the strong topology `β(E', E)` on its dual is coarser
than the Mackey topology `τ(E', E)`; this is the Mackey–Arens theorem for the pairing of the dual
and the space. -/
theorem semiReflexiveSpace_iff_mackeyTopology_le (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    SemiReflexiveSpace 𝕜 E ↔ (topDualPairing 𝕜 E).mackeyTopology ≤ (inferInstance : TopologicalSpace
      (StrongDual 𝕜 E)) :=
  _root_.semiReflexiveSpace_iff_mackeyTopology_le 𝕜 E

-- With the library imported, instance search finds `ContinuousSMul 𝕜 𝕜` through
-- `IsModuleTopology`; the Challenge, which imports only Mathlib, finds it through
-- `PolynormableSpace`. The local priority reproduces the Challenge statement exactly.
attribute [local instance 2000] PolynormableSpace.continuousSMul in
/-- The strong dual of a reflexive locally convex space is reflexive, including under the
non-Hausdorff convention used here. This is Schaefer–Wolff, IV §5.6, Corollary 1, using
semi-reflexivity and barrelledness of the strong dual. -/
theorem ReflexiveSpace.strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [ReflexiveSpace 𝕜 E] :
    ReflexiveSpace 𝕜 (StrongDual 𝕜 E) :=
  _root_.ReflexiveSpace.strongDual

/-- A barrelled locally convex Montel space is reflexive. -/
theorem MontelSpace.reflexiveSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E] [MontelSpace 𝕜 E] [BarrelledSpace 𝕜 E] :
    ReflexiveSpace 𝕜 E :=
  _root_.MontelSpace.reflexiveSpace

/-- The strong dual of a quasi-barrelled Hausdorff Montel space is Montel. -/
theorem MontelSpace.strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [MontelSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [QuasiBarrelledSpace 𝕜 E] :
    MontelSpace 𝕜 (StrongDual 𝕜 E) :=
  _root_.MontelSpace.strongDual

/-- The strong dual of a Hausdorff Montel locally convex space is barrelled. This follows from
semi-reflexivity, even without barrelledness of the original space. -/
theorem MontelSpace.barrelledSpace_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [MontelSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E] :
    BarrelledSpace 𝕜 (StrongDual 𝕜 E) :=
  _root_.MontelSpace.barrelledSpace_strongDual

/-- A closed subspace of a semi-reflexive space is reflexive if it is quasi-barrelled. -/
theorem ReflexiveSpace.submodule_of_quasiBarrelledSpace {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [SemiReflexiveSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) [QuasiBarrelledSpace 𝕜 M] :
    ReflexiveSpace 𝕜 M :=
  _root_.ReflexiveSpace.submodule_of_quasiBarrelledSpace M hM

/-- Arbitrary products of semi-reflexive spaces are semi-reflexive. -/
theorem SemiReflexiveSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, SemiReflexiveSpace 𝕜 (E i)] :
    SemiReflexiveSpace 𝕜 (∀ i, E i) :=
  _root_.SemiReflexiveSpace.pi

/-- Arbitrary products of reflexive locally convex spaces are reflexive. -/
theorem ReflexiveSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, ReflexiveSpace 𝕜 (E i)] :
    ReflexiveSpace 𝕜 (∀ i, E i) :=
  _root_.ReflexiveSpace.pi

/-- Arbitrary products of Montel spaces have the Heine–Borel property. -/
theorem MontelSpace.pi {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)] [∀ i, ContinuousSMul 𝕜 (G i)] [∀ i, MontelSpace 𝕜 (G i)]
    [∀ i, T2Space (G i)] :
    MontelSpace 𝕜 (∀ i, G i) :=
  _root_.MontelSpace.pi

/-- Arbitrary products of quasi-barrelled locally convex spaces are quasi-barrelled. -/
theorem QuasiBarrelledSpace.pi {𝕜 : Type*} {ι : Type*} [RCLike 𝕜] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [∀ i, QuasiBarrelledSpace 𝕜 (E i)] :
    QuasiBarrelledSpace 𝕜 (∀ i, E i) :=
  _root_.QuasiBarrelledSpace.pi

/-! ### Completeness of strong duals -/

/-- The strong dual of a bornological space over a complete nontrivially normed field is complete,
without metrizability or completeness assumptions on the original space. -/
theorem BornologicalSpace.completeSpace_strongDual {𝕜 : Type*} {E : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [BornologicalSpace 𝕜 E] :
    CompleteSpace (StrongDual 𝕜 E) :=
  _root_.BornologicalSpace.completeSpace_strongDual

/-- The strong dual of a quasi-barrelled space is quasi-complete. In particular this applies to
barrelled spaces. -/
theorem QuasiBarrelledSpace.quasiCompleteSpace_strongDual {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [QuasiBarrelledSpace 𝕜 E] :
    QuasiCompleteSpace 𝕜 (StrongDual 𝕜 E) :=
  _root_.QuasiBarrelledSpace.quasiCompleteSpace_strongDual

/-- The strong dual of Schwartz space is complete, over either the real or complex scalars. No
completeness assumption on the target of the Schwartz functions is needed. -/
theorem SchwartzMap.instCompleteSpaceStrongDual {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] :
    CompleteSpace (StrongDual 𝕜 (SchwartzMap E F)) :=
  _root_.SchwartzMap.instCompleteSpaceStrongDual

/-- Test-function spaces are bornological: their topology is final for the bornological spaces of
functions supported in fixed compact subsets. -/
theorem TestFunction.instBornologicalSpace {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {Ω : TopologicalSpace.Opens E} {n : ℕ∞} :
    BornologicalSpace 𝕜 (TestFunction Ω F n) :=
  _root_.TestFunction.instBornologicalSpace

/-- The real or complex strong dual of test-function space is complete for uniform convergence on
bounded sets, even when the normed target of the test functions is incomplete. -/
theorem TestFunction.instCompleteSpaceStrongDual {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {Ω : TopologicalSpace.Opens E} {n : ℕ∞} :
    CompleteSpace (StrongDual 𝕜 (TestFunction Ω F n)) :=
  _root_.TestFunction.instCompleteSpaceStrongDual

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
    ∃ n, B ⊆ Set.range (f n) :=
  _root_.IsStrictInductiveLimit.exists_subset_range_of_isVonNBounded h hjcl hB

/-- A countable strict inductive limit of complete locally convex spaces is complete. -/
theorem IsStrictInductiveLimit.completeSpace {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} {F : Type*}
    [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)] [∀ n, Module ℝ (E n)]
    [∀ n, IsScalarTower ℝ 𝕜 (E n)] [∀ n, UniformSpace (E n)] [∀ n, IsUniformAddGroup (E n)]
    [∀ n, ContinuousSMul 𝕜 (E n)] [∀ n, LocallyConvexSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [uF : UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul 𝕜 F] {j : ∀ n, E n →L[𝕜] E (n + 1)} {f : ∀ n, E n →ₗ[𝕜] F}
    (h : IsStrictInductiveLimit j f) (hFtop : uF.toTopologicalSpace = locallyConvexFinalTopology f) :
    CompleteSpace F :=
  _root_.IsStrictInductiveLimit.completeSpace h hFtop

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
    ReflexiveSpace 𝕜 F :=
  _root_.IsStrictInductiveLimit.reflexiveSpace h hjcl htop

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
    MontelSpace 𝕜 F :=
  _root_.IsStrictInductiveLimit.montelSpace h hjcl htop

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
    Continuous A :=
  _root_.LinearMap.continuous_of_isSeqClosed_graph_of_ultrabornologicalSpace A hA

/-- **De Wilde's open mapping theorem**: a linear map with sequentially closed graph from a webbed
locally convex space onto an ultrabornological space is open, Köthe II §35.3.(5). -/
theorem LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} {F : Type*} [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [UltrabornologicalSpace 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F] [WebbedSpace F] (A : F →ₗ[𝕜] E)
    (hA : IsSeqClosed (A.graph : Set (F × E))) (hsurj : Function.Surjective A) :
    IsOpenMap A :=
  _root_.LinearMap.isOpenMap_of_isSeqClosed_graph_of_ultrabornologicalSpace A hA hsurj

end LeanLCS
