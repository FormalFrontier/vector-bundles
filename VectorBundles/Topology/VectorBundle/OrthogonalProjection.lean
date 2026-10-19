/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalAddition
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.VectorBundle.Hom
import VectorBundles.Topology.VectorBundle.CoordinateMap

/-!
# Orthogonal projections and continuous projector fields

The inverse of orthogonal addition, followed by the first or second total-space
projection of the fiberwise product, gives the two orthogonal projections of an
ambient vector bundle with a supplied continuous Hermitian metric. The first target
retains the intrinsic subbundle total topology; the second has the ambient-induced
total topology. The domain retains the original ambient total topology.

Mathlib's `Submodule.projectionOntoL` and `Submodule.projectionL` give the
continuous-linear maps on the original fibers. Their intrinsic-valued projection
field and both ambient-valued projection fields are continuous sections of the
Hom bundles with models `F →L[𝕜] G` and `F →L[𝕜] F`, respectively. The two ambient
fields use the same Hom-bundle topology. No complement-valued Hom bundle is chosen.

## Implementation notes

Only the ambient model is assumed finite-dimensional; the subbundle model is arbitrary,
and the base need not be nonempty, separated or paracompact. Continuity follows from
the inverse addition homeomorphism and the canonical fiberwise-product topology:
its inducing diagonal into the product of total spaces is continuous, as are the
two product projections. The underlying functions are fixed compositions with the
inverse addition homeomorphism. The field assertions use Mathlib's existing
continuous-linear projectors and Hom topology with the given model norms and
original coupled bundle structures; no new projector data or fiber norms are
introduced. Finite-dimensionality is needed for the source model, not globally for
the intrinsic target model. This module does not construct a metric, isometric
charts or a stable-triviality theorem.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.3, p. 12: the geometric orthogonal-splitting construction for a
  given metric. The projection maps here are derived components of that splitting,
  not a separately stated assertion of the proposition; scalars are generalized to `RCLike`.
* Mathlib's fiber-bundle constructions, by Nicolò Cavalleri, Sébastien Gouëzel,
  Heather Macbeth and Floris van Doorn; its continuous-map product projections.
* Mathlib's topological complements and continuous-linear projections, by Anatole
  Dedecker and Sharvil Kesarwani, and its Hom-bundle construction by Heather Macbeth
  and Floris van Doorn.
-/

@[expose] public section

open Bundle

namespace Bundle.ContinuousHermitianMetric

universe u𝕜 uB uF uG uE

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
  [FiniteDimensional 𝕜 F]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
  (hS : Topology.IsEmbedding
    (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))

local notation "C" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g b)) (S b))
local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))
local notation "tC" => TopologicalSpace.induced
  (fun p : TotalSpace H C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance
local notation "tProd" => @FiberBundle.Prod.topologicalSpace B G (fun b ↦ S b) H C
  inferInstance tC
local notation "Φ" => @Homeomorph.toEquiv _ _ tProd inferInstance
  (g.orthogonalAdditionHomeomorph S hS)

/-- The continuous total-space projection onto an embedded intrinsic submodule
bundle along its metric orthogonal complement. The target has the given intrinsic
total topology. Its function is the first total projection after inverse addition. -/
noncomputable def orthogonalProjectionTotal :
    C(TotalSpace F E, TotalSpace G (fun b ↦ S b)) where
  toFun := (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
    TotalSpace.mk' G p.proj p.2.1) ∘ (Φ).symm
  continuous_toFun := by
    let : TopologicalSpace (TotalSpace H C) := tC
    exact (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous.fst.comp
      (g.orthogonalAdditionHomeomorph S hS).continuous_invFun

/-- The continuous total-space projection onto the metric orthogonal family of an
embedded intrinsic submodule bundle. The target has the ambient-induced total
topology. Its function is the second total projection after inverse addition. -/
noncomputable def orthogonalComplementProjectionTotal :
    @ContinuousMap (TotalSpace F E) (TotalSpace H C) inferInstance tC := by
  letI : TopologicalSpace (TotalSpace H C) := tC
  exact
    { toFun := (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
        TotalSpace.mk' H p.proj p.2.2) ∘ (Φ).symm
      continuous_toFun := by
        exact (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous.snd.comp
          (g.orthogonalAdditionHomeomorph S hS).continuous_invFun }

private theorem orthogonalAdditionHomeomorph_symm_proj (p : TotalSpace F E) :
    ((Φ).symm p).proj = p.proj := by
  have h := congrArg TotalSpace.proj ((Φ).apply_symm_apply p)
  exact h

/-- Projection onto the intrinsic subbundle preserves the base point. -/
@[simp]
theorem orthogonalProjectionTotal_proj (p : TotalSpace F E) :
    (g.orthogonalProjectionTotal S hS p).proj = p.proj :=
  orthogonalAdditionHomeomorph_symm_proj g S hS p

/-- Projection onto the orthogonal family preserves the base point. -/
@[simp]
theorem orthogonalComplementProjectionTotal_proj (p : TotalSpace F E) :
    (g.orthogonalComplementProjectionTotal S hS p).proj = p.proj :=
  orthogonalAdditionHomeomorph_symm_proj g S hS p

/-- On a sum of orthogonal components, the intrinsic projection returns the first
component, as a point of the intrinsic total space. -/
@[simp]
theorem orthogonalProjectionTotal_apply_add (b : B) (s : S b) (c : C b) :
    g.orthogonalProjectionTotal S hS (TotalSpace.mk' F b ((s : E b) + (c : E b))) =
      TotalSpace.mk' G b s := by
  have h := (Φ).symm_apply_apply ⟨b, s, c⟩
  exact congrArg
    (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' G (E := fun b ↦ S b) p.proj p.2.1) h

/-- On a sum of orthogonal components, the complement projection returns the second
component, as a point of the ambient-induced orthogonal total space. -/
@[simp]
theorem orthogonalComplementProjectionTotal_apply_add (b : B) (s : S b) (c : C b) :
    g.orthogonalComplementProjectionTotal S hS
        (TotalSpace.mk' F b ((s : E b) + (c : E b))) = TotalSpace.mk' H b c := by
  have h := (Φ).symm_apply_apply ⟨b, s, c⟩
  exact congrArg
    (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' H (E := C) p.proj p.2.2) h

/-- The total intrinsic projection agrees on each fiber with the algebraic
projection onto the intrinsic submodule along its orthogonal complement. -/
theorem orthogonalProjectionTotal_apply (b : B) (v : E b) :
    g.orthogonalProjectionTotal S hS (TotalSpace.mk' F b v) =
      TotalSpace.mk' G b
        ((S b).projectionOnto (C b) (g.orthogonal_isCompl S b) v) := by
  let s : S b := (S b).projectionOnto (C b) (g.orthogonal_isCompl S b) v
  let c : C b := ⟨v - (s : E b),
    Submodule.sub_projection_mem (g.orthogonal_isCompl S b) v⟩
  have hsum : (s : E b) + (c : E b) = v := by
    change (s : E b) + (v - (s : E b)) = v
    rw [add_comm, sub_add_cancel]
  simpa only [hsum] using
    g.orthogonalProjectionTotal_apply_add S hS b s c

/-- The total complement projection agrees on each fiber with the algebraic
projection onto that complement along the intrinsic submodule. -/
theorem orthogonalComplementProjectionTotal_apply (b : B) (v : E b) :
    g.orthogonalComplementProjectionTotal S hS (TotalSpace.mk' F b v) =
      TotalSpace.mk' H b
        ((C b).projectionOnto (S b) (g.orthogonal_isCompl S b).symm v) := by
  let c : C b := (C b).projectionOnto (S b) (g.orthogonal_isCompl S b).symm v
  let s : S b := ⟨v - (c : E b),
    Submodule.sub_projection_mem (g.orthogonal_isCompl S b).symm v⟩
  have hsum : (s : E b) + (c : E b) = v := sub_add_cancel _ _
  simpa only [hsum] using
    g.orthogonalComplementProjectionTotal_apply_add S hS b s c

-- These are propositions about the original fiber topology. They choose no
-- topology, bundle structure, or norm, and need no intrinsic subbundle data.
omit [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)] in
private theorem orthogonal_isTopCompl (b : B) : (S b).IsTopCompl (C b) := by
  let e := VectorBundle.continuousLinearEquivAt 𝕜 F E b
  let : IsTopologicalAddGroup (E b) := e.toContinuousAddEquiv.isTopologicalAddGroup
  let : ContinuousSMul 𝕜 (E b) := e.continuousSMul
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  let : IsModuleTopology 𝕜 (E b) := IsModuleTopology.iso e.symm
  exact ⟨g.orthogonal_isCompl S b, IsModuleTopology.continuous_of_linearMap _⟩

omit [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)] in
private theorem orthogonal_isTopCompl_symm (b : B) : (C b).IsTopCompl (S b) := by
  let : IsTopologicalAddGroup (E b) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F E b).toContinuousAddEquiv.isTopologicalAddGroup
  exact (orthogonal_isTopCompl g S b).symm

-- Both topologies below are Mathlib's atlas Hom topology. The inferred DATA
-- arguments are the original model norms, fiber/total topologies, and coupled
-- FiberBundle/VectorBundle structures in the telescope above. Only the last two
-- fiber-operation arguments are supplied by transport, and both are propositions.
local notation "homSTopology" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    _ _ _ _ (RingHom.id 𝕜) _ F _ _ E _ _ _
    G _ _ (fun b ↦ S b) _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv
        (VectorBundle.continuousLinearEquivAt 𝕜 G (fun b ↦ S b) b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt 𝕜 G (fun b ↦ S b) b)) _

local notation "homETopology" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    _ _ _ _ (RingHom.id 𝕜) _ F _ _ E _ _ _
    F _ _ E _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv
        (VectorBundle.continuousLinearEquivAt 𝕜 F E b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt 𝕜 F E b)) _

include hS in
/-- The continuous-linear projections onto the intrinsic submodule form a
continuous section of the Hom bundle from the ambient bundle to the given
intrinsic bundle, with the original model norms and bundle structures. -/
theorem continuous_orthogonalProjectionOntoL :
    @Continuous B (TotalSpace (F →L[𝕜] G) (fun b ↦ E b →L[𝕜] S b))
      inferInstance homSTopology
      (fun b ↦ TotalSpace.mk' (F →L[𝕜] G) b
        ((S b).projectionOntoL (C b) (by exact orthogonal_isTopCompl g S b))) := by
  let : ∀ b, IsTopologicalAddGroup (S b) := fun b ↦
    ContinuousAddEquiv.isTopologicalAddGroup
      (VectorBundle.continuousLinearEquivAt 𝕜 G (fun b ↦ S b) b).toContinuousAddEquiv
  let : ∀ b, ContinuousSMul 𝕜 (S b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 G (fun b ↦ S b) b).continuousSMul
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  let φ : ∀ b, E b →ₗ[𝕜] S b := fun b ↦
    (S b).projectionOnto (C b) (g.orthogonal_isCompl S b)
  have hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' (E := fun b ↦ S b) G p.proj (φ p.proj p.snd)) := by
    refine (g.orthogonalProjectionTotal S hS).continuous.congr ?_
    intro p
    exact g.orthogonalProjectionTotal_apply S hS p.proj p.snd
  refine continuous_iff_continuousAt.2 fun b₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  let e := trivializationAt F E b₀
  let eS := trivializationAt G (fun b ↦ S b) b₀
  -- Finite-dimensionality of the source upgrades joint continuity to operator-norm continuity.
  exact (e.continuousOn_linearMapAt_comp_of_isModuleTopology eS φ hφ).continuousAt
    (Filter.inter_mem
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b₀))
      (eS.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G (fun b ↦ S b) b₀)))

include hS in
/-- The ambient-valued continuous-linear projections onto the intrinsic submodule
form a continuous section of the ambient endomorphism Hom bundle. -/
theorem continuous_orthogonalProjectionL :
    @Continuous B (TotalSpace (F →L[𝕜] F) (fun b ↦ E b →L[𝕜] E b))
      inferInstance homETopology
      (fun b ↦ TotalSpace.mk' (F →L[𝕜] F) b
        ((S b).projectionL (C b) (by exact orthogonal_isTopCompl g S b))) := by
  let : ∀ b, IsTopologicalAddGroup (E b) := fun b ↦
    ContinuousAddEquiv.isTopologicalAddGroup
      (VectorBundle.continuousLinearEquivAt 𝕜 F E b).toContinuousAddEquiv
  let : ∀ b, ContinuousSMul 𝕜 (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F E b).continuousSMul
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  let φ : ∀ b, E b →ₗ[𝕜] E b := fun b ↦
    (S b).projection (C b) (g.orthogonal_isCompl S b)
  have hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' F p.proj (φ p.proj p.snd)) := by
    refine (hS.continuous.comp (g.orthogonalProjectionTotal S hS).continuous).congr ?_
    intro p
    exact congrArg
      (fun q : TotalSpace G (fun b ↦ S b) ↦
        TotalSpace.mk' F q.proj (q.2 : E q.proj))
      (g.orthogonalProjectionTotal_apply S hS p.proj p.snd)
  refine continuous_iff_continuousAt.2 fun b₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  let e := trivializationAt F E b₀
  have hU := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b₀)
  exact (e.continuousOn_linearMapAt_comp_of_isModuleTopology e φ hφ).continuousAt
    (Filter.inter_mem hU hU)

include hS in
/-- The ambient-valued continuous-linear projections onto the orthogonal family
form a continuous section of the same ambient endomorphism Hom bundle as the
projections onto the intrinsic submodule. -/
theorem continuous_orthogonalComplementProjectionL :
    @Continuous B (TotalSpace (F →L[𝕜] F) (fun b ↦ E b →L[𝕜] E b))
      inferInstance homETopology
      (fun b ↦ TotalSpace.mk' (F →L[𝕜] F) b
        ((C b).projectionL (S b) (by exact orthogonal_isTopCompl_symm g S b))) := by
  let : ∀ b, IsTopologicalAddGroup (E b) := fun b ↦
    ContinuousAddEquiv.isTopologicalAddGroup
      (VectorBundle.continuousLinearEquivAt 𝕜 F E b).toContinuousAddEquiv
  let : ∀ b, ContinuousSMul 𝕜 (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F E b).continuousSMul
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  let : TopologicalSpace (TotalSpace H C) := tC
  have hi : Topology.IsInducing (fun q : TotalSpace H C ↦
      TotalSpace.mk' F q.proj (q.2 : E q.proj)) := ⟨rfl⟩
  let φ : ∀ b, E b →ₗ[𝕜] E b := fun b ↦
    (C b).projection (S b) (g.orthogonal_isCompl S b).symm
  have hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' F p.proj (φ p.proj p.snd)) := by
    refine (hi.continuous.comp
      (g.orthogonalComplementProjectionTotal S hS).continuous).congr ?_
    intro p
    exact congrArg
      (fun q : TotalSpace H C ↦ TotalSpace.mk' F q.proj (q.2 : E q.proj))
      (g.orthogonalComplementProjectionTotal_apply S hS p.proj p.snd)
  refine continuous_iff_continuousAt.2 fun b₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  let e := trivializationAt F E b₀
  have hU := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b₀)
  exact (e.continuousOn_linearMapAt_comp_of_isModuleTopology e φ hφ).continuousAt
    (Filter.inter_mem hU hU)

end Bundle.ContinuousHermitianMetric
