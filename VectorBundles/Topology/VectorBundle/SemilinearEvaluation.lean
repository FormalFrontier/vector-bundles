/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn, Sébastien Gouëzel, Sophie Morel, Yury Kudryashov,
  Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Evaluation in bundles of continuous semilinear maps

Evaluation of a continuous family of continuous `σ`-semilinear maps on a continuous family of
vectors is continuous, for an isometric homomorphism `σ` between possibly distinct scalar fields.
The maps and vectors lie over the same base map from an arbitrary topological space.
The two-argument versions allow two isometric homomorphisms into a common scalar field.

These results use the semilinear hom-bundle topology of
`Mathlib.Topology.VectorBundle.Hom`; no new topology is introduced. Only the model fibers,
not the bundle fibers themselves, are assumed normed.

## Implementation notes

The local proof follows `ContinuousWithinAt.clm_apply_of_inCoordinates` and
`ContinuousWithinAt.clm_bundle_apply` in Mathlib, by Heather Macbeth and Floris van Doorn.
Joint evaluation on the model fibers follows from uniform convergence on bounded sets, as in
`ContinuousMultilinearMap.instContinuousEval`, by Sébastien Gouëzel, Sophie Morel and
Yury Kudryashov.
The evaluation statements retain the codomain fiber-operation instances used to form Mathlib's
canonical hom-bundle topology and the additive and module structures on spaces of continuous maps.
For two arguments, the inner hom-fibers also need a joint scalar action. This action is transported
from their normed models along the preferred charts, without any further hypothesis.
Local notation supplies this proof to Mathlib's existing topology instance; it does not define
a topology or register an instance. No surjectivity assumption on either scalar homomorphism
is needed.

Two-argument evaluation is obtained by applying one-argument evaluation twice.
For the identity homomorphism the types and topology are definitionally those of Mathlib's
linear evaluation lemmas, independently of the proofs of the fiber laws.

## References

* Heather Macbeth and Floris van Doorn, `Mathlib.Topology.VectorBundle.Hom`.
* Sébastien Gouëzel, Sophie Morel and Yury Kudryashov,
  `Mathlib.Analysis.Normed.Module.Multilinear.Basic`.
-/

@[expose] public section

noncomputable section

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

section Model

variable {𝕜₁ 𝕜₂ F₁ F₂ : Type*}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] {σ : 𝕜₁ →+* 𝕜₂}

private lemma continuous_semilinear_apply :
    Continuous (fun p : (F₁ →SL[σ] F₂) × F₁ ↦ p.1 p.2) := by
  refine (UniformOnFun.continuousOn_eval₂ fun v ↦ ?_).comp_continuous
    (isUniformEmbedding_toUniformOnFun.isEmbedding.continuous.prodMap continuous_id)
    fun (f, v) ↦ f.cont.continuousAt
  exact ⟨Metric.ball v 1, NormedSpace.isVonNBounded_of_isBounded _ Metric.isBounded_ball,
    Metric.ball_mem_nhds _ zero_lt_one⟩

end Model

section OneVariable

variable {𝕜₁ 𝕜₂ B F₁ F₂ M : Type*}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]
  {b : M → B} {ϕ : ∀ m, E₁ (b m) →SL[σ] E₂ (b m)} {v : ∀ m, E₁ (b m)}
  {s : Set M} {x : M}

/-- A continuous family of continuous semilinear maps between vector bundles can be evaluated
on a continuous family of vectors over the same base map, with continuity within a set at a
point. This generalizes `ContinuousWithinAt.clm_bundle_apply` to an isometric scalar homomorphism.
The proof follows Mathlib's evaluation lemma in local coordinates. -/
lemma ContinuousWithinAt.clm_bundle_apply_semilinear
    (hϕ : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →SL[σ] F₂)
        (E := fun y ↦ E₁ y →SL[σ] E₂ y) (b m) (ϕ m)) s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  rw [← continuousWithinAt_insert_self] at hϕ hv ⊢
  rw [continuousWithinAt_hom_bundle] at hϕ
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hϕ.1, ?_⟩
  apply (continuous_semilinear_apply.continuousAt.comp_continuousWithinAt
    (hϕ.2.prodMk hv.2)).congr_of_eventuallyEq_of_mem ?_ (mem_insert x s)
  have h₁ : ∀ᶠ m in 𝓝[insert x s] x,
      b m ∈ (trivializationAt F₁ E₁ (b x)).baseSet := by
    apply hv.1
    exact (trivializationAt F₁ E₁ (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₁ E₁ (b x))
  have h₂ : ∀ᶠ m in 𝓝[insert x s] x,
      b m ∈ (trivializationAt F₂ E₂ (b x)).baseSet := by
    apply hϕ.1
    exact (trivializationAt F₂ E₂ (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ (b x))
  filter_upwards [h₁, h₂] with m hm h'm using by simp [inCoordinates_eq hm h'm, hm]

/-- Pointwise continuity of evaluation of continuous semilinear maps and vectors in bundles
above the same base map. -/
lemma ContinuousAt.clm_bundle_apply_semilinear
    (hϕ : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →SL[σ] F₂)
        (E := fun y ↦ E₁ y →SL[σ] E₂ y) (b m) (ϕ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  rw [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply_semilinear hv

/-- Continuity on a set of evaluation of continuous semilinear maps and vectors in bundles
above the same base map. -/
lemma ContinuousOn.clm_bundle_apply_semilinear
    (hϕ : ContinuousOn (fun m ↦ TotalSpace.mk' (F₁ →SL[σ] F₂)
        (E := fun y ↦ E₁ y →SL[σ] E₂ y) (b m) (ϕ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply_semilinear (hv x hx)

/-- Continuity of evaluation of continuous semilinear maps and vectors in bundles above the
same base map. -/
lemma Continuous.clm_bundle_apply_semilinear
    (hϕ : Continuous (fun m ↦ TotalSpace.mk' (F₁ →SL[σ] F₂)
        (E := fun y ↦ E₁ y →SL[σ] E₂ y) (b m) (ϕ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) := by
  rw [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply_semilinear hv

end OneVariable

section Identity

variable {𝕜 B F₁ F₂ M : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {b : M → B} {ϕ : ∀ m, E₁ (b m) →L[𝕜] E₂ (b m)} {v : ∀ m, E₁ (b m)}
  {s : Set M} {x : M}

/-- Specializing semilinear bundle evaluation to the identity scalar homomorphism recovers
`ContinuousWithinAt.clm_bundle_apply`, on its original linear maps and hom-bundle topology,
without any conversion of the hypotheses or conclusion. -/
lemma ContinuousWithinAt.clm_bundle_apply_id
    (hϕ : ContinuousWithinAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (b m) (ϕ m)) s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x :=
  hϕ.clm_bundle_apply_semilinear (σ := RingHom.id 𝕜) hv

end Identity

section TwoVariables

variable {𝕜₁ 𝕜₂ 𝕜₃ B F₁ F₂ F₃ M : Type*}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜₃ (E₃ x)]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜₃ F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜₃ F₃ E₃]

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜₃ (E₃ x)]

-- This is the existing iterated hom-bundle topology, with joint scalar multiplication on
-- the inner hom-fiber transported from its normed model. No scalar homomorphism is assumed
-- surjective.
local notation "hom₂Topology" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    _ _ _ _ σ₁₃ _ F₁ _ _ E₁ _ _ _
    (F₂ →SL[σ₂₃] F₃) _ _ (fun y ↦ E₂ y →SL[σ₂₃] E₃ y) _ _ _
    _ _ _ _ _ _ _ _
    (fun y ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt 𝕜₃ (F₂ →SL[σ₂₃] F₃)
        (fun z ↦ E₂ z →SL[σ₂₃] E₃ z) y)) _

variable {b : M → B} {ψ : ∀ m, E₁ (b m) →SL[σ₁₃] E₂ (b m) →SL[σ₂₃] E₃ (b m)}
  {v : ∀ m, E₁ (b m)} {w : ∀ m, E₂ (b m)} {s : Set M} {x : M}

/-- A continuous family of continuous maps semilinear in each of two variables can be evaluated
on two continuous families of vectors over the same base map, with continuity within a set at a
point. The two scalar homomorphisms have a common codomain, and need not be surjective.
The scalar action on the inner hom-fibers is transported from their normed models. -/
lemma ContinuousWithinAt.clm_bundle_apply₂_semilinear
    (hψ : @ContinuousWithinAt _ _ _ hom₂Topology (fun m ↦
      TotalSpace.mk' (F₁ →SL[σ₁₃] F₂ →SL[σ₂₃] F₃)
        (E := fun y ↦ E₁ y →SL[σ₁₃] E₂ y →SL[σ₂₃] E₃ y) (b m) (ψ m)) s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x := by
  let : ∀ y, ContinuousSMul 𝕜₃ (E₂ y →SL[σ₂₃] E₃ y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜₃ (F₂ →SL[σ₂₃] F₃)
      (fun z ↦ E₂ z →SL[σ₂₃] E₃ z) y).continuousSMul
  exact (hψ.clm_bundle_apply_semilinear hv).clm_bundle_apply_semilinear hw

/-- Pointwise continuity of two-argument semilinear evaluation in vector bundles above the same
base map. -/
lemma ContinuousAt.clm_bundle_apply₂_semilinear
    (hψ : @ContinuousAt _ _ _ hom₂Topology (fun m ↦
      TotalSpace.mk' (F₁ →SL[σ₁₃] F₂ →SL[σ₂₃] F₃)
        (E := fun y ↦ E₁ y →SL[σ₁₃] E₂ y →SL[σ₂₃] E₃ y) (b m) (ψ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x := by
  let : ∀ y, ContinuousSMul 𝕜₃ (E₂ y →SL[σ₂₃] E₃ y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜₃ (F₂ →SL[σ₂₃] F₃)
      (fun z ↦ E₂ z →SL[σ₂₃] E₃ z) y).continuousSMul
  exact (hψ.clm_bundle_apply_semilinear hv).clm_bundle_apply_semilinear hw

/-- Continuity on a set of two-argument semilinear evaluation in vector bundles above the same
base map. -/
lemma ContinuousOn.clm_bundle_apply₂_semilinear
    (hψ : @ContinuousOn _ _ _ hom₂Topology (fun m ↦
      TotalSpace.mk' (F₁ →SL[σ₁₃] F₂ →SL[σ₂₃] F₃)
        (E := fun y ↦ E₁ y →SL[σ₁₃] E₂ y →SL[σ₂₃] E₃ y) (b m) (ψ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s := by
  let : ∀ y, ContinuousSMul 𝕜₃ (E₂ y →SL[σ₂₃] E₃ y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜₃ (F₂ →SL[σ₂₃] F₃)
      (fun z ↦ E₂ z →SL[σ₂₃] E₃ z) y).continuousSMul
  exact (hψ.clm_bundle_apply_semilinear hv).clm_bundle_apply_semilinear hw

/-- Continuity of two-argument semilinear evaluation in vector bundles above the same base map. -/
lemma Continuous.clm_bundle_apply₂_semilinear
    (hψ : @Continuous _ _ _ hom₂Topology (fun m ↦
      TotalSpace.mk' (F₁ →SL[σ₁₃] F₂ →SL[σ₂₃] F₃)
        (E := fun y ↦ E₁ y →SL[σ₁₃] E₂ y →SL[σ₂₃] E₃ y) (b m) (ψ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) := by
  let : ∀ y, ContinuousSMul 𝕜₃ (E₂ y →SL[σ₂₃] E₃ y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜₃ (F₂ →SL[σ₂₃] F₃)
      (fun z ↦ E₂ z →SL[σ₂₃] E₃ z) y).continuousSMul
  exact (hψ.clm_bundle_apply_semilinear hv).clm_bundle_apply_semilinear hw

end TwoVariables
