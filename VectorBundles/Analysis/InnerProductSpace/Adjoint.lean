/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import VectorBundles.Analysis.InnerProductSpace.AdjointPair

/-!
# Adjoints with complete domain

The adjoint of a continuous linear map from a Hilbert space is defined by
precomposition on continuous duals and the Fréchet–Riesz equivalence.
The target need not be complete or separated.

The composition laws generalize Mathlib's `ContinuousLinearMap.adjoint_comp`.
For normed complete source and target, `ContinuousLinearMap.adjointMap_eq_adjoint`
identifies this construction with Mathlib's adjoint.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace ContinuousLinearMap

variable {K : Type u} {H : Type v} {A : Type w}
  [RCLike K] [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
  [SeminormedAddCommGroup A] [InnerProductSpace K A]

/-- Taking adjoints as a continuous conjugate-linear map for operators with
complete domain. The target need not be complete or separated. -/
def adjointMap : (H →L[K] A) →L⋆[K] (A →L[K] H) :=
  let R := (InnerProductSpace.toDual K H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let I := (InnerProductSpace.toDualMap K A).toContinuousLinearMap
  let p : (H →L[K] A) →L[K] (A →L⋆[K] StrongDual K H) :=
    ((compSL A (StrongDual K A) (StrongDual K H)
      (starRingEnd K) (RingHom.id K)).flip I).comp (compL K H A K).flip
  let q : (A →L⋆[K] StrongDual K H) →L⋆[K] (A →L[K] H) :=
    compSL A (StrongDual K H) H (starRingEnd K) (starRingEnd K) R
  q.comp p

/-- The adjoint evaluated at a vector is the Riesz representative of the
functional obtained by precomposition. -/
theorem adjointMap_apply (Γ : H →L[K] A) (a : A) :
    adjointMap Γ a = (InnerProductSpace.toDual K H).symm
      ((InnerProductSpace.toDualMap K A a).comp Γ) := rfl

/-- The defining inner-product identity with the adjoint in the first argument. -/
@[simp]
theorem adjointMap_inner_left (Γ : H →L[K] A) (a : A) (h : H) :
    inner K (adjointMap Γ a) h = inner K a (Γ h) := by
  simp only [adjointMap_apply, InnerProductSpace.toDual_symm_apply,
    comp_apply, InnerProductSpace.toDualMap_apply_apply]

/-- The defining inner-product identity with the adjoint in the second argument. -/
@[simp]
theorem adjointMap_inner_right (Γ : H →L[K] A) (h : H) (a : A) :
    inner K h (adjointMap Γ a) = inner K (Γ h) a := by
  calc
    inner K h (adjointMap Γ a) = star (inner K (adjointMap Γ a) h) :=
      (inner_conj_symm _ _).symm
    _ = star (inner K a (Γ h)) := congrArg star (adjointMap_inner_left Γ a h)
    _ = inner K (Γ h) a := inner_conj_symm _ _

/-- An operator and its adjoint form an adjoint pair for the given inner products. -/
theorem isAdjointPair_adjointMap (Γ : H →L[K] A) :
    Function.IsAdjointPair (inner K) (inner K) Γ (adjointMap Γ) := by
  intro h a
  exact (adjointMap_inner_right Γ h a).symm

/-- The inner-product identity characterizes the adjoint among all functions. -/
theorem isAdjointPair_iff_eq_adjointMap (Γ : H →L[K] A) (S : A → H) :
    Function.IsAdjointPair (inner K) (inner K) Γ S ↔ S = ⇑(adjointMap Γ) := by
  constructor
  · intro hS
    funext a
    apply ext_inner_left (𝕜 := K)
    intro h
    exact (hS h a).symm.trans (adjointMap_inner_right Γ h a).symm
  · rintro rfl
    exact isAdjointPair_adjointMap Γ

/-- The adjoint of the identity on a complete inner product space is the identity. -/
@[simp]
theorem adjointMap_id : adjointMap (ContinuousLinearMap.id K H) = ContinuousLinearMap.id K H := by
  ext h
  exact (congrFun ((isAdjointPair_iff_eq_adjointMap
    (ContinuousLinearMap.id K H) id).mp (Function.isAdjointPair_id (inner K))) h).symm

section Composition

variable {M : Type x} [SeminormedAddCommGroup M] [InnerProductSpace K M]

/-- A supplied raw adjoint partner composes with the adjoint on its left.
No linearity or continuity of the partner, or completeness of the intermediate
or target space, is assumed. -/
theorem adjointMap_comp_apply_of_isAdjointPair (Γ₂ : M →L[K] A) (Γ₁ : H →L[K] M)
    {S₂ : A → M} (h₂ : Function.IsAdjointPair (inner K) (inner K) Γ₂ S₂) (a : A) :
    adjointMap (Γ₂.comp Γ₁) a = adjointMap Γ₁ (S₂ a) := by
  exact (congrFun ((isAdjointPair_iff_eq_adjointMap
    (Γ₂.comp Γ₁) (adjointMap Γ₁ ∘ S₂)).mp
      ((isAdjointPair_adjointMap Γ₁).comp h₂)) a).symm

/-- For a bundled adjoint partner, composition is an equality of continuous
linear maps. Neither the intermediate nor the target space need be complete. -/
theorem adjointMap_comp_of_isAdjointPair (Γ₂ : M →L[K] A) (Γ₁ : H →L[K] M)
    (S₂ : A →L[K] M) (h₂ : Function.IsAdjointPair (inner K) (inner K) Γ₂ S₂) :
    adjointMap (Γ₂.comp Γ₁) = (adjointMap Γ₁).comp S₂ := by
  ext a
  exact adjointMap_comp_apply_of_isAdjointPair Γ₂ Γ₁ h₂ a

end Composition

section CompleteIntermediate

variable {M : Type x} [NormedAddCommGroup M] [InnerProductSpace K M] [CompleteSpace M]

/-- Adjoint formation reverses composition when the intermediate space is
normed and complete. The target may still be seminormed and incomplete. -/
theorem adjointMap_comp (Γ₂ : M →L[K] A) (Γ₁ : H →L[K] M) :
    adjointMap (Γ₂.comp Γ₁) = (adjointMap Γ₁).comp (adjointMap Γ₂) :=
  adjointMap_comp_of_isAdjointPair Γ₂ Γ₁ (adjointMap Γ₂) (isAdjointPair_adjointMap Γ₂)

end CompleteIntermediate

/-- An operator and its adjoint have the same operator norm. -/
@[simp]
theorem norm_adjointMap (Γ : H →L[K] A) : ‖adjointMap Γ‖ = ‖Γ‖ :=
  (isAdjointPair_adjointMap Γ).norm_eq.symm

/-- The operator norm of taking adjoints is at most one, including when the
operator spaces are trivial. -/
theorem norm_adjointMap_le_one :
    ‖(adjointMap : (H →L[K] A) →L⋆[K] (A →L[K] H))‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro Γ
  simpa only [one_mul] using (norm_adjointMap Γ).le

/-- Taking adjoints preserves the norm of a difference of operators. -/
@[simp]
theorem norm_adjointMap_sub (Γ Δ : H →L[K] A) :
    ‖adjointMap Γ - adjointMap Δ‖ = ‖Γ - Δ‖ :=
  ((isAdjointPair_adjointMap Γ).norm_sub_eq (isAdjointPair_adjointMap Δ)).symm

/-- Taking adjoints preserves the distance between operators. -/
@[simp]
theorem dist_adjointMap (Γ Δ : H →L[K] A) :
    dist (adjointMap Γ) (adjointMap Δ) = dist Γ Δ :=
  ((isAdjointPair_adjointMap Γ).dist_eq (isAdjointPair_adjointMap Δ)).symm

section CompleteTarget

variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]

/-- The Hilbert-space adjoint forms an adjoint pair for the given inner products. -/
theorem isAdjointPair_adjoint (Γ : H →L[K] F) :
    Function.IsAdjointPair (inner K) (inner K) Γ (adjoint Γ) := by
  intro h a
  exact (adjoint_inner_right Γ h a).symm

/-- For complete normed targets, the complete-domain adjoint agrees with the
Hilbert-space adjoint. -/
theorem adjointMap_eq_adjoint (Γ : H →L[K] F) : adjointMap Γ = adjoint Γ := by
  ext a
  exact (congrFun ((isAdjointPair_iff_eq_adjointMap Γ (adjoint Γ)).mp
    (isAdjointPair_adjoint Γ)) a).symm

end CompleteTarget

end ContinuousLinearMap
