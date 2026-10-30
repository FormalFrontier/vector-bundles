/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Projection.LinearMap

/-!
# Fibrewise orthogonal retractions into a total space

For a map `p : E → X`, suppose each fibre `{t : E // p t = x}` has a given
module structure and an injective linear map into a given inner product space
`A`. When each image admits an orthogonal projection, the projection/preimage
construction in that fibre gives a map `X × A → E`. Finite-dimensional fibres
supply this capability without any additional hypotheses.

The construction lies over `X` and retracts the map sending `t` to
`(p t, β (p t) ⟨t, rfl⟩)`. No topology on `E` or `X`, norm on the fibres, or
completeness of `A` is required. This is an algebraic construction; no continuity
or residual-orthogonality result for the family is asserted.

## References

This family construction uses the pointwise projection/preimage API in
`VectorBundles.Analysis.InnerProductSpace.Projection.LinearMap`, built on
Mathlib's submodule-valued orthogonal projection.
-/

@[expose] public section

universe u v w z

namespace Function

variable {K : Type u} [RCLike K]
variable {X : Type v} {E : Type w} {A : Type z}
variable [NormedAddCommGroup A] [InnerProductSpace K A]
variable (p : E → X)
variable [∀ x, AddCommGroup {t : E // p t = x}]
variable [∀ x, Module K {t : E // p t = x}]
variable (β : (x : X) → {t : E // p t = x} →ₗ[K] A)
variable (hβ : ∀ x, Injective (β x))

section OrthogonalProjection

variable [∀ x, (β x).range.HasOrthogonalProjection]

/-- Project in the specified fibre and return its underlying total-space value. -/
noncomputable def fiberwiseOrthogonalRetraction (q : X × A) : E :=
  ((β q.1).orthogonalRetraction (hβ q.1) q.2).val

/-- Evaluation uses the given module structure on the fibre over `x`. -/
theorem fiberwiseOrthogonalRetraction_apply (x : X) (a : A) :
    p.fiberwiseOrthogonalRetraction β hβ (x, a) =
      ((β x).orthogonalRetraction (hβ x) a).val := rfl

/-- The constructed value belongs to the fibre specified by its first argument. -/
theorem proj_fiberwiseOrthogonalRetraction (q : X × A) :
    p (p.fiberwiseOrthogonalRetraction β hβ q) = q.1 :=
  ((β q.1).orthogonalRetraction (hβ q.1) q.2).property

/-- The construction retracts the canonical fibrewise image of a total-space point. -/
@[simp] theorem fiberwiseOrthogonalRetraction_apply_image (t : E) :
    p.fiberwiseOrthogonalRetraction β hβ (p t, β (p t) ⟨t, rfl⟩) = t :=
  congrArg Subtype.val ((β (p t)).orthogonalRetraction_apply_image (hβ (p t)) ⟨t, rfl⟩)

/-- A specified map with the canonical fibrewise-image formula has this left inverse. -/
theorem fiberwiseOrthogonalRetraction_leftInverse (Φ : E → X × A)
    (hΦ : ∀ t, Φ t = (p t, β (p t) ⟨t, rfl⟩)) :
    LeftInverse (p.fiberwiseOrthogonalRetraction β hβ) Φ := by
  intro t
  rw [hΦ t]
  exact p.fiberwiseOrthogonalRetraction_apply_image β hβ t

end OrthogonalProjection

section FiniteDimensional

variable [∀ x, FiniteDimensional K {t : E // p t = x}]

/-- The total-space retraction obtained from finite-dimensionality of the given fibres. -/
noncomputable def fiberwiseOrthogonalRetractionOfFiniteDimensional (q : X × A) : E :=
  ((β q.1).orthogonalRetractionOfFiniteDimensional (hβ q.1) q.2).val

/-- The finite-dimensional family construction agrees with the projection-capability version. -/
@[simp] theorem fiberwiseOrthogonalRetractionOfFiniteDimensional_eq :
    p.fiberwiseOrthogonalRetractionOfFiniteDimensional β hβ =
      p.fiberwiseOrthogonalRetraction β hβ := rfl

/-- Evaluation of the finite-dimensional family construction in the original fibre. -/
theorem fiberwiseOrthogonalRetractionOfFiniteDimensional_apply (x : X) (a : A) :
    p.fiberwiseOrthogonalRetractionOfFiniteDimensional β hβ (x, a) =
      ((β x).orthogonalRetractionOfFiniteDimensional (hβ x) a).val := rfl

/-- The finite-dimensional family construction lies over the given base point. -/
theorem proj_fiberwiseOrthogonalRetractionOfFiniteDimensional (q : X × A) :
    p (p.fiberwiseOrthogonalRetractionOfFiniteDimensional β hβ q) = q.1 := by
  rw [fiberwiseOrthogonalRetractionOfFiniteDimensional_eq]
  exact p.proj_fiberwiseOrthogonalRetraction β hβ q

/-- The finite-dimensional family construction retracts the canonical fibrewise image. -/
theorem fiberwiseOrthogonalRetractionOfFiniteDimensional_apply_image (t : E) :
    p.fiberwiseOrthogonalRetractionOfFiniteDimensional β hβ
      (p t, β (p t) ⟨t, rfl⟩) = t := by
  rw [fiberwiseOrthogonalRetractionOfFiniteDimensional_eq]
  exact p.fiberwiseOrthogonalRetraction_apply_image β hβ t

/-- The finite-dimensional construction is a left inverse for any map with the image formula. -/
theorem fiberwiseOrthogonalRetractionOfFiniteDimensional_leftInverse (Φ : E → X × A)
    (hΦ : ∀ t, Φ t = (p t, β (p t) ⟨t, rfl⟩)) :
    LeftInverse (p.fiberwiseOrthogonalRetractionOfFiniteDimensional β hβ) Φ := by
  rw [fiberwiseOrthogonalRetractionOfFiniteDimensional_eq]
  exact p.fiberwiseOrthogonalRetraction_leftInverse β hβ Φ hΦ

end FiniteDimensional

end Function
