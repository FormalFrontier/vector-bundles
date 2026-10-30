/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal retractions onto images of plain modules

A linear embedding of a plain module into an inner product space admits a
projection/preimage construction whenever its range has an orthogonal projection.
The range carries the ambient space's inherited norm. Finite-dimensional domains
supply this capability through completeness of the range, without imposing a norm
or topology on the domain or completeness on the ambient space.

## Main definitions and results

* `LinearMap.IsOrthogonalRetraction` records the left-inverse and
  residual-orthogonality laws for a specified linear map.
* `LinearMap.orthogonalRetraction` lifts Mathlib's projection to the original module;
  `LinearMap.image_orthogonalRetraction` identifies its image with that projection.
* `LinearMap.orthogonalRetractionOfFiniteDimensional` supplies the projection
  capability from finite-dimensionality of the domain.

## Limitations

The construction has an image/preimage characterization and a left-inverse law.
No theorem here asserts that it satisfies the residual-orthogonality field of
`LinearMap.IsOrthogonalRetraction`. No continuity in parameters is asserted.

## References

The construction uses Mathlib's submodule-valued orthogonal projection and the
inherited completeness of finite-dimensional submodules from
`Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`.
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {K : Type u} [RCLike K]
variable {F : Type v} [AddCommGroup F] [Module K F]
variable {A : Type w} [NormedAddCommGroup A] [InnerProductSpace K A]

/-- A left inverse whose embedded residual is orthogonal to the embedded module.
The inner product is the given one on `A`, conjugate-linear in its first argument. -/
structure IsOrthogonalRetraction (β : F →ₗ[K] A) (r : A →ₗ[K] F) : Prop where
  /-- Retraction on the original module. -/
  left_inv (v : F) : r (β v) = v
  /-- Orthogonality is measured in the given ambient inner product. -/
  residual_inner (a : A) (v : F) : inner K (a - β (r a)) (β v) = 0

/-- Characterization by the left-inverse and residual-orthogonality laws. -/
theorem isOrthogonalRetraction_iff (β : F →ₗ[K] A) (r : A →ₗ[K] F) :
    β.IsOrthogonalRetraction r ↔
      (∀ v, r (β v) = v) ∧ ∀ a v, inner K (a - β (r a)) (β v) = 0 :=
  ⟨fun h => ⟨h.left_inv, h.residual_inner⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Project onto the range, with its inherited ambient norm, then take its unique
preimage in the original module. The range need only admit an orthogonal projection;
no finite-dimensionality, norm, or topology on `F` is required. -/
noncomputable def orthogonalRetraction (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) : A →ₗ[K] F :=
  { toFun a := Classical.choose (β.range.orthogonalProjectionOnto a).property
    map_add' a b := hβ (by
      have hp (x : A) :
          β (Classical.choose (β.range.orthogonalProjectionOnto x).property) =
            (β.range.orthogonalProjectionOnto x : A) :=
        Classical.choose_spec (β.range.orthogonalProjectionOnto x).property
      rw [β.map_add, hp, hp, hp]
      exact congrArg Subtype.val (β.range.orthogonalProjectionOnto.map_add a b))
    map_smul' c a := hβ (by
      have hp (x : A) :
          β (Classical.choose (β.range.orthogonalProjectionOnto x).property) =
            (β.range.orthogonalProjectionOnto x : A) :=
        Classical.choose_spec (β.range.orthogonalProjectionOnto x).property
      rw [β.map_smul, hp, hp]
      exact congrArg Subtype.val (β.range.orthogonalProjectionOnto.map_smul c a)) }

/-- The embedded value is precisely Mathlib's submodule-valued projection. -/
theorem image_orthogonalRetraction (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) (a : A) :
    β (β.orthogonalRetraction hβ a) = (β.range.orthogonalProjectionOnto a : A) :=
  Classical.choose_spec (β.range.orthogonalProjectionOnto a).property

/-- Projection followed by preimage retracts the original embedding. -/
@[simp] theorem orthogonalRetraction_apply_image (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) (v : F) :
    β.orthogonalRetraction hβ (β v) = v := by
  apply hβ
  rw [image_orthogonalRetraction]
  exact congrArg Subtype.val
    (β.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨β v, ⟨v, rfl⟩⟩)

/-- The lifted value is the unique original-module preimage of the projection. -/
theorem orthogonalRetraction_eq_iff (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) (a : A) (v : F) :
    β.orthogonalRetraction hβ a = v ↔
      (β.range.orthogonalProjectionOnto a : A) = β v := by
  rw [← image_orthogonalRetraction β hβ a]
  constructor
  · exact congrArg β
  · exact fun h => hβ h

section FiniteDimensional

variable [FiniteDimensional K F]

/-- The projection/preimage retraction for a finite-dimensional domain, using the
inherited completeness of its range. No additional structure on `F` is chosen. -/
noncomputable def orthogonalRetractionOfFiniteDimensional (β : F →ₗ[K] A)
    (hβ : Function.Injective β) : A →ₗ[K] F := by
  haveI : CompleteSpace β.range := inferInstance
  exact β.orthogonalRetraction hβ

/-- The finite-dimensional construction agrees with the projection/preimage retraction. -/
@[simp] theorem orthogonalRetractionOfFiniteDimensional_eq (β : F →ₗ[K] A)
    (hβ : Function.Injective β) :
    β.orthogonalRetractionOfFiniteDimensional hβ = β.orthogonalRetraction hβ := rfl

/-- The finite-dimensional construction retracts the original embedding. -/
theorem orthogonalRetractionOfFiniteDimensional_apply_image (β : F →ₗ[K] A)
    (hβ : Function.Injective β) (v : F) :
    β.orthogonalRetractionOfFiniteDimensional hβ (β v) = v := by
  rw [orthogonalRetractionOfFiniteDimensional_eq, orthogonalRetraction_apply_image]

end FiniteDimensional

end LinearMap
