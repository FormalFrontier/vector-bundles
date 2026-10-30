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
* `LinearMap.isClosed_ker_orthogonalRetraction` shows that the retraction has
  closed kernel in the ambient inner product space.
* `LinearMap.orthogonalRetractionOfFiniteDimensional` supplies the projection
  capability from finite-dimensionality of the domain.
* `LinearMap.IsOrthogonalRetraction.ker_eq_orthogonal` identifies the kernel of
  a specified orthogonal retraction with the orthogonal complement of the range.
  `LinearMap.isOrthogonalRetraction_iff_leftInverse_and_ker_eq_orthogonal`
  characterizes orthogonal retractions by this kernel equality and a left inverse.
* `LinearMap.isCompl_range_ker_orthogonalRetraction` shows that the range and the
  constructed retraction's kernel are algebraic complements.

## Limitations

The construction has an image/preimage characterization and a left-inverse law.
The orthogonal-kernel characterization is conditional on
`LinearMap.IsOrthogonalRetraction`; no theorem here asserts that the constructed
retraction satisfies its residual-orthogonality field or that its kernel equals
the orthogonal complement of the range. No continuity in parameters or
principal-bundle construction is asserted.

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

/-- The kernel of an orthogonal retraction is the orthogonal complement of the range. -/
theorem IsOrthogonalRetraction.ker_eq_orthogonal {β : F →ₗ[K] A} {r : A →ₗ[K] F}
    (h : β.IsOrthogonalRetraction r) : r.ker = β.rangeᗮ := by
  ext a
  constructor
  · intro ha
    have hra : r a = 0 := ha
    apply (β.range.mem_orthogonal' a).2
    rintro _ ⟨v, rfl⟩
    simpa only [hra, map_zero, sub_zero] using h.residual_inner a v
  · intro ha
    have hinner : inner K (β (r a)) (β (r a)) = 0 := by
      have ha' := (β.range.mem_orthogonal' a).1 ha (β (r a)) ⟨r a, rfl⟩
      have hres := h.residual_inner a (r a)
      simpa only [inner_sub_left, ha', zero_sub, neg_eq_zero] using hres
    have hz : β (r a) = 0 := inner_self_eq_zero.mp hinner
    change r a = 0
    calc
      r a = r (β (r a)) := (h.left_inv (r a)).symm
      _ = 0 := by rw [hz, map_zero]

/-- A linear map is an orthogonal retraction exactly when it is a left inverse
and its kernel is the orthogonal complement of the range. -/
theorem isOrthogonalRetraction_iff_leftInverse_and_ker_eq_orthogonal
    (β : F →ₗ[K] A) (r : A →ₗ[K] F) :
    β.IsOrthogonalRetraction r ↔
      Function.LeftInverse r β ∧ r.ker = β.rangeᗮ := by
  constructor
  · intro h
    exact ⟨h.left_inv, h.ker_eq_orthogonal⟩
  · rintro ⟨hleft, hker⟩
    refine ⟨hleft, ?_⟩
    intro a v
    have hmem : a - β (r a) ∈ r.ker := by
      change r (a - β (r a)) = 0
      rw [map_sub, hleft (r a), sub_self]
    rw [hker] at hmem
    exact (β.range.mem_orthogonal' _).1 hmem (β v) ⟨v, rfl⟩

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

/-- The range and the kernel of the projection/preimage retraction are algebraic
complements, using only its left-inverse law. -/
theorem isCompl_range_ker_orthogonalRetraction (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) :
    IsCompl β.range (β.orthogonalRetraction hβ).ker := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro a ⟨v, rfl⟩ ha
    change β.orthogonalRetraction hβ (β v) = 0 at ha
    rw [orthogonalRetraction_apply_image] at ha
    rw [ha, map_zero]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro a
    have hres : a - β (β.orthogonalRetraction hβ a) ∈
        (β.orthogonalRetraction hβ).ker := by
      change β.orthogonalRetraction hβ (a - β (β.orthogonalRetraction hβ a)) = 0
      rw [map_sub, orthogonalRetraction_apply_image, sub_self]
    have himage : β (β.orthogonalRetraction hβ a) ∈ β.range := ⟨_, rfl⟩
    simpa only [sub_add_cancel] using
      (β.range ⊔ (β.orthogonalRetraction hβ).ker).add_mem
        (Submodule.mem_sup_right hres) (Submodule.mem_sup_left himage)

/-- The kernel of the projection/preimage retraction is closed in the ambient space. -/
theorem isClosed_ker_orthogonalRetraction (β : F →ₗ[K] A)
    [β.range.HasOrthogonalProjection] (hβ : Function.Injective β) :
    IsClosed ((β.orthogonalRetraction hβ).ker : Set A) := by
  have hker : ((β.orthogonalRetraction hβ).ker : Set A) =
      (β.range.orthogonalProjectionOnto.ker : Set A) := by
    ext a
    change β.orthogonalRetraction hβ a = 0 ↔ β.range.orthogonalProjectionOnto a = 0
    rw [orthogonalRetraction_eq_iff, map_zero]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hker]
  exact β.range.orthogonalProjectionOnto.isClosed_ker

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
