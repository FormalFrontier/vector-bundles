/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import VectorBundles.Analysis.InnerProductSpace.Orthogonal

/-!
# Orthogonal retractions onto images of plain modules

A linear embedding of a plain module into an inner product space admits a
projection/preimage construction whenever its range has an orthogonal projection.
The range carries the ambient space's inherited norm. Finite-dimensional domains
supply this capability through completeness of the range, without imposing a norm
or topology on the domain or completeness on the ambient space.

The orthogonal-retraction laws, residual-orthogonality and kernel-inclusion API,
coproduct criterion, and algebraic coordinate transport also apply in a seminormed
inner product space. Kernel equality and uniqueness require a normed ambient space.

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
* `LinearMap.IsOrthogonalRetraction.eq` gives uniqueness of orthogonal retractions
  of a fixed linear map.
* `LinearMap.isOrthogonalRetraction_coprod_iff` characterizes the coproduct and
  product of given orthogonal retractions by vanishing of both cross composites,
  including in a seminormed ambient space.
* `LinearMap.IsOrthogonalRetraction.coprod` combines given orthogonal retractions
  whose images are orthogonal, using the coproduct embedding and product retraction.
* `LinearMap.isOrthogonalRetraction_comp_linearEquiv_iff` transports the predicate
  under a linear equivalence of plain coordinate modules.
* `LinearMap.IsOrthogonalRetraction.symm_apply_eq` compares the pointwise coordinates
  of two given orthogonal retractions under that equivalence.
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

universe u v w z
universe uK uF1 uF2 uA

namespace LinearMap

variable {K : Type u} [RCLike K]
variable {F : Type v} [AddCommGroup F] [Module K F]

section SeminormedA

variable {A : Type w} [SeminormedAddCommGroup A] [InnerProductSpace K A]

/-- A left inverse whose embedded residual is orthogonal to the embedded module.
The inner product is the given one on `A`, conjugate-linear in its first argument.
With a degenerate seminorm, such a retraction need not be unique. -/
structure IsOrthogonalRetraction (β : F →ₗ[K] A) (r : A →ₗ[K] F) : Prop where
  /-- Retraction on the original module. -/
  left_inv (v : F) : r (β v) = v
  /-- Orthogonality is measured in the given ambient inner product. -/
  residual_inner (a : A) (v : F) : inner K (a - β (r a)) (β v) = 0

/-- The full residual of an orthogonal retraction is orthogonal to the embedded
range of `β` for the given ambient inner product. -/
theorem IsOrthogonalRetraction.residual_mem_orthogonalBilin
    {β : F →ₗ[K] A} {r : A →ₗ[K] F}
    (h : β.IsOrthogonalRetraction r) (a : A) :
    a - β (r a) ∈ β.range.orthogonalBilin (innerₛₗ K) := by
  apply Submodule.mem_orthogonalBilin.mpr
  rintro _ ⟨v, rfl⟩
  simpa only [innerₛₗ_apply_apply] using
    (inner_eq_zero_symm.mp (h.residual_inner a v))

/-- The kernel of an orthogonal retraction is contained in the algebraic
orthogonal complement of the embedded range of `β` for the given ambient inner
product. -/
theorem IsOrthogonalRetraction.ker_le_orthogonalBilin
    {β : F →ₗ[K] A} {r : A →ₗ[K] F}
    (h : β.IsOrthogonalRetraction r) :
    r.ker ≤ β.range.orthogonalBilin (innerₛₗ K) := by
  intro a ha
  have hra : r a = 0 := ha
  simpa only [hra, map_zero, sub_zero] using h.residual_mem_orthogonalBilin a

/-- Characterization by the left-inverse and residual-orthogonality laws. -/
theorem isOrthogonalRetraction_iff (β : F →ₗ[K] A) (r : A →ₗ[K] F) :
    β.IsOrthogonalRetraction r ↔
      (∀ v, r (β v) = v) ∧ ∀ a v, inner K (a - β (r a)) (β v) = 0 :=
  ⟨fun h => ⟨h.left_inv, h.residual_inner⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Orthogonal retractions are invariant under a change of domain coordinates.
No isometry assumption on `e` is needed: both sides use the same ambient residual
`a - β (e (rAux a))` and the inner product on `A`. -/
theorem isOrthogonalRetraction_comp_linearEquiv_iff {G : Type z} [AddCommGroup G]
    [Module K G] (β : F →ₗ[K] A) (e : G ≃ₗ[K] F) (rAux : A →ₗ[K] G) :
    (β.comp e.toLinearMap).IsOrthogonalRetraction rAux ↔
      β.IsOrthogonalRetraction (e.toLinearMap.comp rAux) := by
  constructor
  · intro h
    refine IsOrthogonalRetraction.mk ?_ ?_
    · intro v
      have hleft : rAux (β (e (e.symm v))) = e.symm v :=
        h.left_inv (e.symm v)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using congrArg e hleft
    · intro a v
      have hres :
          inner K (a - β (e (rAux a))) (β (e (e.symm v))) = 0 :=
        h.residual_inner a (e.symm v)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hres
  · intro h
    refine IsOrthogonalRetraction.mk ?_ ?_
    · intro g
      exact e.injective (h.left_inv (e g))
    · intro a g
      exact h.residual_inner a (e g)

/-- Given orthogonal retractions, the coproduct and product form an orthogonal
retraction exactly when each retraction vanishes on the other embedded module. -/
theorem isOrthogonalRetraction_coprod_iff
    {K : Type uK} [RCLike K]
    {F₁ : Type uF1} [AddCommGroup F₁] [Module K F₁]
    {F₂ : Type uF2} [AddCommGroup F₂] [Module K F₂]
    {A : Type uA} [SeminormedAddCommGroup A] [InnerProductSpace K A]
    {β₁ : F₁ →ₗ[K] A} {β₂ : F₂ →ₗ[K] A}
    {r₁ : A →ₗ[K] F₁} {r₂ : A →ₗ[K] F₂}
    (h₁ : β₁.IsOrthogonalRetraction r₁)
    (h₂ : β₂.IsOrthogonalRetraction r₂) :
    (β₁.coprod β₂).IsOrthogonalRetraction (r₁.prod r₂) ↔
      r₁.comp β₂ = 0 ∧ r₂.comp β₁ = 0 := by
  constructor
  · intro h
    constructor
    · ext v₂
      change r₁ (β₂ v₂) = 0
      have hleft := congrArg Prod.fst (h.left_inv (0, v₂))
      simpa only [LinearMap.coe_prod, Function.prod_apply, LinearMap.coprod_apply,
        map_zero, zero_add] using hleft
    · ext v₁
      change r₂ (β₁ v₁) = 0
      have hleft := congrArg Prod.snd (h.left_inv (v₁, 0))
      simpa only [LinearMap.coe_prod, Function.prod_apply, LinearMap.coprod_apply,
        map_zero, add_zero] using hleft
  · rintro ⟨hc₁, hc₂⟩
    have hcross₁ (v₂ : F₂) : r₁ (β₂ v₂) = 0 :=
      congrArg (fun f : F₂ →ₗ[K] F₁ => f v₂) hc₁
    have hcross₂ (v₁ : F₁) : r₂ (β₁ v₁) = 0 :=
      congrArg (fun f : F₁ →ₗ[K] F₂ => f v₁) hc₂
    refine IsOrthogonalRetraction.mk ?_ ?_
    · intro v
      simp only [coe_prod, Function.prod_apply, coprod_apply, map_add, h₁.left_inv,
        h₂.left_inv, hcross₁, hcross₂, Prod.mk_add_mk, add_zero, zero_add]
    · intro a v
      have hinner₁ : inner K (β₂ (r₂ a)) (β₁ v.1) = 0 := by
        apply inner_eq_zero_symm.mp
        have hmem : β₂ (r₂ a) ∈ β₁.range.orthogonalBilin (innerₛₗ K) :=
          h₁.ker_le_orthogonalBilin (hcross₁ (r₂ a))
        simpa only [innerₛₗ_apply_apply] using
          (Submodule.mem_orthogonalBilin.mp hmem) (β₁ v.1) ⟨v.1, rfl⟩
      have hinner₂ : inner K (β₁ (r₁ a)) (β₂ v.2) = 0 := by
        apply inner_eq_zero_symm.mp
        have hmem : β₁ (r₁ a) ∈ β₂.range.orthogonalBilin (innerₛₗ K) :=
          h₂.ker_le_orthogonalBilin (hcross₂ (r₁ a))
        simpa only [innerₛₗ_apply_apply] using
          (Submodule.mem_orthogonalBilin.mp hmem) (β₂ v.2) ⟨v.2, rfl⟩
      have hres₁ :
          inner K (a - (β₁ (r₁ a) + β₂ (r₂ a))) (β₁ v.1) = 0 := by
        simpa only [inner_sub_left, inner_add_left, hinner₁, add_zero] using
          h₁.residual_inner a v.1
      have hres₂ :
          inner K (a - (β₁ (r₁ a) + β₂ (r₂ a))) (β₂ v.2) = 0 := by
        simpa only [inner_sub_left, inner_add_left, hinner₂, zero_add] using
          h₂.residual_inner a v.2
      simp only [coprod_apply, coe_prod, Function.prod_apply, inner_add_right]
      rw [hres₁, hres₂, add_zero]

end SeminormedA

variable {A : Type w} [NormedAddCommGroup A] [InnerProductSpace K A]

/-- The kernel of an orthogonal retraction is the orthogonal complement of the range. -/
theorem IsOrthogonalRetraction.ker_eq_orthogonal {β : F →ₗ[K] A} {r : A →ₗ[K] F}
    (h : β.IsOrthogonalRetraction r) : r.ker = β.rangeᗮ := by
  ext a
  constructor
  · intro ha
    simpa only [Submodule.orthogonalBilin_innerₛₗ] using
      h.ker_le_orthogonalBilin ha
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

/-- Orthogonal retractions of the same linear map are equal. -/
theorem IsOrthogonalRetraction.eq {β : F →ₗ[K] A} {r s : A →ₗ[K] F}
    (hr : β.IsOrthogonalRetraction r) (hs : β.IsOrthogonalRetraction s) : r = s := by
  ext a
  have hmem : a - β (s a) ∈ r.ker := by
    rw [hr.ker_eq_orthogonal, ← hs.ker_eq_orthogonal]
    change s (a - β (s a)) = 0
    rw [map_sub, hs.left_inv, sub_self]
  change r (a - β (s a)) = 0 at hmem
  simpa only [map_sub, hr.left_inv, sub_eq_zero] using hmem

/-- Retractions along linearly equivalent coordinate modules agree after applying
the inverse coordinate change, when both orthogonality witnesses are given. -/
theorem IsOrthogonalRetraction.symm_apply_eq {G : Type z} [AddCommGroup G] [Module K G]
    {β : F →ₗ[K] A} {rCanon : A →ₗ[K] F} {rAux : A →ₗ[K] G}
    (hCanon : β.IsOrthogonalRetraction rCanon) (e : G ≃ₗ[K] F)
    (hAux : (β.comp e.toLinearMap).IsOrthogonalRetraction rAux) (a : A) :
    e.symm (rCanon a) = rAux a := by
  have hTransported := (isOrthogonalRetraction_comp_linearEquiv_iff β e rAux).mp hAux
  have hEq := hCanon.eq hTransported
  calc
    e.symm (rCanon a) = e.symm (e (rAux a)) :=
      congrArg (fun r : A →ₗ[K] F => e.symm (r a)) hEq
    _ = rAux a := e.symm_apply_apply (rAux a)

/-- Given orthogonal retractions with orthogonal images combine by coproduct and product. -/
theorem IsOrthogonalRetraction.coprod
    {K : Type uK} [RCLike K]
    {F₁ : Type uF1} [AddCommGroup F₁] [Module K F₁]
    {F₂ : Type uF2} [AddCommGroup F₂] [Module K F₂]
    {A : Type uA} [NormedAddCommGroup A] [InnerProductSpace K A]
    {β₁ : F₁ →ₗ[K] A} {β₂ : F₂ →ₗ[K] A}
    {r₁ : A →ₗ[K] F₁} {r₂ : A →ₗ[K] F₂}
    (h₁ : β₁.IsOrthogonalRetraction r₁)
    (h₂ : β₂.IsOrthogonalRetraction r₂)
    (horth : β₁.range.IsOrtho β₂.range) :
    (β₁.coprod β₂).IsOrthogonalRetraction (r₁.prod r₂) := by
  have hcross₁ (v₂ : F₂) : r₁ (β₂ v₂) = 0 := by
    have hmem : β₂ v₂ ∈ r₁.ker := by
      rw [h₁.ker_eq_orthogonal]
      exact horth.ge ⟨v₂, rfl⟩
    exact hmem
  have hcross₂ (v₁ : F₁) : r₂ (β₁ v₁) = 0 := by
    have hmem : β₁ v₁ ∈ r₂.ker := by
      rw [h₂.ker_eq_orthogonal]
      exact horth.le ⟨v₁, rfl⟩
    exact hmem
  apply (isOrthogonalRetraction_coprod_iff h₁ h₂).mpr
  constructor
  · ext v₂
    exact hcross₁ v₂
  · ext v₁
    exact hcross₂ v₁

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
