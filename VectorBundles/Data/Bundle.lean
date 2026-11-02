/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Bundle
public import Mathlib.Logic.Equiv.Set

/-!
# Dependent total spaces and projection fibres

A base map `f : B → C` and fiber maps `φ : ∀ b, E b → V (f b)` induce a map from
`Bundle.TotalSpace F E` to `Bundle.TotalSpace G V`. The source and target model parameters
`F` and `G` are independent phantom types: no elements or structures on them are required.
The base, fiber and model types all have independent universes.

The constructor, projection and dependent fiber equations describe this map without transport.
Identity and composition hold on the original total spaces. For identity fiber maps on a
pullback family and the same model on both sides, the map is `Bundle.Pullback.lift`.

`Bundle.TotalSpace.fiberEquiv` identifies each original fibre with the equality subtype of
the total space over its base point. The canonical additive monoids and modules on these
subtypes are reducible non-instances, transported only from the given original fibres.
The pointwise constructions `fiberAddCommMonoidAt`, `fiberModuleAt` and
`fiberLinearEquivAt` require algebraic structures only on `E b`: addition is independent
of the scalar type, and the scalar type needs only to be a semiring. The corresponding
family constructions are applications of these pointwise constructions.
Install their families with `letI := Bundle.TotalSpace.fiberAddCommMonoid (E := E) P` and
`letI := Bundle.TotalSpace.fiberModule R (E := E) P`. The resulting `fiberLinearEquiv`
preserves the original total-space values. No topology or structure on the total space
itself is introduced or changed.

## References

Mathlib's `Mathlib.Data.Bundle`, by Nicolò Cavalleri, supplies the total-space structure,
constructor, extensionality, eta and pullback lift. The elementary map and its characteristic
API are by Formal Frontier Agents.
-/

@[expose] public section

universe uB uC uE uV uF uG uD uW uJ uR uM

namespace Bundle.TotalSpace

variable {B : Type uB} {C : Type uC} {E : B → Type uE} {V : C → Type uV}

/-- Map dependent total spaces by a base map and a family of fiber maps.
The source model `F` and target model `G` are independent phantom parameters. -/
def map (F : Type uF) (G : Type uG) (f : B → C) (φ : ∀ b, E b → V (f b)) :
    TotalSpace F E → TotalSpace G V :=
  fun p ↦ mk' G (f p.proj) (φ p.proj p.snd)

section Coordinates

variable (F : Type uF) (G : Type uG) (f : B → C) (φ : ∀ b, E b → V (f b))

/-- The total-space map sends each constructor to the corresponding mapped constructor. -/
theorem map_mk (b : B) (x : E b) :
    map F G f φ (mk' F b x) = mk' G (f b) (φ b x) := rfl

/-- The projection of the image is the image of the projection under the base map. -/
theorem map_proj (p : TotalSpace F E) :
    (map F G f φ p).proj = f p.proj := rfl

/-- The fiber coordinate of the image is given by the fiber map, with no index transport. -/
theorem map_snd (p : TotalSpace F E) :
    (map F G f φ p).snd = φ p.proj p.snd := rfl

end Coordinates

/-- Identity base and fiber maps give the identity on the same total space and model. -/
theorem map_id (F : Type uF) :
    map (E := E) (V := E) F F id (fun _ ↦ id) = id := rfl

/-- Total-space maps compose by composing the base maps and the corresponding fiber maps.
The intermediate total space has the same family and model in both factors. -/
theorem map_comp {D : Type uD} {W : D → Type uW}
    (F : Type uF) (G : Type uG) (J : Type uJ)
    (f : B → C) (φ : ∀ b, E b → V (f b))
    (g : C → D) (ψ : ∀ c, V c → W (g c)) :
    map G J g ψ ∘ map F G f φ =
      map F J (g ∘ f) (fun b ↦ ψ (f b) ∘ φ b) := rfl

/-- On a pullback family, identity fiber maps with a common model give the pullback lift. -/
theorem map_pullback_eq_lift (G : Type uG) (f : B → C) :
    map (E := Bundle.Pullback f V) (V := V) G G f (fun _ ↦ id) =
      Bundle.Pullback.lift (F := G) (E := V) f := rfl

noncomputable section

/-- The original fibre is equivalent to the projection's equality fibre in the same total space.
The model parameter is an arbitrary phantom type, with no additional structure. -/
def fiberEquiv (P : Type uF) (b : B) :
    E b ≃ {p : TotalSpace P E // p.proj = b} :=
  (Equiv.ofInjective (mk b : E b → TotalSpace P E) (mk_injective b)).trans
    (Set.equivOfEq (range_mk (F := P) (E := E) b))

/-- Packing an original fibre vector leaves its total-space value and projection unchanged. -/
@[simp]
theorem fiberEquiv_apply (P : Type uF) (b : B) (v : E b) :
    fiberEquiv P b v = ⟨mk b v, rfl⟩ := rfl

/-- Unpacking transports the original dependent component in the direction of the fibre equation. -/
theorem fiberEquiv_symm_apply (P : Type uF) (b : B)
    (p : {p : TotalSpace P E // p.proj = b}) :
    (fiberEquiv P b).symm p = cast (congrArg E p.property) p.val.snd := by
  rcases p with ⟨⟨c, v⟩, h⟩
  cases h
  exact (fiberEquiv P c).symm_apply_apply v

/-- Unpacking a total-space point at its own projection recovers its dependent component. -/
@[simp]
theorem fiberEquiv_symm_apply_self (P : Type uF) (p : TotalSpace P E) :
    (fiberEquiv P p.proj).symm ⟨p, rfl⟩ = p.snd := by
  rcases p with ⟨b, v⟩
  exact (fiberEquiv P b).symm_apply_apply v

/-- Unpacking and rebuilding a fibre point preserves its original total-space value. -/
@[simp]
theorem mk_fiberEquiv_symm (P : Type uF) (b : B)
    (p : {p : TotalSpace P E // p.proj = b}) :
    (mk b ((fiberEquiv P b).symm p) : TotalSpace P E) = p.val :=
  congrArg Subtype.val ((fiberEquiv P b).apply_symm_apply p)

section PointwiseAlgebra

/-- The additive monoid on a projection fibre transported from its original fibre.
No algebraic structure on any other fibre or scalar type is required. -/
abbrev fiberAddCommMonoidAt (P : Type uF) (b : B) [AddCommMonoid (E b)] :
    AddCommMonoid {p : TotalSpace P E // p.proj = b} :=
  (fiberEquiv P b).symm.addCommMonoid

attribute [local instance] fiberAddCommMonoidAt

/-- Zero in a projection fibre is the packed original zero, using only that fibre's monoid. -/
theorem fiberAt_zero_def (P : Type uF) (b : B) [AddCommMonoid (E b)] :
    (0 : {p : TotalSpace P E // p.proj = b}) = fiberEquiv P b 0 := rfl

/-- Addition in a projection fibre packs the sum in the original fibre. -/
theorem fiberAt_add_def (P : Type uF) (b : B) [AddCommMonoid (E b)]
    (p q : {p : TotalSpace P E // p.proj = b}) :
    p + q = fiberEquiv P b ((fiberEquiv P b).symm p + (fiberEquiv P b).symm q) := rfl

/-- The module on a projection fibre transported from its original module over a semiring.
Its addition is `fiberAddCommMonoidAt`, independent of the scalar type. -/
abbrev fiberModuleAt (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)] :
    Module R {p : TotalSpace P E // p.proj = b} :=
  (fiberEquiv P b).symm.addEquiv.module R

attribute [local instance] fiberModuleAt

/-- Scalar multiplication in a projection fibre packs the original scalar multiplication. -/
theorem fiberAt_smul_def (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)] (r : R)
    (p : {p : TotalSpace P E // p.proj = b}) :
    r • p = fiberEquiv P b (r • (fiberEquiv P b).symm p) := rfl

/-- The canonical linear identification of one original fibre with its projection equality
subtype. Only that fibre's module over a semiring is required, with no topology assumptions. -/
def fiberLinearEquivAt (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)] :
    E b ≃ₗ[R] {p : TotalSpace P E // p.proj = b} :=
  ((fiberEquiv (E := E) P b).symm.addEquiv.linearEquiv R).symm

/-- Forgetting pointwise linearity recovers the canonical equivalence of the original carriers. -/
@[simp]
theorem fiberLinearEquivAt_toEquiv (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)] :
    (fiberLinearEquivAt (E := E) R P b).toEquiv = fiberEquiv (E := E) P b := rfl

/-- The pointwise linear identification packs the original vector in the same total space. -/
@[simp]
theorem fiberLinearEquivAt_apply (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)] (v : E b) :
    fiberLinearEquivAt R P b v = ⟨mk b v, rfl⟩ := rfl

/-- The inverse pointwise linear identification is the original unpacking map. -/
@[simp]
theorem fiberLinearEquivAt_symm_apply (R : Type uR) [Semiring R] (P : Type uF) (b : B)
    [AddCommMonoid (E b)] [Module R (E b)]
    (p : {p : TotalSpace P E // p.proj = b}) :
    (fiberLinearEquivAt R P b).symm p = (fiberEquiv P b).symm p := rfl

end PointwiseAlgebra

section Algebra

variable [∀ b, AddCommMonoid (E b)]

/-- The additive monoids on projection fibres transported from the given original fibres.
This family is not a global instance and changes no original fibre operation. -/
abbrev fiberAddCommMonoid (P : Type uF) :
    ∀ b : B, AddCommMonoid {p : TotalSpace P E // p.proj = b} :=
  fun b => fiberAddCommMonoidAt (E := E) P b

attribute [local instance] fiberAddCommMonoid

/-- Zero in a projection fibre is the packed original zero. -/
theorem fiber_zero_def (P : Type uF) (b : B) :
    (0 : {p : TotalSpace P E // p.proj = b}) = fiberEquiv P b 0 :=
  fiberAt_zero_def (E := E) P b

/-- Addition in a projection fibre packs the sum of the original unpacked vectors. -/
theorem fiber_add_def (P : Type uF) (b : B)
    (p q : {p : TotalSpace P E // p.proj = b}) :
    p + q = fiberEquiv P b ((fiberEquiv P b).symm p + (fiberEquiv P b).symm q) :=
  fiberAt_add_def P b p q

variable (R : Type uR) [Semiring R] [∀ b, Module R (E b)]

/-- The modules on projection fibres transported from the given original fibre modules.
Use this family together with `fiberAddCommMonoid`; neither is a global instance. -/
abbrev fiberModule (P : Type uF) :
    ∀ b : B, Module R {p : TotalSpace P E // p.proj = b} :=
  fun b => fiberModuleAt (E := E) R P b

attribute [local instance] fiberModule

/-- Scalar multiplication in a projection fibre packs the original scalar multiplication. -/
theorem fiber_smul_def (P : Type uF) (b : B) (r : R)
    (p : {p : TotalSpace P E // p.proj = b}) :
    r • p = fiberEquiv P b (r • (fiberEquiv P b).symm p) :=
  fiberAt_smul_def R P b r p

/-- The canonical linear identification of an original fibre with its projection equality subtype.
Its target uses `fiberAddCommMonoid` and `fiberModule`, without any topology assumptions. -/
def fiberLinearEquiv (P : Type uF) (b : B) :
    E b ≃ₗ[R] {p : TotalSpace P E // p.proj = b} :=
  fiberLinearEquivAt (E := E) R P b

/-- Forgetting linearity recovers the canonical equivalence of the original carriers. -/
@[simp]
theorem fiberLinearEquiv_toEquiv (P : Type uF) (b : B) :
    (fiberLinearEquiv (E := E) R P b).toEquiv = fiberEquiv (E := E) P b := rfl

/-- The linear identification packs the original vector without changing its total-space value. -/
@[simp]
theorem fiberLinearEquiv_apply (P : Type uF) (b : B) (v : E b) :
    fiberLinearEquiv R P b v = ⟨mk b v, rfl⟩ := rfl

/-- The inverse linear identification is the original unpacking map. -/
@[simp]
theorem fiberLinearEquiv_symm_apply (P : Type uF) (b : B)
    (p : {p : TotalSpace P E // p.proj = b}) :
    (fiberLinearEquiv R P b).symm p = (fiberEquiv P b).symm p := rfl

/-- Lifting a fibre reconstruction into the equality fibre preserves its total-space realization. -/
theorem fiberLinearEquiv_comp_apply_val {M : Type uM} [AddCommMonoid M] [Module R M]
    (P : Type uF) (b : B) (ρ : M →ₗ[R] E b) (v : M) :
    (((fiberLinearEquiv R P b).toLinearMap.comp ρ) v).val = mk b (ρ v) := rfl

/-- Moving original fibre coordinate maps to equality fibres preserves evaluation on total
points. -/
theorem comp_fiberLinearEquiv_symm_apply_self {M : Type uM}
    [AddCommMonoid M] [Module R M] (P : Type uF) (β : ∀ b, E b →ₗ[R] M)
    (p : TotalSpace P E) :
    ((β p.proj).comp (fiberLinearEquiv R P p.proj).symm.toLinearMap) ⟨p, rfl⟩ =
      β p.proj p.snd := by
  simp

end Algebra

end

end Bundle.TotalSpace
