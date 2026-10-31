/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib

/-!
# Adjoint functions for arbitrary pairings

Adjointness relates two given functions and two pairings. No algebraic structure or
nondegeneracy is required. This includes bilinear, sesquilinear, and evaluation pairings.
The order of the arguments of each pairing is preserved.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace Function

variable {E : Type u₁} {H : Type u₂} {F : Type u₃} {G : Type u₄} {R : Type u₅}

/-- Two functions are adjoint for two pairings if moving the first function across
its pairing gives the second function, without reversing either pairing. -/
def IsAdjointPair (B₁ : E → H → R) (B₂ : F → G → R)
    (f : E → F) (g : G → H) : Prop :=
  ∀ x y, B₂ (f x) y = B₁ x (g y)

/-- The pointwise characterization of adjoint functions. -/
@[simp] theorem isAdjointPair_iff {B₁ : E → H → R} {B₂ : F → G → R}
    {f : E → F} {g : G → H} :
    IsAdjointPair B₁ B₂ f g ↔ ∀ x y, B₂ (f x) y = B₁ x (g y) := Iff.rfl

/-- Evaluate the defining identity of adjoint functions. -/
theorem IsAdjointPair.apply {B₁ : E → H → R} {B₂ : F → G → R}
    {f : E → F} {g : G → H} (h : IsAdjointPair B₁ B₂ f g) (x : E) (y : G) :
    B₂ (f x) y = B₁ x (g y) := h x y

/-- Identity functions are adjoint for every pairing. -/
theorem isAdjointPair_id (B : E → H → R) : IsAdjointPair B B id id :=
  fun _ _ => rfl

/-- Composition of adjoint functions reverses the order on their partners. -/
theorem IsAdjointPair.comp {J : Type u₆} {L : Type u₇}
    {B₁ : E → H → R} {B₂ : F → G → R} {B₃ : J → L → R}
    {f : E → F} {g : G → H} {f' : F → J} {g' : L → G}
    (h : IsAdjointPair B₁ B₂ f g) (h' : IsAdjointPair B₂ B₃ f' g') :
    IsAdjointPair B₁ B₃ (f' ∘ f) (g ∘ g') :=
  fun x y => (h'.apply (f x) y).trans (h.apply x (g' y))

/-- For an adjoint pair with an anisotropic biadditive pairing, the composite
identifies exactly the same pairs of points as the first function. -/
theorem IsAdjointPair.comp_apply_eq_iff_of_anisotropic
    {X : Type u₁} {Y : Type u₂} {A : Type u₃} {R : Type u₄}
    [AddGroup A] [AddCommGroup R]
    {qH : X → Y → R} {qA : A →+ A →+ R}
    {f : X → A} {g : A → Y}
    (h : IsAdjointPair qH (fun a b => qA a b) f g)
    (hA : ∀ a, qA a a = 0 → a = 0) (x y : X) :
    g (f x) = g (f y) ↔ f x = f y := by
  constructor
  · intro hxy
    have hpair (v : X) : qA (f v) (f x) = qA (f v) (f y) := by
      calc
        qA (f v) (f x) = qH v (g (f x)) := h v (f x)
        _ = qH v (g (f y)) := congrArg (qH v) hxy
        _ = qA (f v) (f y) := (h v (f y)).symm
    have hx : qA (f x) (f x - f y) = 0 := by
      rw [map_sub, hpair x, sub_self]
    have hy : qA (f y) (f x - f y) = 0 := by
      rw [map_sub, hpair y, sub_self]
    have hself : qA (f x - f y) (f x - f y) = 0 := by
      rw [map_sub qA (f x) (f y), AddMonoidHom.sub_apply, hx, hy, sub_self]
    exact sub_eq_zero.mp (hA _ hself)
  · exact congrArg g

/-- For an adjoint pair with an anisotropic biadditive pairing, the composite is
injective if and only if the first function is injective. -/
theorem IsAdjointPair.injective_comp_iff_of_anisotropic
    {X : Type u₁} {Y : Type u₂} {A : Type u₃} {R : Type u₄}
    [AddGroup A] [AddCommGroup R]
    {qH : X → Y → R} {qA : A →+ A →+ R}
    {f : X → A} {g : A → Y}
    (h : IsAdjointPair qH (fun a b => qA a b) f g)
    (hA : ∀ a, qA a a = 0 → a = 0) :
    Injective (g ∘ f) ↔ Injective f := by
  constructor
  · intro hcomp x y hxy
    exact hcomp (congrArg g hxy)
  · intro hf x y hxy
    exact hf ((h.comp_apply_eq_iff_of_anisotropic hA x y).mp hxy)

/-- Evaluation pairs every function with precomposition on function spaces. -/
theorem isAdjointPair_eval (f : E → F) :
    IsAdjointPair (fun x (φ : E → R) => φ x) (fun y (ψ : F → R) => ψ y)
      f (fun ψ => ψ ∘ f) := fun _ _ => rfl

end Function

/-- For bilinear forms, adjointness for arbitrary functions agrees with the
bilinear adjoint-pair predicate. -/
theorem LinearMap.isAdjointPair_iff_function
    {R : Type u₁} {E : Type u₂} {F : Type u₃}
    [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
    (B₁ : E →ₗ[R] E →ₗ[R] R) (B₂ : F →ₗ[R] F →ₗ[R] R)
    (f : E → F) (g : F → E) :
    LinearMap.IsAdjointPair B₁ B₂ f g ↔
      Function.IsAdjointPair (fun x y => B₁ x y) (fun x y => B₂ x y) f g := Iff.rfl
