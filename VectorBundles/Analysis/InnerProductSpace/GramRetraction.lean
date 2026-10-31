/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import VectorBundles.Analysis.InnerProductSpace.AdjointPair
public import VectorBundles.Analysis.InnerProductSpace.Projection.LinearMap
import Mathlib.RingTheory.Artinian.Module

/-!
# Inverse Gram composites

For continuous linear maps `Γ : H →L[K] A` and `S : A →L[K] H`,
`ContinuousLinearMap.inverseGramComp Γ S` is the total composite
`(Ring.inverse (S.comp Γ)).comp S`. The definition does not assume that the Gram
endomorphism is a unit.

When `S.comp Γ` is a unit, the inverse Gram composite is a left inverse of `Γ`,
and its composition with `Γ` is an ambient idempotent. The recovery identity
`(S.comp Γ).comp (inverseGramComp Γ S) = S` also identifies its kernel with that
of `S`. These identities hold for modules over a semiring with arbitrary
topologies. If the ambient module has subtraction, `S` annihilates the full
ambient residual; no additive inverses on the domain are needed.

For an adjoint pair, injectivity of the Gram endomorphism is equivalent to
injectivity of `Γ`, without a completeness or dimension assumption. In finite
dimension this is also the unit criterion. The inverse Gram composite then gives
an orthogonal retraction for the given inner products.

## Implementation notes

The inner products and norms in the orthogonal specialization are the given
ones. The domain `H` may be an auxiliary space, including a subsingleton space;
it does not supply a new norm on `A`. Orthogonality requires the stated adjoint
pair, injectivity, and finite-dimensionality hypotheses, unlike the unit-only
normalization identities. The residual identity is pointwise and requires no
continuity of subtraction. These constructions make no assertion about
parameter dependence.
-/

@[expose] public section

universe uK uH uA

namespace ContinuousLinearMap

section Module

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [Semiring K]
  [AddCommMonoid H] [Module K H] [TopologicalSpace H]
  [AddCommMonoid A] [Module K A] [TopologicalSpace A]

/-- The inverse of the Gram endomorphism, followed by `S`.

This uses the total `Ring.inverse`. Without a unit hypothesis on `S.comp Γ`,
this definition is not asserted to be a retraction of `Γ`. -/
noncomputable def inverseGramComp (Γ : H →L[K] A) (S : A →L[K] H) : A →L[K] H :=
  (Ring.inverse (S.comp Γ)).comp S

/-- Evaluation of the inverse Gram composite. -/
theorem inverseGramComp_apply (Γ : H →L[K] A) (S : A →L[K] H) (a : A) :
    inverseGramComp Γ S a = Ring.inverse (S.comp Γ) (S a) := rfl

variable {Γ : H →L[K] A} {S : A →L[K] H}

/-- A unit Gram endomorphism makes the inverse Gram composite a left inverse of `Γ`. -/
theorem inverseGramComp_comp_of_isUnit (hG : IsUnit (S.comp Γ)) :
    (inverseGramComp Γ S).comp Γ = ContinuousLinearMap.id K H := by
  obtain ⟨u, hu⟩ := hG
  apply ContinuousLinearMap.ext
  intro v
  change inverseGramComp Γ S (Γ v) = v
  rw [inverseGramComp_apply]
  change Ring.inverse (S.comp Γ) ((S.comp Γ) v) = v
  rw [← hu, Ring.inverse_unit]
  exact congrArg (fun f : H →L[K] H => f v) u.inv_val

/-- With a unit Gram endomorphism, the inverse Gram composite recovers domain vectors. -/
theorem inverseGramComp_apply_image_of_isUnit (hG : IsUnit (S.comp Γ)) (v : H) :
    inverseGramComp Γ S (Γ v) = v := by
  exact congrArg (fun f : H →L[K] H => f v) (inverseGramComp_comp_of_isUnit hG)

/-- With a unit Gram endomorphism, the ambient composite fixes the image of `Γ`. -/
theorem comp_inverseGramComp_apply_image_of_isUnit (hG : IsUnit (S.comp Γ)) (v : H) :
    (Γ.comp (inverseGramComp Γ S)) (Γ v) = Γ v := by
  exact congrArg Γ (inverseGramComp_apply_image_of_isUnit hG v)

/-- With a unit Gram endomorphism, the ambient composite is idempotent. -/
theorem comp_inverseGramComp_idempotent_of_isUnit (hG : IsUnit (S.comp Γ)) :
    (Γ.comp (inverseGramComp Γ S)).comp (Γ.comp (inverseGramComp Γ S)) =
      Γ.comp (inverseGramComp Γ S) := by
  apply ContinuousLinearMap.ext
  intro a
  exact comp_inverseGramComp_apply_image_of_isUnit hG (inverseGramComp Γ S a)

/-- Applying the Gram endomorphism after its normalized composite recovers `S`. -/
theorem gram_comp_inverseGramComp_of_isUnit (hG : IsUnit (S.comp Γ)) :
    (S.comp Γ).comp (inverseGramComp Γ S) = S := by
  obtain ⟨u, hu⟩ := hG
  apply ContinuousLinearMap.ext
  intro a
  change (S.comp Γ) (inverseGramComp Γ S a) = S a
  rw [inverseGramComp_apply, ← hu, Ring.inverse_unit]
  exact congrArg (fun f : H →L[K] H => f (S a)) u.val_inv

/-- With a unit Gram endomorphism, the inverse Gram composite and `S` have the same kernel. -/
theorem inverseGramComp_eq_zero_iff_of_isUnit (hG : IsUnit (S.comp Γ)) (a : A) :
    inverseGramComp Γ S a = 0 ↔ S a = 0 := by
  constructor
  · intro ha
    calc
      S a = (S.comp Γ) (inverseGramComp Γ S a) :=
        (congrArg (fun f : A →L[K] H => f a)
          (gram_comp_inverseGramComp_of_isUnit hG)).symm
      _ = 0 := by rw [ha, map_zero]
  · intro ha
    rw [inverseGramComp_apply, ha, map_zero]

end Module

section AddCommGroup

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [Semiring K]
  [AddCommMonoid H] [Module K H] [TopologicalSpace H]
  [AddCommGroup A] [Module K A] [TopologicalSpace A]
  {Γ : H →L[K] A} {S : A →L[K] H}

/-- With a unit Gram endomorphism, `S` annihilates the full ambient residual.
Only the ambient module needs subtraction; no continuity of subtraction is assumed. -/
theorem apply_comp_inverseGramComp_residual_of_isUnit (hG : IsUnit (S.comp Γ)) (a : A) :
    S (a - (Γ.comp (inverseGramComp Γ S)) a) = 0 := by
  let P : A →L[K] A := Γ.comp (inverseGramComp Γ S)
  have hPP : P (P a) = P a :=
    congrArg (fun f : A →L[K] A => f a) (comp_inverseGramComp_idempotent_of_isUnit hG)
  have hP : P (a - P a) = 0 := by
    rw [map_sub, hPP, sub_self]
  have hSP (b : A) : S (P b) = S b :=
    congrArg (fun f : A →L[K] H => f b) (gram_comp_inverseGramComp_of_isUnit hG)
  calc
    S (a - P a) = S (P (a - P a)) := (hSP (a - P a)).symm
    _ = 0 := by rw [hP, map_zero]

end AddCommGroup

end ContinuousLinearMap

namespace Function.IsAdjointPair

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [RCLike K]
  [NormedAddCommGroup H] [InnerProductSpace K H]
  [NormedAddCommGroup A] [InnerProductSpace K A]

/-- For an adjoint pair of functions, the composite is injective exactly when the
forward map is injective. No linearity, continuity, completeness or dimension
assumption on the functions or spaces is needed beyond the given inner products. -/
theorem injective_comp_iff {Γ : H → A} {S : A → H}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    Function.Injective (S ∘ Γ) ↔ Function.Injective Γ := by
  constructor
  · intro hcomp x y hxy
    apply hcomp
    change S (Γ x) = S (Γ y)
    exact congrArg S hxy
  · intro hΓ x y hxy
    change S (Γ x) = S (Γ y) at hxy
    have hinner (v : H) : inner K (Γ v) (Γ x) = inner K (Γ v) (Γ y) := by
      calc
        inner K (Γ v) (Γ x) = inner K v (S (Γ x)) := h v (Γ x)
        _ = inner K v (S (Γ y)) := congrArg (fun w : H => inner K v w) hxy
        _ = inner K (Γ v) (Γ y) := (h v (Γ y)).symm
    have hx : inner K (Γ x) (Γ x - Γ y) = 0 := by
      rw [inner_sub_right, hinner x, sub_self]
    have hy : inner K (Γ y) (Γ x - Γ y) = 0 := by
      rw [inner_sub_right, hinner y, sub_self]
    have hself : inner K (Γ x - Γ y) (Γ x - Γ y) = 0 := by
      rw [inner_sub_left, hx, hy, sub_self]
    exact hΓ (sub_eq_zero.mp (inner_self_eq_zero.mp hself))

/-- For an adjoint pair with finite-dimensional domain, the Gram endomorphism
is a unit exactly when the forward map is injective. This includes subsingleton
domains, whose endomorphism ring is the trivial ring. -/
theorem isUnit_comp_iff [FiniteDimensional K H]
    {Γ : H →L[K] A} {S : A →L[K] H}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    IsUnit (S.comp Γ) ↔ Function.Injective Γ := by
  have hcomp : Function.Injective (S.comp Γ) ↔ Function.Injective Γ :=
    h.injective_comp_iff
  constructor
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    apply hcomp.mp
    have hinv (v : H) : u.inv ((S.comp Γ) v) = v := by
      have hv := congrArg (fun T : H →L[K] H => T v) u.inv_val
      change u.inv (u.val v) = v at hv
      rw [hu] at hv
      exact hv
    intro x y hxy
    calc
      x = u.inv ((S.comp Γ) x) := (hinv x).symm
      _ = u.inv ((S.comp Γ) y) := congrArg (fun v : H => u.inv v) hxy
      _ = y := hinv y
  · intro hΓ
    let : IsArtinianRing ((H →L[K] H)ᵐᵒᵖ) :=
      IsArtinianRing.of_finite K ((H →L[K] H)ᵐᵒᵖ)
    have hG : Function.Injective (S.comp Γ) := hcomp.mpr hΓ
    apply IsArtinianRing.isUnit_iff_isLeftRegular.mpr
    intro U V hUV
    apply ContinuousLinearMap.ext
    intro v
    apply hG
    have hUVv := congrArg (fun T : H →L[K] H => T v) hUV
    change (S.comp Γ) (U v) = (S.comp Γ) (V v) at hUVv
    exact hUVv

end Function.IsAdjointPair

namespace ContinuousLinearMap

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [RCLike K]
  [NormedAddCommGroup H] [InnerProductSpace K H]
  [NormedAddCommGroup A] [InnerProductSpace K A]

section FiniteDimensional

variable [FiniteDimensional K H] {Γ : H →L[K] A} {S : A →L[K] H}

/-- The inverse Gram composite is a left inverse of an injective member of an
adjoint pair with finite-dimensional domain. -/
theorem inverseGramComp_comp
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) :
    (inverseGramComp Γ S).comp Γ = ContinuousLinearMap.id K H := by
  exact inverseGramComp_comp_of_isUnit ((h.isUnit_comp_iff).2 hΓ)

/-- The inverse Gram composite recovers the original domain vector. -/
theorem inverseGramComp_apply_image
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) (v : H) :
    inverseGramComp Γ S (Γ v) = v := by
  exact inverseGramComp_apply_image_of_isUnit ((h.isUnit_comp_iff).2 hΓ) v

/-- The ambient composite fixes every vector in the image of `Γ`. -/
theorem comp_inverseGramComp_apply_image
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) (v : H) :
    (Γ.comp (inverseGramComp Γ S)) (Γ v) = Γ v := by
  exact comp_inverseGramComp_apply_image_of_isUnit ((h.isUnit_comp_iff).2 hΓ) v

/-- The ambient composite is idempotent. -/
theorem comp_inverseGramComp_idempotent
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) :
    (Γ.comp (inverseGramComp Γ S)).comp (Γ.comp (inverseGramComp Γ S)) =
      Γ.comp (inverseGramComp Γ S) := by
  exact comp_inverseGramComp_idempotent_of_isUnit ((h.isUnit_comp_iff).2 hΓ)

/-- The full residual of the ambient composite is annihilated by `S`. -/
theorem apply_comp_inverseGramComp_residual
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) (a : A) :
    S (a - (Γ.comp (inverseGramComp Γ S)) a) = 0 := by
  exact apply_comp_inverseGramComp_residual_of_isUnit ((h.isUnit_comp_iff).2 hΓ) a

/-- Every image vector is orthogonal to the full ambient residual. -/
theorem inner_comp_inverseGramComp_residual
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) (a : A) (v : H) :
    inner K (Γ v) (a - (Γ.comp (inverseGramComp Γ S)) a) = 0 := by
  rw [h v (a - (Γ.comp (inverseGramComp Γ S)) a),
    apply_comp_inverseGramComp_residual h hΓ a]
  simp

/-- The inverse Gram composite is an orthogonal retraction, measured using the
given ambient inner product. -/
theorem inverseGramComp_isOrthogonalRetraction
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : Function.Injective Γ) :
    LinearMap.IsOrthogonalRetraction Γ.toLinearMap
      (inverseGramComp Γ S).toLinearMap := by
  refine LinearMap.IsOrthogonalRetraction.mk ?_ ?_
  · first
    | exact congrArg (fun f : H →L[K] H => f.toLinearMap)
        (inverseGramComp_comp h hΓ)
    | exact inverseGramComp_apply_image h hΓ
  · intros
    exact inner_eq_zero_symm.mp (inner_comp_inverseGramComp_residual h hΓ _ _)

end FiniteDimensional

end ContinuousLinearMap
