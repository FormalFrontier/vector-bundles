/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Units
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

For given pairings that make `Γ` and `S` an adjoint pair, the normalized range
projection preserves pairings with image vectors. Its residual pairs like zero
when the ambient module has subtraction; this need not be a zero-valued identity
for arbitrary pairings. Explicit star symmetry of the ambient pairing makes the
projection adjoint to itself, without symmetry of the domain pairing or an
involutive star operation on all values.

For the given inner products on seminormed inner-product spaces, a supplied Gram
unit gives self-adjointness and orthogonality of the residual to the image, with
the image vector in the conjugate-linear slot. These conclusions require neither
finite dimension nor completeness.

For an adjoint pair, injectivity of the Gram endomorphism is equivalent to
injectivity of `Γ`, without a completeness or dimension assumption. In finite
dimension this is also the unit criterion. As a special case, the inverse Gram
composite then gives an orthogonal retraction for the given inner products.

## Implementation notes

The inner products and norms in the inner-product specializations are the given
ones. The domain `H` may be an auxiliary space, including a zero module singleton;
it does not supply a new norm on `A`. The given-inner-product conclusions use
the adjoint-pair hypothesis. More generally, self-adjointness also uses the
explicit star symmetry of the ambient pairing; unit-only normalization does not
imply orthogonality. The residual identity is pointwise and requires no
continuity of subtraction. These identities make no assertion about parameter
dependence.

For a continuously varying injective adjoint pair, continuity of `Γ` alone
implies operator-norm continuity of the inverse Gram composite and joint
continuity of its evaluation. No completeness of `A` is required.
-/

@[expose] public section

universe uK uH uA uB uR

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

section Module

variable {K : Type uK} {H : Type uH} {A : Type uA} {R : Type uR}
  [Semiring K]
  [AddCommMonoid H] [Module K H] [TopologicalSpace H]
  [AddCommMonoid A] [Module K A] [TopologicalSpace A]
  {Γ : H →L[K] A} {S : A →L[K] H}
  {qH : H → H → R} {qA : A → A → R}

/-- The normalized range projection preserves pairings with vectors in the image
of an adjoint pair. No algebraic laws on the pairings are required. -/
theorem pairing_comp_inverseGramComp_of_isUnit (hG : IsUnit (S.comp Γ))
    (hAdj : Function.IsAdjointPair qH qA Γ S) (v : H) (a : A) :
    qA (Γ v) ((Γ.comp (inverseGramComp Γ S)) a) = qA (Γ v) a := by
  have hSP : S ((Γ.comp (inverseGramComp Γ S)) a) = S a :=
    congrArg (fun f : A →L[K] H => f a) (gram_comp_inverseGramComp_of_isUnit hG)
  calc
    qA (Γ v) ((Γ.comp (inverseGramComp Γ S)) a) =
        qH v (S ((Γ.comp (inverseGramComp Γ S)) a)) := hAdj.apply v _
    _ = qH v (S a) := congrArg (qH v) hSP
    _ = qA (Γ v) a := (hAdj.apply v a).symm

/-- Star symmetry of the ambient pairing makes the normalized range projection
adjoint to itself. The star operation need not be involutive on all values. -/
theorem isAdjointPair_comp_inverseGramComp_of_isUnit [Star R]
    (hG : IsUnit (S.comp Γ)) (hAdj : Function.IsAdjointPair qH qA Γ S)
    (hQ : ∀ a b : A, star (qA a b) = qA b a) :
    Function.IsAdjointPair qA qA
      (Γ.comp (inverseGramComp Γ S)) (Γ.comp (inverseGramComp Γ S)) := by
  intro a b
  let P : A →L[K] A := Γ.comp (inverseGramComp Γ S)
  calc
    qA (P a) b = qA (P a) (P b) :=
      (pairing_comp_inverseGramComp_of_isUnit hG hAdj (inverseGramComp Γ S a) b).symm
    _ = star (qA (P b) (P a)) := (hQ (P b) (P a)).symm
    _ = star (qA (P b) a) :=
      congrArg star
        (pairing_comp_inverseGramComp_of_isUnit hG hAdj (inverseGramComp Γ S b) a)
    _ = qA a (P b) := hQ (P b) a

end Module

section AddCommGroup

variable {K : Type uK} {H : Type uH} {A : Type uA} {R : Type uR}
  [Semiring K]
  [AddCommMonoid H] [Module K H] [TopologicalSpace H]
  [AddCommGroup A] [Module K A] [TopologicalSpace A]
  {Γ : H →L[K] A} {S : A →L[K] H}
  {qH : H → H → R} {qA : A → A → R}

/-- The residual of the normalized range projection pairs like zero with image
vectors. For arbitrary pairings this need not be a zero-valued identity. -/
theorem pairing_comp_inverseGramComp_residual_of_isUnit (hG : IsUnit (S.comp Γ))
    (hAdj : Function.IsAdjointPair qH qA Γ S) (v : H) (a : A) :
    qA (Γ v) (a - (Γ.comp (inverseGramComp Γ S)) a) = qA (Γ v) 0 := by
  calc
    qA (Γ v) (a - (Γ.comp (inverseGramComp Γ S)) a) =
        qH v (S (a - (Γ.comp (inverseGramComp Γ S)) a)) := hAdj.apply v _
    _ = qH v 0 :=
      congrArg (qH v) (apply_comp_inverseGramComp_residual_of_isUnit hG a)
    _ = qH v (S 0) := by rw [map_zero]
    _ = qA (Γ v) 0 := (hAdj.apply v 0).symm

end AddCommGroup

section InnerProductSpace

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [RCLike K]
  [SeminormedAddCommGroup H] [InnerProductSpace K H]
  [SeminormedAddCommGroup A] [InnerProductSpace K A]
  {Γ : H →L[K] A} {S : A →L[K] H}

/-- For an adjoint pair of seminormed inner-product spaces, a supplied unit Gram
endomorphism makes the normalized range projection self-adjoint for the given
inner product. -/
theorem isAdjointPair_inner_comp_inverseGramComp_of_isUnit (hG : IsUnit (S.comp Γ))
    (hAdj : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    Function.IsAdjointPair (inner K) (inner K)
      (Γ.comp (inverseGramComp Γ S)) (Γ.comp (inverseGramComp Γ S)) := by
  apply isAdjointPair_comp_inverseGramComp_of_isUnit hG hAdj
  intro a b
  simp

/-- The residual of the normalized range projection is orthogonal to the image
for the given inner products, with the image vector in the conjugate-linear slot. -/
theorem inner_comp_inverseGramComp_residual_of_isUnit (hG : IsUnit (S.comp Γ))
    (hAdj : Function.IsAdjointPair (inner K) (inner K) Γ S) (v : H) (a : A) :
    inner K (Γ v) (a - (Γ.comp (inverseGramComp Γ S)) a) = 0 := by
  simpa only [inner_zero_right] using
    (pairing_comp_inverseGramComp_residual_of_isUnit hG hAdj v a)

end InnerProductSpace

end ContinuousLinearMap

universe uPairingValue

private theorem isUnit_iff_injective_continuousLinearMap
    {K : Type uK} {H : Type uH}
    [Semiring K] [AddCommMonoid H] [Module K H]
    [TopologicalSpace H] [ContinuousAdd H]
    [IsArtinianRing ((H →L[K] H)ᵐᵒᵖ)] (U : H →L[K] H) :
    IsUnit U ↔ Function.Injective U := by
  constructor
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have hinv (v : H) : u.inv (U v) = v := by
      have hv := congrArg (fun T : H →L[K] H => T v) u.inv_val
      change u.inv (u.val v) = v at hv
      rw [hu] at hv
      exact hv
    intro x y hxy
    calc
      x = u.inv (U x) := (hinv x).symm
      _ = u.inv (U y) := congrArg (fun v : H => u.inv v) hxy
      _ = y := hinv y
  · intro hU
    apply IsArtinianRing.isUnit_iff_isLeftRegular.mpr
    intro V W hVW
    apply ContinuousLinearMap.ext
    intro v
    apply hU
    have hv := congrArg (fun T : H →L[K] H => T v) hVW
    change U (V v) = U (W v) at hv
    exact hv

namespace Function.IsAdjointPair

/-- For an adjoint pair with an anisotropic biadditive pairing, the Gram
endomorphism is a unit exactly when the forward map is injective, provided its
endomorphism semiring is right Artinian. Only the ambient module needs inverses;
no continuity of the pairings or of ambient addition is required. -/
theorem isUnit_comp_iff_of_anisotropic
    {K : Type uK} {H : Type uH} {A : Type uA} {R : Type uPairingValue}
    [Semiring K]
    [AddCommMonoid H] [Module K H] [TopologicalSpace H] [ContinuousAdd H]
    [AddCommGroup A] [Module K A] [TopologicalSpace A]
    [AddCommGroup R] [IsArtinianRing ((H →L[K] H)ᵐᵒᵖ)]
    {qH : H → H → R} {qA : A →+ A →+ R}
    {Γ : H →L[K] A} {S : A →L[K] H}
    (h : Function.IsAdjointPair qH (fun a b => qA a b) Γ S)
    (hA : ∀ a, qA a a = 0 → a = 0) :
    IsUnit (S.comp Γ) ↔ Function.Injective Γ :=
  (isUnit_iff_injective_continuousLinearMap (S.comp Γ)).trans
    (h.injective_comp_iff_of_anisotropic hA)

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
  let qA : A →+ A →+ K :=
    { toFun := fun a =>
        { toFun := fun b => inner K a b
          map_zero' := by simp only [inner_zero_right]
          map_add' := by
            intro b c
            simp only [inner_add_right] }
      map_zero' := by
        apply AddMonoidHom.ext
        intro b
        change inner K (0 : A) b = 0
        simp only [inner_zero_left]
      map_add' := by
        intro a b
        apply AddMonoidHom.ext
        intro c
        change inner K (a + b) c = inner K a c + inner K b c
        simp only [inner_add_left] }
  have h' : Function.IsAdjointPair (inner K) (fun a b => qA a b) Γ S := h
  exact h'.injective_comp_iff_of_anisotropic (fun a ha => inner_self_eq_zero.mp ha)

/-- For an adjoint pair with finite-dimensional domain, the Gram endomorphism
is a unit exactly when the forward map is injective. This includes subsingleton
domains, whose endomorphism ring is the trivial ring. -/
theorem isUnit_comp_iff [FiniteDimensional K H]
    {Γ : H →L[K] A} {S : A →L[K] H}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    IsUnit (S.comp Γ) ↔ Function.Injective Γ := by
  let : IsArtinianRing ((H →L[K] H)ᵐᵒᵖ) :=
    IsArtinianRing.of_finite K ((H →L[K] H)ᵐᵒᵖ)
  exact (isUnit_iff_injective_continuousLinearMap (S.comp Γ)).trans h.injective_comp_iff

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

namespace ContinuousLinearMap

section Continuity

variable {K : Type uK} {H : Type uH} {A : Type uA} {B : Type uB}
  [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H] [CompleteSpace H]
  [SeminormedAddCommGroup A] [NormedSpace K A] [TopologicalSpace B]

/-- The inverse Gram composite is continuous at a parameter where the Gram
endomorphism is a unit. Only the auxiliary space needs to be complete. -/
theorem continuousAt_inverseGramComp
    {Γ : B → (H →L[K] A)} {S : B → (A →L[K] H)} {b : B}
    (hΓ : ContinuousAt Γ b) (hS : ContinuousAt S b)
    (hu : IsUnit ((S b).comp (Γ b))) :
    ContinuousAt (fun b => inverseGramComp (Γ b) (S b)) b := by
  have hG : ContinuousAt (fun b => (S b).comp (Γ b)) b :=
    ((compL K H A H).continuous.continuousAt.comp hS).clm_apply hΓ
  have hi : ContinuousAt Ring.inverse ((S b).comp (Γ b)) := by
    obtain ⟨u, hu⟩ := hu
    simpa only [hu] using NormedRing.inverse_continuousAt u
  have hInv : ContinuousAt (fun b => Ring.inverse ((S b).comp (Γ b))) b :=
    hi.comp (f := fun b => (S b).comp (Γ b)) hG
  simpa only [inverseGramComp, Function.comp_apply, compL_apply] using
    ((compL K A H H).continuous.continuousAt.comp hInv).clm_apply hS

end Continuity

section Families

variable {K : Type uK} {H : Type uH} {A : Type uA} {B : Type uB}
  [RCLike K]
  [NormedAddCommGroup H] [InnerProductSpace K H]
  [NormedAddCommGroup A] [InnerProductSpace K A]
  [TopologicalSpace B] [FiniteDimensional K H]

/-- For an injective family of adjoint pairs, continuity of the original maps
implies operator-norm continuity of their inverse Gram composites. -/
theorem continuous_inverseGramComp
    {Γ : B → (H →L[K] A)} {S : B → (A →L[K] H)}
    (h : ∀ b, Function.IsAdjointPair (inner K) (inner K) (Γ b) (S b))
    (hΓ_injective : ∀ b, Function.Injective (Γ b)) (hΓ : Continuous Γ) :
    Continuous (fun b => inverseGramComp (Γ b) (S b)) := by
  let : CompleteSpace H := FiniteDimensional.complete K H
  have hS : Continuous S := (Function.IsAdjointPair.continuous_iff h).mp hΓ
  exact continuous_iff_continuousAt.mpr fun b =>
    continuousAt_inverseGramComp hΓ.continuousAt hS.continuousAt
      ((h b).isUnit_comp_iff.mpr (hΓ_injective b))

/-- Evaluation of an inverse Gram family is jointly continuous in the parameter
and ambient vector, assuming continuity only of the original map family. -/
theorem continuous_inverseGramComp_apply
    {Γ : B → (H →L[K] A)} {S : B → (A →L[K] H)}
    (h : ∀ b, Function.IsAdjointPair (inner K) (inner K) (Γ b) (S b))
    (hΓ_injective : ∀ b, Function.Injective (Γ b)) (hΓ : Continuous Γ) :
    Continuous (fun x : B × A => inverseGramComp (Γ x.1) (S x.1) x.2) := by
  exact ((continuous_inverseGramComp h hΓ_injective hΓ).comp continuous_fst).clm_apply
    continuous_snd

end Families

end ContinuousLinearMap
