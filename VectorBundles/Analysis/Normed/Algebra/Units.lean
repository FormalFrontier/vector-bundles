module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Inseparable
public import CoherentModules.RingTheory.Artinian.Regular

/-!
# Near-one units without completeness

In a normed ring, an element at distance less than one from the identity acts
injectively by left multiplication. Algebraicity of that element over a field,
finite dimensionality over a field, or left Artinianity makes it a unit. For
algebraic algebras, finite-dimensional algebras and left-Artinian rings the unit
locus is open.

For a seminormed algebra, the preimage of units in its canonical separation
quotient is open whenever that quotient is algebraic. This need not be the unit
locus of the original ring.

No norm or topology on the scalar field is needed for the algebraic or
finite-dimensional results. Neither completeness nor commutativity of the ring is assumed. The
separation in `NormedRing` is used in the injectivity argument; the zero ring
is allowed throughout.

## References

* Mathlib's `Algebra.lmul_isUnit_iff` and
  `LinearMap.isUnit_iff_ker_eq_bot` supply the finite-dimensional unit criterion.
* Mathlib's `isAlgebraic_iff_isIntegral` and
  `Algebra.finite_adjoin_simple_of_isIntegral` reduce algebraicity to the
  finite-dimensional criterion in the generated subalgebra.
* Coherent Modules' `IsLeftRegular.isUnit_of_isArtinianRing` supplies the
  left-Artinian unit criterion.
-/

@[expose] public section

universe uK uR

namespace NormedRing

/-- Left multiplication by an element less than unit distance from the identity
is injective. Separation of the norm, but no finiteness or completeness, is
needed. -/
theorem isLeftRegular_of_norm_one_sub_lt_one
    {R : Type uR} [NormedRing R] {a : R} (ha : ‖1 - a‖ < 1) :
    IsLeftRegular a := by
  intro x y hxy
  change a * x = a * y at hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hne
  have heq : (1 - a) * (x - y) = x - y := by
    rw [sub_mul, one_mul, mul_sub, hxy, sub_self, sub_zero]
  have hle : ‖x - y‖ ≤ ‖1 - a‖ * ‖x - y‖ := by
    calc
      ‖x - y‖ = ‖(1 - a) * (x - y)‖ := congrArg norm heq.symm
      _ ≤ ‖1 - a‖ * ‖x - y‖ := norm_mul_le _ _
  have hlt : ‖1 - a‖ * ‖x - y‖ < ‖x - y‖ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right ha hpos
  exact (not_lt_of_ge hle) hlt

end NormedRing

-- Translate a neighborhood of the identity by a unit. Using continuity rather
-- than dividing by the norm of its inverse also covers the zero ring.
private theorem isOpen_setOf_isUnit_of_near_one
    {R : Type uR} [NormedRing R]
    (h : ∀ a : R, ‖1 - a‖ < 1 → IsUnit a) :
    IsOpen {a : R | IsUnit a} := by
  refine isOpen_iff_mem_nhds.mpr ?_
  intro a ha
  obtain ⟨u, rfl⟩ := ha
  have hopen : IsOpen {b : R | ‖1 - (↑(u⁻¹) : R) * b‖ < 1} :=
    isOpen_lt (continuous_norm.comp
      (continuous_const.sub (continuous_const.mul continuous_id))) continuous_const
  have hmem : (↑u : R) ∈ {b : R | ‖1 - (↑(u⁻¹) : R) * b‖ < 1} := by
    simp
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  intro b hb
  simpa [← mul_assoc] using u.isUnit.mul (h _ hb)

namespace FiniteDimensional

/-- In a finite-dimensional algebra over a field, an element less than unit
distance from the identity is a unit. Mathlib's kernel criterion for
endomorphisms and `Algebra.lmul_isUnit_iff` turn norm injectivity into a unit;
no scalar norm or completeness is required. -/
theorem isUnit_of_norm_one_sub_lt_one
    (K : Type uK) {R : Type uR} [Field K] [NormedRing R]
    [Algebra K R] [FiniteDimensional K R] {a : R}
    (ha : ‖1 - a‖ < 1) : IsUnit a := by
  have hinj : Function.Injective (Algebra.lmul K R a) :=
    NormedRing.isLeftRegular_of_norm_one_sub_lt_one ha
  have hu : IsUnit (Algebra.lmul K R a) :=
    (LinearMap.isUnit_iff_ker_eq_bot (Algebra.lmul K R a)).mpr
      (LinearMap.ker_eq_bot.mpr hinj)
  exact (show IsUnit (Algebra.lmul K R a) ↔ IsUnit a from
    Algebra.lmul_isUnit_iff).mp hu

/-- The units of a finite-dimensional algebra over an arbitrary field form an
open subset for any given ring norm. No compatibility between the scalar
field and the norm is required. -/
theorem isOpen_setOf_isUnit
    (K : Type uK) {R : Type uR} [Field K] [NormedRing R]
    [Algebra K R] [FiniteDimensional K R] :
    IsOpen {a : R | IsUnit a} :=
  isOpen_setOf_isUnit_of_near_one (fun a ha =>
    isUnit_of_norm_one_sub_lt_one K (a := a) ha)

end FiniteDimensional

namespace IsAlgebraic

/-- An algebraic element of a normed algebra over a field is a unit if it is less
than unit distance from the identity. The proof uses the inherited norm on the
finite-dimensional subalgebra generated by the element, with no scalar norm or
completeness assumption. -/
theorem isUnit_of_norm_one_sub_lt_one
    {K : Type uK} {R : Type uR} [Field K] [NormedRing R]
    [Algebra K R] {a : R} (hAlg : IsAlgebraic K a)
    (ha : ‖1 - a‖ < 1) : IsUnit a := by
  let S : Subalgebra K R := Algebra.adjoin K {a}
  have : FiniteDimensional K S :=
    Algebra.finite_adjoin_simple_of_isIntegral
      (isAlgebraic_iff_isIntegral.mp hAlg)
  let aS : S := ⟨a, Algebra.subset_adjoin (by simp)⟩
  have hu : IsUnit aS :=
    FiniteDimensional.isUnit_of_norm_one_sub_lt_one K (a := aS) ha
  exact hu.map S.val

end IsAlgebraic

namespace Algebra.IsAlgebraic

/-- The units of an algebraic algebra over an arbitrary field form an open
subset for any given ring norm. No completeness or compatibility with a scalar
norm is required, and the ring may be noncommutative or trivial. -/
theorem isOpen_setOf_isUnit
    (K : Type uK) {R : Type uR} [Field K] [NormedRing R]
    [Algebra K R] [Algebra.IsAlgebraic K R] :
    IsOpen {a : R | IsUnit a} :=
  isOpen_setOf_isUnit_of_near_one (fun a ha =>
    IsAlgebraic.isUnit_of_norm_one_sub_lt_one (K := K)
      (Algebra.IsAlgebraic.isAlgebraic a) ha)

end Algebra.IsAlgebraic

namespace SeparationQuotient

/-- For a seminormed algebra whose canonical separation quotient is algebraic,
the preimage of the quotient unit locus is open. This does not assert that the
units of the original seminormed ring form an open set. -/
theorem isOpen_setOf_isUnit_mk
    (K : Type uK) {R : Type uR} [Field K] [SeminormedRing R]
    [Algebra K R] [Algebra.IsAlgebraic K (SeparationQuotient R)] :
    IsOpen {a : R | IsUnit (mk a)} :=
  (Algebra.IsAlgebraic.isOpen_setOf_isUnit K
    (R := SeparationQuotient R)).preimage continuous_mk

/-- For an algebraic seminormed algebra over an arbitrary field, the elements
whose images in its canonical separation quotient are units form an open set.
The original seminorm, topology and scalar action are unchanged; no separation
or completeness of the original ring is assumed. -/
theorem isOpen_setOf_isUnit_mk_of_isAlgebraic
    (K : Type uK) {R : Type uR} [Field K] [SeminormedRing R]
    [Algebra K R] [Algebra.IsAlgebraic K R] :
    IsOpen {a : R | IsUnit (mk a)} := by
  let q : R →ₐ[K] SeparationQuotient R :=
    { (mkRingHom : R →+* SeparationQuotient R) with
      commutes' := fun k => mk_algebraMap k }
  have : Algebra.IsAlgebraic K (SeparationQuotient R) := by
    constructor
    intro a
    obtain ⟨r, rfl⟩ := surjective_mk a
    have hr : IsAlgebraic K r := Algebra.IsAlgebraic.isAlgebraic r
    exact hr.algHom q
  exact isOpen_setOf_isUnit_mk K

end SeparationQuotient

namespace IsArtinianRing

/-- In a left-Artinian normed ring, an element less than unit distance from the
identity is a unit. This uses Coherent Modules' unit criterion for a left
regular element, with Artinianity on the original left regular module. -/
theorem isUnit_of_norm_one_sub_lt_one
    {R : Type uR} [NormedRing R] [IsArtinianRing R] {a : R}
    (ha : ‖1 - a‖ < 1) : IsUnit a :=
  (NormedRing.isLeftRegular_of_norm_one_sub_lt_one ha).isUnit_of_isArtinianRing

/-- The units of a left-Artinian normed ring form an open subset, without a
completeness or nontriviality assumption. -/
theorem isOpen_setOf_isUnit
    {R : Type uR} [NormedRing R] [IsArtinianRing R] :
    IsOpen {a : R | IsUnit a} :=
  isOpen_setOf_isUnit_of_near_one (fun a ha =>
    isUnit_of_norm_one_sub_lt_one (a := a) ha)

end IsArtinianRing
