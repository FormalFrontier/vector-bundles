/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.NoncommRing
import VectorBundles.Algebra.Ring.OrthogonalIdempotents

/-!
# Idempotents and prescribed conjugacy in rings

The normalized intertwiner of two idempotents intertwines them without a
commutativity assumption. Multiplying it by the reversed intertwiner gives one
minus the square of their difference. If this defect is a unit, the normalized
intertwiner is a unit and conjugates the two idempotents.
-/

@[expose] public section

/-- The normalized intertwiner of two idempotents intertwines them over any ring. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (q * p + (1 - q) * (1 - p)) * p = q * (q * p + (1 - q) * (1 - p)) := by
  have h := (CompleteOrthogonalIdempotents.of_isIdempotentElem hp).toOrthogonalIdempotents
    |>.sum_mul_intertwines
      (CompleteOrthogonalIdempotents.of_isIdempotentElem hq).toOrthogonalIdempotents
      (0 : Fin 2)
  simpa [Fin.sum_univ_two] using h.1.trans h.2

/-- The normalized intertwiner equals one on the diagonal. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_self
    {A : Type*} [Ring A] {p : A} (hp : IsIdempotentElem p) :
    p * p + (1 - p) * (1 - p) = 1 := by
  have hpEq := isIdempotentElem_iff.mp hp
  calc
    p * p + (1 - p) * (1 - p) = 1 + (p * p - p) + (p * p - p) := by
      noncomm_ring
    _ = 1 := by rw [hpEq]; simp

/-- The product of the normalized intertwiner with the reversed intertwiner is the
squared-difference defect. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_mul_swap
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (q * p + (1 - q) * (1 - p)) * (p * q + (1 - p) * (1 - q)) =
      1 - (p - q) ^ 2 := by
  calc
    (q * p + (1 - q) * (1 - p)) * (p * q + (1 - p) * (1 - q)) =
        q * (p * p) * q + q * (p * (1 - p)) * (1 - q) +
          (1 - q) * ((1 - p) * p) * q +
          (1 - q) * ((1 - p) * (1 - p)) * (1 - q) := by noncomm_ring
    _ = q * p * q + (1 - q) * (1 - p) * (1 - q) := by
      simp only [hp.eq, hp.mul_one_sub_self, hp.one_sub_mul_self,
        hp.one_sub.eq, mul_zero, zero_mul, add_zero]
    _ = (1 - (p - q) ^ 2) + (p * p - p) + (q * q - q) +
        (q * q - q) := by noncomm_ring
    _ = 1 - (p - q) ^ 2 := by
      simp only [hp.eq, hq.eq, sub_self, add_zero]

/-- The reversed product of the normalized intertwiners has the same
squared-difference defect. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_swap_mul
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (p * q + (1 - p) * (1 - q)) * (q * p + (1 - q) * (1 - p)) =
      1 - (p - q) ^ 2 := by
  calc
    (p * q + (1 - p) * (1 - q)) * (q * p + (1 - q) * (1 - p)) =
        1 - (q - p) ^ 2 :=
      _root_.IsIdempotentElem.mul_add_mul_one_sub_mul_swap hq hp
    _ = 1 - (p - q) ^ 2 := by noncomm_ring

/-- The normalized intertwiner is a unit whenever one minus the difference square is a unit.
The factorization through `p + q - 1` avoids any commutativity assumption. -/
theorem _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : IsUnit (1 - (p - q) ^ 2)) :
    IsUnit (q * p + (1 - q) * (1 - p)) := by
  have hpEq := isIdempotentElem_iff.mp hp
  have hqEq := isIdempotentElem_iff.mp hq
  have hsquare : (p + q - 1) * (p + q - 1) = 1 - (p - q) ^ 2 := by
    calc
      (p + q - 1) * (p + q - 1) =
          (1 - (p - q) ^ 2) + (p * p - p) + (p * p - p) +
            (q * q - q) + (q * q - q) := by noncomm_ring
      _ = 1 - (p - q) ^ 2 := by rw [hpEq, hqEq]; simp
  have hreflection : (p + p - 1) * (p + p - 1) = 1 := by
    calc
      (p + p - 1) * (p + p - 1) =
          1 + (p * p - p) + (p * p - p) + (p * p - p) + (p * p - p) := by
        noncomm_ring
      _ = 1 := by rw [hpEq]; simp
  have ha : IsUnit (p + q - 1) := isUnit_mul_self_iff.mp (by rw [hsquare]; exact h)
  have hc : IsUnit (p + p - 1) := isUnit_mul_self_iff.mp (by
    rw [hreflection]
    exact isUnit_one)
  have hfactor : (p + q - 1) * (p + p - 1) = q * p + (1 - q) * (1 - p) := by
    calc
      (p + q - 1) * (p + p - 1) =
          (q * p + (1 - q) * (1 - p)) + (p * p - p) + (p * p - p) := by
        noncomm_ring
      _ = q * p + (1 - q) * (1 - p) := by rw [hpEq]; simp
  rw [← hfactor]
  exact ha.mul hc

/-- Idempotents whose squared-difference defect is a unit are conjugate by a unit
with the prescribed normalized value. -/
theorem _root_.IsIdempotentElem.exists_unit_conj_eq_of_isUnit_one_sub_sq
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : IsUnit (1 - (p - q) ^ 2)) :
    ∃ u : Aˣ, (u : A) = q * p + (1 - q) * (1 - p) ∧
      (u : A) * p = q * (u : A) ∧ (u : A) * p * (↑u⁻¹ : A) = q := by
  have hu := _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub hp hq h
  refine ⟨hu.unit, hu.unit_spec, ?_, ?_⟩
  · rw [hu.unit_spec]
    exact _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines hp hq
  · apply (Units.mul_inv_eq_iff_eq_mul hu.unit).2
    rw [hu.unit_spec]
    exact _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines hp hq
