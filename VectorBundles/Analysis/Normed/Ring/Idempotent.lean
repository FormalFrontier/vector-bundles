/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Norms of idempotents

The lower bound generalizes Mathlib's `one_le_norm_one` from the unit to idempotents.
-/

@[expose] public section

universe u

namespace IsIdempotentElem

variable {R : Type u} [NonUnitalNormedRing R] {p : R}

/-- A nonzero idempotent in a non-unital normed ring has norm at least one. -/
theorem one_le_norm (hp : IsIdempotentElem p) (hp0 : p ≠ 0) :
    1 ≤ ‖p‖ := by
  have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hmul : ‖p‖ ≤ ‖p‖ * ‖p‖ := by
    simpa only [hp.eq] using norm_mul_le p p
  exact (le_mul_iff_one_le_left hpos).mp hmul

/-- A nonzero contractive idempotent has norm exactly one. -/
theorem norm_eq_one (hp : IsIdempotentElem p) (hp0 : p ≠ 0)
    (hcontractive : ‖p‖ ≤ 1) : ‖p‖ = 1 := by
  exact le_antisymm hcontractive (hp.one_le_norm hp0)

end IsIdempotentElem


/-! ## Units conjugating close idempotents -/

/-- The normalized intertwiner of two idempotents intertwines them over any ring. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines
    {A : Type*} [Ring A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (q * p + (1 - q) * (1 - p)) * p = q * (q * p + (1 - q) * (1 - p)) := by
  have hpEq := isIdempotentElem_iff.mp hp
  have hqEq := isIdempotentElem_iff.mp hq
  calc
    (q * p + (1 - q) * (1 - p)) * p =
        q * (p * p) + (1 - q) * (p - p * p) := by noncomm_ring
    _ = q * p := by rw [hpEq]; simp
    _ = q * (q * p + (1 - q) * (1 - p)) := by
      symm
      calc
        q * (q * p + (1 - q) * (1 - p)) =
            (q * q) * p + (q - q * q) * (1 - p) := by noncomm_ring
        _ = q * p := by rw [hqEq]; simp

/-- The normalized intertwiner equals one on the diagonal. -/
theorem _root_.IsIdempotentElem.mul_add_mul_one_sub_self
    {A : Type*} [Ring A] {p : A} (hp : IsIdempotentElem p) :
    p * p + (1 - p) * (1 - p) = 1 := by
  have hpEq := isIdempotentElem_iff.mp hp
  calc
    p * p + (1 - p) * (1 - p) = 1 + (p * p - p) + (p * p - p) := by
      noncomm_ring
    _ = 1 := by rw [hpEq]; simp

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

/-- Idempotents at distance less than one have a unit normalized intertwiner.
The geometric-series hypothesis is inferred for complete normed rings, including the zero ring. -/
theorem _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub_of_norm_sub_lt_one
    {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    IsUnit (q * p + (1 - q) * (1 - p)) := by
  apply _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub hp hq
  apply isUnit_one_sub_of_norm_lt_one
  calc
    ‖(p - q) ^ 2‖ = ‖(p - q) * (p - q)‖ := by rw [pow_two]
    _ ≤ ‖p - q‖ * ‖p - q‖ := norm_mul_le _ _
    _ < 1 := by nlinarith [norm_nonneg (p - q)]

/-- Close idempotents are conjugate by a unit with the prescribed normalized value.
No commutativity, nontriviality, norm-one, or bound on the individual idempotents is needed. -/
theorem _root_.IsIdempotentElem.exists_unit_conj_eq_of_norm_sub_lt_one
    {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    ∃ u : Aˣ, (u : A) = q * p + (1 - q) * (1 - p) ∧
      (u : A) * p = q * (u : A) ∧ (u : A) * p * (↑u⁻¹ : A) = q := by
  have hu := _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub_of_norm_sub_lt_one hp hq h
  refine ⟨hu.unit, hu.unit_spec, ?_, ?_⟩
  · rw [hu.unit_spec]
    exact _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines hp hq
  · apply (Units.mul_inv_eq_iff_eq_mul hu.unit).2
    rw [hu.unit_spec]
    exact _root_.IsIdempotentElem.mul_add_mul_one_sub_intertwines hp hq
