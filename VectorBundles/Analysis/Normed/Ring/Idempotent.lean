/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Analysis.SpecificLimits.Normed
public import VectorBundles.Algebra.Ring.Idempotent
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

private theorem isUnit_one_sub_sq_of_norm_sub_lt_one
    {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {p q : A}
    (h : ‖p - q‖ < 1) : IsUnit (1 - (p - q) ^ 2) := by
  apply isUnit_one_sub_of_norm_lt_one
  calc
    ‖(p - q) ^ 2‖ = ‖(p - q) * (p - q)‖ := by rw [pow_two]
    _ ≤ ‖p - q‖ * ‖p - q‖ := norm_mul_le _ _
    _ < 1 := by nlinarith [norm_nonneg (p - q)]

/-- Idempotents at distance less than one have a unit normalized intertwiner.
The geometric-series hypothesis is inferred for complete normed rings, including the zero ring. -/
theorem _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub_of_norm_sub_lt_one
    {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    IsUnit (q * p + (1 - q) * (1 - p)) := by
  exact _root_.IsIdempotentElem.isUnit_mul_add_mul_one_sub hp hq
    (isUnit_one_sub_sq_of_norm_sub_lt_one h)

/-- Close idempotents are conjugate by a unit with the prescribed normalized value.
No commutativity, nontriviality, norm-one, or bound on the individual idempotents is needed. -/
theorem _root_.IsIdempotentElem.exists_unit_conj_eq_of_norm_sub_lt_one
    {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {p q : A}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    ∃ u : Aˣ, (u : A) = q * p + (1 - q) * (1 - p) ∧
      (u : A) * p = q * (u : A) ∧ (u : A) * p * (↑u⁻¹ : A) = q := by
  exact _root_.IsIdempotentElem.exists_unit_conj_eq_of_isUnit_one_sub_sq hp hq
    (isUnit_one_sub_sq_of_norm_sub_lt_one h)
