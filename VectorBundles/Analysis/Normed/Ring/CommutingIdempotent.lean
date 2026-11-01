/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import VectorBundles.Algebra.Ring.CommutingIdempotent
import Mathlib.Tactic.Abel

/-!
# Norm gaps for commuting idempotents

An element with cubic defect of seminorm zero has seminorm zero or at least one.
Consequently, the difference between an idempotent and a commuting element whose
idempotence defect has seminorm zero has the same gap. Two commuting idempotents
therefore coincide at distance less than one in a normed ring.

The seminormed statements do not require separation. In particular, they apply to
the zero seminorm and do not infer equality from zero seminorm. No multiplicative
identity, completeness, scalar field, or restriction on the characteristic is required.
-/

@[expose] public section

universe u

variable {R : Type u}

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing R]

/-- An element whose cubic defect has seminorm zero has seminorm zero or at least one. -/
theorem norm_eq_zero_or_one_le_norm_of_cubic_defect {a : R}
    (ha : ‖(a * a) * a - a‖ = 0) : ‖a‖ = 0 ∨ 1 ≤ ‖a‖ := by
  have hle : ‖a‖ ≤ ‖(a * a) * a‖ := by
    calc
      ‖a‖ = ‖(a * a) * a - ((a * a) * a - a)‖ := by
        congr 1
        abel
      _ ≤ ‖(a * a) * a‖ + ‖(a * a) * a - a‖ := norm_sub_le _ _
      _ = ‖(a * a) * a‖ := by rw [ha, add_zero]
  have hcube : ‖a‖ ≤ ‖a‖ * ‖a‖ * ‖a‖ := hle.trans norm_mul₃_le
  rcases eq_or_lt_of_le (norm_nonneg a) with hzero | hpos
  · exact Or.inl hzero.symm
  · right
    by_contra hnot
    have hlt : ‖a‖ < 1 := lt_of_not_ge hnot
    have hsquare : ‖a‖ * ‖a‖ < ‖a‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hlt hpos
    have hcube_lt : ‖a‖ * ‖a‖ * ‖a‖ < ‖a‖ := by
      have hsquare_one : ‖a‖ * ‖a‖ < 1 := hsquare.trans hlt
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsquare_one hpos
    exact (not_lt_of_ge hcube) hcube_lt

namespace IsIdempotentElem

/-- The difference from an idempotent has seminorm zero or at least one if the other
element commutes with it and has idempotence defect of seminorm zero. No idempotence
assumption on the other element is needed. -/
theorem norm_sub_eq_zero_or_one_le_of_norm_mul_self_sub_eq_zero {e : R}
    (he : IsIdempotentElem e) (p : R) (hep : Commute e p) (hp : ‖p * p - p‖ = 0) :
    ‖e - p‖ = 0 ∨ 1 ≤ ‖e - p‖ := by
  apply norm_eq_zero_or_one_le_norm_of_cubic_defect
  rw [he.sub_cubic_defect p hep]
  let δ := p * p - p
  change ‖(3 : ℕ) • (e * δ) - p * δ - δ‖ = 0
  have hδ : ‖δ‖ = 0 := hp
  have hmul (a : R) : ‖a * δ‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    calc
      ‖a * δ‖ ≤ ‖a‖ * ‖δ‖ := norm_mul_le _ _
      _ = 0 := by rw [hδ, mul_zero]
  have hthree : ‖(3 : ℕ) • (e * δ)‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    calc
      ‖(3 : ℕ) • (e * δ)‖ ≤ 3 * ‖e * δ‖ := norm_nsmul_le
      _ = 0 := by rw [hmul e, mul_zero]
  apply le_antisymm _ (norm_nonneg _)
  calc
    ‖(3 : ℕ) • (e * δ) - p * δ - δ‖ ≤
        ‖(3 : ℕ) • (e * δ) - p * δ‖ + ‖δ‖ := norm_sub_le _ _
    _ ≤ (‖(3 : ℕ) • (e * δ)‖ + ‖p * δ‖) + ‖δ‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = 0 := by simp only [hthree, hmul p, hδ, add_zero]

/-- The difference of two commuting idempotents has seminorm zero or at least one. -/
theorem norm_sub_eq_zero_or_one_le {e p : R} (he : IsIdempotentElem e)
    (hp : IsIdempotentElem p) (hep : Commute e p) : ‖e - p‖ = 0 ∨ 1 ≤ ‖e - p‖ := by
  apply he.norm_sub_eq_zero_or_one_le_of_norm_mul_self_sub_eq_zero p hep
  have hpp : p * p = p := hp
  rw [hpp, sub_self, norm_zero]

end IsIdempotentElem

end NonUnitalSeminormedRing

namespace IsIdempotentElem

/-- Two commuting idempotents in a nonunital normed ring coincide when their distance
is strictly less than one. Separation is used only to turn zero norm into equality. -/
theorem eq_of_commute_of_norm_sub_lt_one [NonUnitalNormedRing R] {e p : R}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p) (hep : Commute e p)
    (h : ‖e - p‖ < 1) : e = p := by
  rcases he.norm_sub_eq_zero_or_one_le hp hep with hzero | hlarge
  · exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · exact False.elim ((not_lt_of_ge hlarge) h)

end IsIdempotentElem
