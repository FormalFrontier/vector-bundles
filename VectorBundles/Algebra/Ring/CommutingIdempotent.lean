/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel

/-!
# Cubic identities for commuting idempotents

The cubic defect of the difference from an idempotent is expressed in terms of the
idempotence defect of a commuting element. In particular, the difference of two
commuting idempotents is tripotent. These identities require no multiplicative identity
and hold in every characteristic.
-/

@[expose] public section

universe u

namespace IsIdempotentElem

variable {R : Type u} [NonUnitalRing R] {e p : R}

/-- The cubic defect of the difference from an idempotent is controlled by the
idempotence defect of a commuting element. The coefficient is natural-number
additive repetition, so no multiplicative identity is required. -/
theorem sub_cubic_defect (he : IsIdempotentElem e) (p : R) (hep : Commute e p) :
    ((e - p) * (e - p)) * (e - p) - (e - p) =
      (3 : ℕ) • (e * (p * p - p)) - p * (p * p - p) - (p * p - p) := by
  have hee : e * e = e := he
  have hpe : p * e = e * p := (show e * p = p * e from hep).symm
  have hepe : e * p * e = e * p := by
    calc
      e * p * e = e * (p * e) := mul_assoc _ _ _
      _ = e * (e * p) := by rw [hpe]
      _ = (e * e) * p := (mul_assoc _ _ _).symm
      _ = e * p := by rw [hee]
  have hppe : p * p * e = e * p * p := by
    calc
      p * p * e = p * (p * e) := mul_assoc _ _ _
      _ = p * (e * p) := by rw [hpe]
      _ = (p * e) * p := (mul_assoc _ _ _).symm
      _ = e * p * p := by rw [hpe]
  simp only [sub_mul, mul_sub, ← mul_assoc, hee, hpe, hepe, hppe]
  abel

/-- The difference of two commuting idempotents is tripotent, without a
multiplicative identity or a restriction on the characteristic. -/
theorem sub_cubic_eq_self (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : Commute e p) : ((e - p) * (e - p)) * (e - p) = e - p := by
  have hpp : p * p = p := hp
  have h := he.sub_cubic_defect p hep
  simp only [hpp, sub_self, mul_zero, nsmul_zero] at h
  exact sub_eq_zero.mp h

end IsIdempotentElem
