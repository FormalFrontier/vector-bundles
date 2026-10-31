/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Group.Idempotent

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
