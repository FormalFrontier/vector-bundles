/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Analysis.Normed.Ring.Idempotent

/-!
# Compatibility with the unit norm lower bound

The generic idempotent bound specializes to Mathlib's `one_le_norm_one`,
including its universe and normed-ring hypotheses.
-/

universe u

example (R : Type u) [NormedRing R] [Nontrivial R] : 1 ≤ ‖(1 : R)‖ :=
  (IsIdempotentElem.one : IsIdempotentElem (1 : R)).one_le_norm one_ne_zero
