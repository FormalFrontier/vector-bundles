/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Reciprocal finite sums of real squares

The reciprocal of a finite sum of squares of continuous real weights is continuous
when the selected weights do not vanish simultaneously at any point.

This real, ordered-square specialization combines Mathlib's `continuous_finsetSum`,
`Continuous.pow`, `Finset.sum_sq_eq_zero_iff` and `Continuous.inv₀`. It does not assert
the corresponding result for arbitrary groups with zero or for sums of complex squares.
-/

@[expose] public section

universe uX uI

/-- The reciprocal of a finite sum of real squares is continuous if the selected
weights are continuous and, at each point, at least one selected weight is nonzero.
Weights outside the finite set are unrestricted, and the domain may be empty. -/
theorem continuous_inv_finset_sum_sq {X : Type uX} [TopologicalSpace X] {I : Type uI}
    (s : Finset I) (w : I → X → ℝ) (hw : ∀ i ∈ s, Continuous (w i))
    (h : ∀ x, ∃ i ∈ s, w i x ≠ 0) :
    Continuous (fun x => (Finset.sum s (fun i => (w i x) ^ 2))⁻¹) := by
  refine (continuous_finsetSum s (fun i hi => (hw i hi).pow 2)).inv₀ ?_
  intro x hx
  obtain ⟨i, hi, hwi⟩ := h x
  exact hwi ((Finset.sum_sq_eq_zero_iff s (fun j => w j x)).mp hx i hi)
