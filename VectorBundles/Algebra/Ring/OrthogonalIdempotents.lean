/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Group.Units.Basic

/-!
# Intertwining finite families of orthogonal idempotents

For two finite families `p` and `q` of orthogonal idempotents in a semiring, the sum
`∑ i, q i * p i` intertwines every pair of corresponding idempotents. If this sum is a
unit, it conjugates the families and forces both families to sum to one. Completeness
is a conclusion, not an assumption; in particular, the diagonal sum is `∑ i, p i`,
which need not be one.
-/

@[expose] public section

open scoped BigOperators

universe uR uI

namespace OrthogonalIdempotents

variable {R : Type uR} [Semiring R] {I : Type uI} [Fintype I]
variable {p q : I → R}

/-- The matched-product sum on the diagonal is the sum of the family. -/
theorem sum_mul_self (hp : OrthogonalIdempotents p) :
    (∑ i, p i * p i) = ∑ i, p i := by
  exact Finset.sum_congr rfl (fun i _ ↦ (hp.idem i).eq)

/-- Right multiplication by a coordinate selects its matched product. -/
theorem sum_mul_mul (hp : OrthogonalIdempotents p) (q : I → R) (j : I) :
    (∑ i, q i * p i) * p j = q j * p j := by
  classical
  simp [Finset.sum_mul, mul_assoc, hp.mul_eq, mul_ite]

/-- Left multiplication by a coordinate selects its matched product. -/
theorem mul_sum_mul (hq : OrthogonalIdempotents q) (p : I → R) (j : I) :
    q j * (∑ i, q i * p i) = q j * p j := by
  classical
  simp [Finset.mul_sum, ← mul_assoc, hq.mul_eq, ite_mul]

/-- The matched-product sum intertwines corresponding orthogonal idempotents,
with both sides equal to the corresponding matched product. -/
theorem sum_mul_intertwines (hp : OrthogonalIdempotents p) (hq : OrthogonalIdempotents q) :
    ∀ j : I, (∑ i, q i * p i) * p j = q j * p j ∧
      q j * p j = q j * (∑ i, q i * p i) := by
  intro j
  exact ⟨hp.sum_mul_mul q j, (hq.mul_sum_mul p j).symm⟩

/-- The matched-product sum absorbs the sum of the right-hand family on the right. -/
theorem sum_mul_mul_sum (hp : OrthogonalIdempotents p) (q : I → R) :
    (∑ i, q i * p i) * (∑ i, p i) = ∑ i, q i * p i := by
  simp only [Finset.mul_sum, hp.sum_mul_mul]

/-- The matched-product sum absorbs the sum of the left-hand family on the left. -/
theorem sum_mul_sum_mul (hq : OrthogonalIdempotents q) (p : I → R) :
    (∑ i, q i) * (∑ i, q i * p i) = ∑ i, q i * p i := by
  simp only [Finset.sum_mul, hq.mul_sum_mul]

/-- A unit matched-product sum forces both orthogonal families to sum to one. -/
theorem sum_eq_one_of_isUnit_sum_mul (hp : OrthogonalIdempotents p)
    (hq : OrthogonalIdempotents q) (hu : IsUnit (∑ i, q i * p i)) :
    (∑ i, p i) = 1 ∧ (∑ i, q i) = 1 := by
  exact ⟨hu.mul_eq_left.mp (hp.sum_mul_mul_sum q),
    hu.mul_eq_right.mp (hq.sum_mul_sum_mul p)⟩

/-- If the matched-product sum is a unit, that prescribed unit conjugates the families,
and both orthogonal families are complete. -/
theorem exists_unit_conj_of_isUnit_sum_mul (hp : OrthogonalIdempotents p)
    (hq : OrthogonalIdempotents q) (hu : IsUnit (∑ i, q i * p i)) :
    ∃ U : Rˣ, (U : R) = (∑ i, q i * p i) ∧
      (∀ j : I, (U : R) * p j * (↑(U⁻¹) : R) = q j) ∧
      (∑ i, p i) = 1 ∧ (∑ i, q i) = 1 := by
  refine ⟨hu.unit, hu.unit_spec, ?_, hp.sum_eq_one_of_isUnit_sum_mul hq hu⟩
  intro j
  have hj : (hu.unit : R) * p j = q j * (hu.unit : R) := by
    rw [hu.unit_spec, hp.sum_mul_mul q j, hq.mul_sum_mul p j]
  calc
    (hu.unit : R) * p j * (↑(hu.unit⁻¹) : R) =
        q j * ((hu.unit : R) * (↑(hu.unit⁻¹) : R)) := by rw [hj, mul_assoc]
    _ = q j := by simp

end OrthogonalIdempotents
