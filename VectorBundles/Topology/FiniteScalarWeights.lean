/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Finite scalar dual coefficients

The real squared-norm sum of a finite scalar family gives conjugate-first
coefficients. Coefficients are defined for every index, including indices outside
the selected finite set. Neither definition requires topology on the domain.
-/

@[expose] public section

open scoped BigOperators

universe uI uX uK

namespace FiniteScalarWeights

variable {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]

/-- The real squared-norm sum of a scalar family over a finite set of indices. -/
noncomputable def denominator (s : Finset I) (w : I → X → K) (x : X) : ℝ :=
  ∑ i ∈ s, ‖w i x‖ ^ 2

/-- Conjugate-first dual coefficients, defined at every index of a scalar family. -/
noncomputable def dualCoeff (s : Finset I) (w : I → X → K) (i : I) (x : X) : K :=
  star (w i x) / (denominator s w x : K)


/-- The denominator is the finite real squared-norm sum. -/
theorem denominator_apply
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K) (x : X) :
    denominator s w x = ∑ i ∈ s, ‖w i x‖ ^ 2 := by
  rfl

/-- Every dual coefficient is the conjugate divided by the real squared-norm sum. -/
theorem dualCoeff_apply
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K) (i : I) (x : X) :
    dualCoeff s w i x =
      star (w i x) / ((∑ j ∈ s, ‖w j x‖ ^ 2 : ℝ) : K) := by
  rfl

/-- A finite scalar family without a common zero has positive denominator. -/
theorem denominator_pos
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (x : X) :
    0 < denominator s w x := by
  obtain ⟨i, hi, hwi⟩ := hcover x
  exact Finset.sum_pos' (fun j _ => sq_nonneg ‖w j x‖)
    ⟨i, hi, pow_pos (norm_pos_iff.mpr hwi) 2⟩

/-- The scalar image of the denominator is nonzero for a family without a common zero. -/
theorem denominator_coe_ne_zero
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (x : X) :
    (denominator s w x : K) ≠ 0 := by
  exact RCLike.ofReal_ne_zero.mpr (ne_of_gt (denominator_pos s w hcover x))

/-- The denominator is continuous when the selected scalar functions are continuous. -/
theorem continuous_denominator
    {I : Type uI} {X : Type uX} {K : Type uK}
    [TopologicalSpace X] [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcont : ∀ i ∈ s, Continuous (w i)) :
    Continuous (denominator s w) := by
  exact continuous_finsetSum s (fun i hi => (hcont i hi).norm.pow 2)

/-- A selected dual coefficient is continuous for a continuous family without a common zero. -/
theorem continuous_dualCoeff
    {I : Type uI} {X : Type uX} {K : Type uK}
    [TopologicalSpace X] [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcont : ∀ i ∈ s, Continuous (w i))
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0)
    (i : I) (hi : i ∈ s) :
    Continuous (dualCoeff s w i) := by
  exact (hcont i hi).star.div
    (RCLike.continuous_ofReal.comp (continuous_denominator s w hcont))
    (denominator_coe_ne_zero s w hcover)

/-- A dual coefficient is nonzero exactly where the original scalar function is nonzero. -/
theorem dualCoeff_ne_zero_iff
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (i : I) (x : X) :
    dualCoeff s w i x ≠ 0 ↔ w i x ≠ 0 := by
  simp [dualCoeff, denominator_coe_ne_zero s w hcover x]

/-- A dual coefficient and the original scalar function have equal cozero sets. -/
theorem support_dualCoeff
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (i : I) :
    Function.support (dualCoeff s w i) = Function.support (w i) := by
  ext x
  exact dualCoeff_ne_zero_iff s w hcover i x

/-- A dual coefficient and the original scalar function have equal closed-cozero supports. -/
theorem tsupport_dualCoeff
    {I : Type uI} {X : Type uX} {K : Type uK}
    [TopologicalSpace X] [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (i : I) :
    tsupport (dualCoeff s w i) = tsupport (w i) := by
  simpa only [tsupport] using congrArg closure (support_dualCoeff s w hcover i)

/-- The finite sum of a dual coefficient times its original scalar equals one. -/
theorem sum_dualCoeff_mul
    {I : Type uI} {X : Type uX} {K : Type uK} [RCLike K]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (x : X) :
    (∑ i ∈ s, dualCoeff s w i x * w i x) = 1 := by
  have hterm (i : I) : dualCoeff s w i x * w i x =
      ((‖w i x‖ ^ 2 : ℝ) : K) / (denominator s w x : K) := by
    rw [dualCoeff, div_mul_eq_mul_div]
    congr 1
    simpa using RCLike.conj_mul (w i x)
  calc
    (∑ i ∈ s, dualCoeff s w i x * w i x) =
        (∑ i ∈ s, ((‖w i x‖ ^ 2 : ℝ) : K)) / (denominator s w x : K) := by
      simp_rw [hterm]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (denominator s w x : K) / (denominator s w x : K) := by
      congr 1
      simp [denominator]
    _ = 1 := div_self (denominator_coe_ne_zero s w hcover x)

/-- Finite scalar coordinates reconstruct their common vector using the dual coefficients. -/
example {M : Type*} [AddCommMonoid M] [Module K M]
    (s : Finset I) (w : I → X → K)
    (hcover : ∀ x, ∃ i ∈ s, w i x ≠ 0) (x : X) (v : M) :
    (∑ i ∈ s, dualCoeff s w i x • (w i x • v)) = v := by
  simp_rw [← mul_smul]
  rw [← Finset.sum_smul, sum_dualCoeff_mul s w hcover x, one_smul]

end FiniteScalarWeights
