/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.MetricPullback

/-!
# A Hermitian metric pulled back along squaring

The standard continuous metric on the trivial complex line over `ℝ` is pulled back along
`t ↦ t²`. The pullback pairing law gives `t` on fiber inputs `1` and `t`, a strictly positive
unit self-pairing at the base point `1`, and zero when the first input is zero. The
nonconstant scalar pairing comes from the varying fiber inputs, not from varying
coefficients of the standard metric.
-/

@[expose] public section

open Bundle

namespace MetricPullbackExamples

/-- Squaring as a continuous map of real bases. -/
def square : C(ℝ, ℝ) where
  toFun t := t ^ 2
  continuous_toFun := continuous_id.pow 2

/-- The pullback of the standard complex-line metric along squaring, with the structures
selected by the pullback constructor. -/
@[no_expose] noncomputable def squareMetric :=
  (ContinuousHermitianMetric.trivial ℂ ℝ ℂ).pullback square

/-- Pairing the unit section with the real-coordinate section gives a nonconstant function. -/
theorem squareMetric_inner_one_real (t : ℝ) :
    squareMetric.inner t (1 : ℂ) (t : ℂ) = (t : ℂ) := by
  simp [squareMetric, RCLike.inner_apply]

/-- The unit vector has strictly positive squared length over the base point `1`. -/
theorem squareMetric_positive_at_one :
    0 < RCLike.re (squareMetric.inner 1 (1 : ℂ) (1 : ℂ)) := by
  have h : squareMetric.inner 1 (1 : ℂ) (1 : ℂ) = 1 := by
    simpa using squareMetric_inner_one_real 1
  simpa only [h, RCLike.one_re] using (zero_lt_one : (0 : ℝ) < 1)

/-- The pairing with the zero section vanishes. -/
theorem squareMetric_inner_zero (t : ℝ) :
    squareMetric.inner t (0 : ℂ) (t : ℂ) = 0 := by
  simp [squareMetric]

end MetricPullbackExamples
