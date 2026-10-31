/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Projection.Distance
public import VectorBundlesTest.OrthogonalRetraction

/-!
# Closest points on the real axis

The real part is the unique closest real point to a complex number. The real axis
is closed, and membership in its closure is characterized by zero residual norm.
-/

public section

example (z : ℂ) (v : ℝ) :
    ‖z - (z.re : ℂ)‖ ≤ ‖z - (v : ℂ)‖ ∧
      (‖z - (v : ℂ)‖ = ‖z - (z.re : ℂ)‖ ↔ v = z.re) ∧
      ‖z - (z.re : ℂ)‖ = Metric.infDist z (Set.range Complex.realAxis) ∧
      (z ∈ closure (Set.range Complex.realAxis) ↔ ‖z - (z.re : ℂ)‖ = 0) ∧
      IsClosed (Set.range Complex.realAxis) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_le z v
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_eq_iff z v
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_eq_infDist z
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.mem_closure_range_iff_norm_sub_image_eq_zero z
  · exact Complex.realPart_isOrthogonalRetraction.isClosed_range
