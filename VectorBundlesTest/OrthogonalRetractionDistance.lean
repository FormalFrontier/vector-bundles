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
It is the orthogonal complement of the imaginary axis, so it contains the real
unit but not the imaginary unit. Taking real parts does not increase distances.
-/

public section

example (z w : ℂ) (v : ℝ) :
    ‖z - (z.re : ℂ)‖ ≤ ‖z - (v : ℂ)‖ ∧
      (‖z - (v : ℂ)‖ = ‖z - (z.re : ℂ)‖ ↔ v = z.re) ∧
      ‖z - (z.re : ℂ)‖ = Metric.infDist z (Set.range Complex.realAxis) ∧
      (z ∈ closure (Set.range Complex.realAxis) ↔ ‖z - (z.re : ℂ)‖ = 0) ∧
      IsClosed (Set.range Complex.realAxis) ∧
      (z ∈ Complex.realPart.kerᗮ ↔ z.im = 0) ∧
      (1 : ℂ) ∈ Complex.realPart.kerᗮ ∧ Complex.I ∉ Complex.realPart.kerᗮ ∧
      dist (z.re : ℂ) (w.re : ℂ) ≤ dist z w := by
  have hmem (w : ℂ) : w ∈ Complex.realPart.kerᗮ ↔ w.im = 0 := by
    rw [← Complex.realPart_isOrthogonalRetraction.range_eq_orthogonal_ker]
    change (∃ v : ℝ, Complex.realAxis v = w) ↔ w.im = 0
    constructor
    · rintro ⟨v, rfl⟩
      simp only [Complex.realAxis_apply, Complex.ofReal_im]
    · intro hw
      refine ⟨w.re, ?_⟩
      apply Complex.ext
      · simp only [Complex.realAxis_apply, Complex.ofReal_re]
      · simpa only [Complex.realAxis_apply, Complex.ofReal_im] using hw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, hmem z, ?_, ?_, ?_⟩
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_le z v
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_eq_iff z v
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.norm_sub_image_eq_infDist z
  · rw [Complex.realPart_isOrthogonalRetraction.closure_range_eq_orthogonalBilin_ker]
    simpa only [SetLike.mem_coe, Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.mem_orthogonalBilin_ker_iff_norm_sub_image_eq_zero z
  · exact Complex.realPart_isOrthogonalRetraction.isClosed_range
  · exact (hmem 1).2 (by simp)
  · intro hI
    have hzero := (hmem Complex.I).1 hI
    simp at hzero
  · simpa only [Complex.realAxis_apply, Complex.realPart_apply] using
      Complex.realPart_isOrthogonalRetraction.dist_image_image_le z w
