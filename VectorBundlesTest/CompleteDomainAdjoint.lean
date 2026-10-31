/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier contributors
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A real-to-complex adjoint

The real-linear map `v ↦ (1 + t * I) * v` has adjoint
`z ↦ z.re + t * z.im`, for the standard real inner products.
The inner-product identity identifies this coordinate functional with
`ContinuousLinearMap.adjointMap`. Both maps retain the standard norms and
topologies on `ℝ` and `ℂ`.
-/

@[expose] public section

namespace CompleteDomainAdjoint

/-- A real line in the standard complex plane, with slope `t`. -/
noncomputable def complexLine (t : ℝ) : ℝ →L[ℝ] ℂ :=
  (1 + (t : ℂ) * Complex.I) • Complex.ofRealCLM

@[simp] theorem complexLine_apply (t v : ℝ) :
    complexLine t v = (1 + (t : ℂ) * Complex.I) * (v : ℂ) := by
  simp [complexLine, smul_eq_mul]

/-- The coordinate functional paired with `complexLine t`. -/
noncomputable def complexLinePartner (t : ℝ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM + t • Complex.imCLM

@[simp] theorem complexLinePartner_apply (t : ℝ) (z : ℂ) :
    complexLinePartner t z = z.re + t * z.im := by
  simp [complexLinePartner, smul_eq_mul]

/-- The given pair uses the usual real inner product on the complex plane. -/
theorem complexLine_isAdjointPair (t : ℝ) :
    Function.IsAdjointPair (inner ℝ : ℝ → ℝ → ℝ)
      (inner ℝ : ℂ → ℂ → ℝ) (complexLine t) (complexLinePartner t) := by
  rw [Function.isAdjointPair_iff]
  intro v z
  rw [complexLine_apply, complexLinePartner_apply, Real.inner_apply]
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change (z * star ((1 + (t : ℂ) * Complex.I) * (v : ℂ))).re =
    v * (z.re + t * z.im)
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

/-- The complete-domain adjoint of the complex line is its coordinate functional. -/
theorem adjointMap_complexLine_apply (t : ℝ) (z : ℂ) :
    ContinuousLinearMap.adjointMap (complexLine t) z = z.re + t * z.im := by
  have h := (ContinuousLinearMap.isAdjointPair_iff_eq_adjointMap
    (complexLine t) (complexLinePartner t)).mp (complexLine_isAdjointPair t)
  simpa only [complexLinePartner_apply] using (congrFun h z).symm

/-- The adjoint at slope one takes `1 + I` to two. -/
theorem adjointMap_complexLine_one_add_I :
    ContinuousLinearMap.adjointMap (complexLine 1) (1 + Complex.I) = 2 := by
  rw [adjointMap_complexLine_apply]
  norm_num

end CompleteDomainAdjoint
