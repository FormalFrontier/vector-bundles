/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.GramRetraction
public import VectorBundles.Analysis.Normed.Operator.UnitGramContinuity
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic

/-!
# A nonisometric real-to-complex Gram calculation

Use the original real and complex norms, with `ℂ` regarded as a real inner-product
space. The forward map is `v ↦ (1 + I) * v`, and the adjoint is `z ↦ z.re + z.im`.
The Gram map is twice the identity, so its inverse is half the identity. The
residual at `1` is nonzero, and the image of `1` has norm `√2`, not `1`.

The adjoint-partner calculations are direct and do not use the generic Gram
injectivity, unit, retraction, or orthogonality theorems. The real-part partner
instead illustrates unit-only normalization through its characteristic API. Its
residual is not orthogonal to the image.
-/

@[expose] public section

namespace RealComplexGram

/-- A real-linear injection into the diagonal real line in `ℂ`. -/
noncomputable def gamma : ℝ →L[ℝ] ℂ :=
  (1 + Complex.I) • Complex.ofRealCLM

/-- The real adjoint of `gamma`. -/
noncomputable def sumReIm : ℂ →L[ℝ] ℝ :=
  Complex.reCLM + Complex.imCLM

/-- The inverse of twice the identity on `ℝ`. -/
noncomputable def half : ℝ →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem gamma_apply (v : ℝ) : gamma v = (1 + Complex.I) * (v : ℂ) := rfl

@[simp] theorem sumReIm_apply (z : ℂ) : sumReIm z = z.re + z.im := rfl

@[simp] theorem half_apply (v : ℝ) : half v = v / 2 := by
  simp [half, div_eq_mul_inv, mul_comm]

/-- The pairing identity is checked in the real inner products on the original
spaces, in the orientation of `Function.IsAdjointPair`. -/
theorem isAdjointPair :
    Function.IsAdjointPair (inner ℝ) (inner ℝ) gamma sumReIm := by
  intro v z
  rw [Complex.inner, Real.inner_apply, gamma_apply, sumReIm_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The real part recovers the input, so `gamma` is injective. -/
theorem gamma_injective : Function.Injective gamma := by
  intro x y h
  have hre := congrArg Complex.re h
  simpa [gamma_apply, Complex.mul_re, Complex.mul_im] using hre

/-- The Gram map is multiplication by two. -/
theorem gram_apply (v : ℝ) : sumReIm (gamma v) = 2 * v := by
  simp [sumReIm_apply, gamma_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The two-sided inverse is supplied by direct calculations, rather than by a
finite-dimensional unit criterion. -/
noncomputable def gramUnit : (ℝ →L[ℝ] ℝ)ˣ where
  val := sumReIm.comp gamma
  inv := half
  val_inv := by
    apply ContinuousLinearMap.ext
    intro v
    change sumReIm (gamma (half v)) = v
    rw [gram_apply, half_apply]
    ring
  inv_val := by
    apply ContinuousLinearMap.ext
    intro v
    change half (sumReIm (gamma v)) = v
    rw [gram_apply, half_apply]
    ring

/-- The total ring inverse agrees with the independently computed inverse. -/
theorem gram_inverse : Ring.inverse (sumReIm.comp gamma) = half := by
  exact Ring.inverse_unit gramUnit

/-- The inverse Gram composite takes the arithmetic mean of the coordinates. -/
theorem inverseGramComp_apply (z : ℂ) :
    ContinuousLinearMap.inverseGramComp gamma sumReIm z = (z.re + z.im) / 2 := by
  rw [ContinuousLinearMap.inverseGramComp_apply, gram_inverse, half_apply, sumReIm_apply]

/-- The ambient composite is the mean times `1 + I`. -/
theorem projected_apply (z : ℂ) :
    gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z) =
      (((z.re + z.im) / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [gamma_apply, inverseGramComp_apply]
  ring

/-- The full residual is the half-difference times `1 - I`. -/
theorem residual_apply (z : ℂ) :
    z - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z) =
      (((z.re - z.im) / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [projected_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The coordinate calculation annihilates the entire residual. -/
theorem residual_annihilated (z : ℂ) :
    sumReIm (z - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z)) = 0 := by
  rw [residual_apply]
  simp [sumReIm_apply, Complex.mul_re, Complex.mul_im]

/-- The residual is orthogonal to every image vector, using only the directly
checked pairing identity and residual calculation. -/
theorem inner_residual (v : ℝ) (z : ℂ) :
    inner ℝ (gamma v)
      (z - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z)) = 0 := by
  calc
    inner ℝ (gamma v)
        (z - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z)) =
        inner ℝ v
          (sumReIm (z - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm z))) :=
      isAdjointPair v _
    _ = 0 := by rw [residual_annihilated]; simp

/-- The example does not preserve the norm of `1`. -/
theorem norm_gamma_one : ‖gamma 1‖ = Real.sqrt 2 ∧ ‖gamma 1‖ ≠ 1 := by
  have hnorm : ‖gamma 1‖ = Real.sqrt 2 := by
    rw [gamma_apply]
    norm_num [Complex.norm_def, Complex.normSq_apply]
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  intro h
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h] at hsq
  norm_num at hsq

/-- The residual at `1` is exactly `(1 - I) / 2`, and is nonzero. -/
theorem residual_one :
    (1 : ℂ) - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm 1) =
        (1 - Complex.I) / 2 ∧
      (1 : ℂ) - gamma (ContinuousLinearMap.inverseGramComp gamma sumReIm 1) ≠ 0 := by
  constructor
  · rw [residual_apply]
    norm_num
    ring
  · intro h
    rw [residual_apply] at h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.mul_im] at hre

/-- With the real-part partner, the same diagonal has identity composite. -/
theorem re_comp_gamma :
    Complex.reCLM.comp gamma = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro v
  change (gamma v).re = v
  simp [gamma_apply, Complex.mul_re]

/-- The unit-only normalization with the real-part partner is the real part. -/
theorem inverseGramComp_re_apply (z : ℂ) :
    ContinuousLinearMap.inverseGramComp gamma Complex.reCLM z = z.re := by
  have hG : IsUnit (Complex.reCLM.comp gamma) := by
    rw [re_comp_gamma]
    exact isUnit_one
  have h := congrArg (fun T : ℂ →L[ℝ] ℝ => T z)
    (ContinuousLinearMap.gram_comp_inverseGramComp_of_isUnit
      (Γ := gamma) (S := Complex.reCLM) hG)
  simpa [re_comp_gamma] using h

/-- The real-part normalization has nonzero residual at `1`. -/
theorem residual_re_one :
    (1 : ℂ) - gamma (ContinuousLinearMap.inverseGramComp gamma Complex.reCLM 1) =
      -Complex.I := by
  rw [inverseGramComp_re_apply, gamma_apply]
  norm_num

/-- An invertible composite alone does not make the residual orthogonal. -/
theorem inner_residual_re_one :
    inner ℝ (gamma 1)
      ((1 : ℂ) - gamma (ContinuousLinearMap.inverseGramComp gamma Complex.reCLM 1)) =
        -1 := by
  rw [residual_re_one, gamma_apply]
  norm_num [Complex.inner, Complex.mul_re, Complex.mul_im]

end RealComplexGram


namespace RealComplexGram

/-- Positive rescaling of the given synthesis map preserves invertibility of its Gram. -/
theorem rescaled_gram_isUnit (t : ℝ) :
    IsUnit (sumReIm.comp ((1 + t ^ 2) • gamma)) := by
  have ha : (2 * (1 + t ^ 2) : ℝ) ≠ 0 := by positivity
  have hG : sumReIm.comp ((1 + t ^ 2) • gamma) =
      (2 * (1 + t ^ 2)) • (1 : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    change sumReIm ((1 + t ^ 2) • gamma v) = (2 * (1 + t ^ 2)) * v
    rw [map_smul, gram_apply]
    change (1 + t ^ 2) * (2 * v) = (2 * (1 + t ^ 2)) * v
    ring
  rw [hG]
  refine isUnit_iff_exists.mpr ?_
  refine ⟨(2 * (1 + t ^ 2))⁻¹ • (1 : ℝ →L[ℝ] ℝ), ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    change (2 * (1 + t ^ 2)) * ((2 * (1 + t ^ 2))⁻¹ * v) = v
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · apply ContinuousLinearMap.ext
    intro v
    change (2 * (1 + t ^ 2))⁻¹ * ((2 * (1 + t ^ 2)) * v) = v
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- The rescaled normalizer varies nontrivially with the scalar parameter. -/
theorem rescaled_inverseGramComp_apply (t : ℝ) (z : ℂ) :
    ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm z =
      (z.re + z.im) / (2 * (1 + t ^ 2)) := by
  have h := congrArg (fun T : ℂ →L[ℝ] ℝ => T z)
    (ContinuousLinearMap.gram_comp_inverseGramComp_of_isUnit (rescaled_gram_isUnit t))
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    map_smul, gram_apply, smul_eq_mul] at h
  apply (eq_div_iff (by positivity : (2 * (1 + t ^ 2) : ℝ) ≠ 0)).mpr
  calc
    _ = (1 + t ^ 2) * (2 *
        ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm z) := by ring
    _ = sumReIm z := h
    _ = z.re + z.im := sumReIm_apply z

/-- Rescaling changes the normalizer but leaves its ambient projection unchanged. -/
theorem rescaled_projection_eq (t : ℝ) :
    ((1 + t ^ 2) • gamma).comp
        (ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm) =
      gamma.comp (ContinuousLinearMap.inverseGramComp gamma sumReIm) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, smul_apply]
  rw [← map_smul, rescaled_inverseGramComp_apply, inverseGramComp_apply]
  congr 1
  change (1 + t ^ 2) * ((z.re + z.im) / (2 * (1 + t ^ 2))) = (z.re + z.im) / 2
  have ht : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [ht]

-- The given real-to-complex pair has a nonconstant normalizer
-- and a fixed nonzero proper projection.
example :
    Continuous (fun t : ℝ =>
      ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm) ∧
    Continuous (fun t : ℝ => ((1 + t ^ 2) • gamma).comp
      (ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm)) ∧
    ContinuousLinearMap.inverseGramComp ((1 + (0 : ℝ) ^ 2) • gamma) sumReIm 1 = 1 / 2 ∧
    ContinuousLinearMap.inverseGramComp ((1 + (1 : ℝ) ^ 2) • gamma) sumReIm 1 = 1 / 4 ∧
    (∀ t : ℝ, ((1 + t ^ 2) • gamma).comp
      (ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm) =
      gamma.comp (ContinuousLinearMap.inverseGramComp gamma sumReIm)) ∧
    (∀ t : ℝ, ((1 + t ^ 2) • gamma)
      (ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm 1) ≠ 0 ∧
      ((1 + t ^ 2) • gamma)
        (ContinuousLinearMap.inverseGramComp ((1 + t ^ 2) • gamma) sumReIm 1) ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_, rescaled_projection_eq, ?_⟩
  · exact ContinuousLinearMap.continuous_inverseGramComp_of_isUnit
      (by fun_prop) continuous_const rescaled_gram_isUnit
  · exact ContinuousLinearMap.continuous_gramProjection_of_isUnit
      (by fun_prop) continuous_const rescaled_gram_isUnit
  · rw [rescaled_inverseGramComp_apply]
    norm_num
  · rw [rescaled_inverseGramComp_apply]
    norm_num
  · intro t
    have hp := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) (rescaled_projection_eq t)
    simp only [ContinuousLinearMap.comp_apply] at hp
    refine ⟨?_, ?_⟩
    · rw [hp, projected_apply]
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
    · intro hP
      apply residual_one.2
      rw [← hp, hP, sub_self]

end RealComplexGram
