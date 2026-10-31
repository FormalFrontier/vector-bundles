/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Operator.KernelChart
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Oblique kernels in the Euclidean complex plane

All norms, submodule structures, and subtype topologies are inherited.
-/

@[expose] public section

noncomputable section

namespace Complex

open ContinuousLinearMap

/-- The square-zero map sending the imaginary coordinate to the real axis. -/
def imagToReal : ℂ →L[ℝ] ℂ := ofRealCLM.comp imCLM

/-- The real shear with matrix `[[1,t],[0,1]]`. -/
def realShear (t : ℝ) : ℂ →L[ℝ] ℂ := 1 + t • imagToReal

/-- Projection onto the real axis along a line of slope parameter `t`. -/
def obliqueProjection (t : ℝ) : ℂ →L[ℝ] ℂ :=
  ofRealCLM.comp reCLM - t • imagToReal

@[simp]
theorem imagToReal_apply (z : ℂ) : imagToReal z = (z.im : ℂ) := rfl

@[simp]
theorem realShear_apply (t : ℝ) (z : ℂ) :
    realShear t z = z + ((t * z.im : ℝ) : ℂ) := by
  simp [realShear, Algebra.smul_def, Complex.ofReal_mul]

@[simp]
theorem obliqueProjection_apply (t : ℝ) (z : ℂ) :
    obliqueProjection t z = ((z.re - t * z.im : ℝ) : ℂ) := by
  simp [obliqueProjection, Algebra.smul_def, Complex.ofReal_sub, Complex.ofReal_mul]

@[simp]
theorem imagToReal_sq : imagToReal * imagToReal = 0 := by
  ext z
  simp

/-- The family is continuous in operator norm. -/
theorem continuous_obliqueProjection : Continuous obliqueProjection :=
  continuous_const.sub (continuous_id.smul continuous_const)

@[simp]
theorem obliqueProjection_idempotent (t : ℝ) :
    obliqueProjection t * obliqueProjection t = obliqueProjection t := by
  ext z
  change obliqueProjection t (obliqueProjection t z) = obliqueProjection t z
  simp

theorem mem_ker_obliqueProjection (t : ℝ) (z : ℂ) :
    z ∈ (obliqueProjection t).ker ↔ z.re = t * z.im := by
  change obliqueProjection t z = 0 ↔ _
  constructor
  · intro h
    have h' : z.re - t * z.im = 0 := by simpa using congrArg Complex.re h
    exact sub_eq_zero.mp h'
  · intro h
    simp [h]

@[simp]
theorem kernelTransport_obliqueProjection (t : ℝ) :
    kernelTransport obliqueProjection 0 t = realShear t := by
  ext z
  apply Complex.ext <;>
    simp [kernelTransport_apply, realShear_apply]

theorem realShear_neg_cancel (t : ℝ) (z : ℂ) :
    realShear (-t) (realShear t z) = z := by
  apply Complex.ext <;> simp [realShear_apply]

private def realShearUnit (t : ℝ) : (ℂ →L[ℝ] ℂ)ˣ where
  val := realShear t
  inv := realShear (-t)
  val_inv := by ext z; simp [realShear_apply]
  inv_val := by ext z; exact realShear_neg_cancel t z

@[simp]
theorem inverse_realShear (t : ℝ) :
    Ring.inverse (realShear t) = realShear (-t) :=
  Ring.inverse_unit (realShearUnit t)

/-- The shear preserves the imaginary coordinate and tilts the real one. -/
def realShearEquiv (t : ℝ) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { (realShear t).toLinearMap with
      invFun := realShear (-t)
      left_inv := realShear_neg_cancel t
      right_inv := by intro z; simp [realShear_apply] }
  continuous_toFun := (realShear t).continuous
  continuous_invFun := (realShear (-t)).continuous

@[simp]
theorem realShearEquiv_apply (t : ℝ) (z : ℂ) :
    realShearEquiv t z = realShear t z := rfl

@[simp]
theorem realShearEquiv_symm_apply (t : ℝ) (z : ℂ) :
    (realShearEquiv t).symm z = realShear (-t) z := rfl

/-- The equivalence from a tilted kernel line to the imaginary axis. -/
def obliqueKernelEquiv (t : ℝ) :
    (obliqueProjection t).ker ≃L[ℝ] (obliqueProjection 0).ker where
  toFun a := ⟨realShear (-t) a, by
    rw [mem_ker_obliqueProjection]
    have h := (mem_ker_obliqueProjection t (a : ℂ)).mp a.2
    simpa [realShear_apply, sub_eq_add_neg] using sub_eq_zero.mpr h⟩
  invFun v := ⟨realShear t v, by
    rw [mem_ker_obliqueProjection]
    have h := (mem_ker_obliqueProjection 0 (v : ℂ)).mp v.2
    simpa [realShear_apply] using congrArg (fun r => r + t * (v : ℂ).im) h⟩
  left_inv a := by
    apply Subtype.ext
    simp [realShear_apply]
  right_inv v := Subtype.ext (realShear_neg_cancel t v)
  map_add' a b := Subtype.ext ((realShear (-t)).map_add a b)
  map_smul' c a := Subtype.ext ((realShear (-t)).map_smul c a)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (realShear (-t)).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (realShear t).continuous.comp continuous_subtype_val

@[simp]
theorem obliqueKernelEquiv_apply (t : ℝ) (a : (obliqueProjection t).ker) :
    (obliqueKernelEquiv t a : ℂ) = realShear (-t) a := rfl

@[simp]
theorem obliqueKernelEquiv_symm_apply (t : ℝ) (v : (obliqueProjection 0).ker) :
    ((obliqueKernelEquiv t).symm v : ℂ) = realShear t v := rfl

/-- A product chart on the inherited total space of the tilted kernels. -/
def obliqueKernelHomeomorph (V : Set ℝ) :
    KernelTotalSpace obliqueProjection V ≃ₜ V × (obliqueProjection 0).ker where
  toFun z := (z.1.1, obliqueKernelEquiv z.1.1.1 ⟨z.1.2, z.2⟩)
  invFun y := ⟨(y.1, ((obliqueKernelEquiv y.1.1).symm y.2 : ℂ)),
    ((obliqueKernelEquiv y.1.1).symm y.2).2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val ((obliqueKernelEquiv z.1.1.1).symm_apply_apply
        (⟨z.1.2, z.2⟩ : (obliqueProjection z.1.1.1).ker))
  right_inv y := by
    apply Prod.ext
    · rfl
    · exact (obliqueKernelEquiv y.1.1).apply_symm_apply y.2
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      change Continuous (fun z : KernelTotalSpace obliqueProjection V =>
        realShear (-z.1.1.1) z.1.2)
      simp only [realShear_apply]
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_fst
    change Continuous (fun y : V × (obliqueProjection 0).ker =>
      realShear y.1.1 (y.2 : ℂ))
    simp only [realShear_apply]
    fun_prop

@[simp]
theorem obliqueKernelHomeomorph_apply (V : Set ℝ)
    (z : KernelTotalSpace obliqueProjection V) :
    obliqueKernelHomeomorph V z =
      (z.1.1, obliqueKernelEquiv z.1.1.1 ⟨z.1.2, z.2⟩) := rfl

@[simp]
theorem obliqueKernelHomeomorph_symm_apply_val (V : Set ℝ)
    (y : V × (obliqueProjection 0).ker) :
    ((obliqueKernelHomeomorph V).symm y).1 =
      (y.1, realShear y.1.1 (y.2 : ℂ)) := rfl

/-- The explicit chart satisfies the inverse-transport prescription. -/
theorem isKernelChart_obliqueKernelHomeomorph (V : Set ℝ) :
    IsKernelChart obliqueProjection 0 V (obliqueKernelHomeomorph V) where
  base_apply _ := rfl
  vector_apply z := by
    change realShear (-z.1.1.1) z.1.2 = _
    rw [kernelTransport_obliqueProjection, inverse_realShear]
  base_symm_apply _ := rfl
  vector_symm_apply y := by
    change realShear y.1.1 (y.2 : ℂ) = _
    rw [kernelTransport_obliqueProjection]

/-- The nilpotent has Euclidean operator norm one. -/
@[simp]
theorem norm_imagToReal : ‖imagToReal‖ = 1 := by
  apply le_antisymm
  · apply imagToReal.opNorm_le_bound zero_le_one
    intro z
    simpa using (RCLike.abs_im_le_norm z)
  · simpa using imagToReal.le_opNorm I

theorem norm_kernelTransport_obliqueProjection_sub_one (t : ℝ) :
    ‖kernelTransport obliqueProjection 0 t - 1‖ = |t| := by
  rw [kernelTransport_obliqueProjection]
  simp [realShear, norm_smul, Real.norm_eq_abs]

@[simp]
theorem kernelChartDomain_obliqueProjection :
    kernelChartDomain obliqueProjection 0 = Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  ext t
  change ‖kernelTransport obliqueProjection 0 t - 1‖ < (1 / 2 : ℝ) ↔
    -(1 / 2 : ℝ) < t ∧ t < 1 / 2
  rw [norm_kernelTransport_obliqueProjection_sub_one]
  exact abs_lt

/-- A nonzero parameter in the canonical chart neighborhood. -/
def quarterParameter : kernelChartDomain obliqueProjection 0 :=
  ⟨1 / 4, by rw [kernelChartDomain_obliqueProjection]; constructor <;> norm_num⟩

@[simp]
theorem quarterParameter_val : (quarterParameter : ℝ) = 1 / 4 := rfl

theorem quarterParameter_ne_zero : (quarterParameter : ℝ) ≠ 0 := by norm_num

/-- The oblique family supplies every output of the kernel-chart specification. -/
def obliqueKernelChart : KernelChart obliqueProjection 0 :=
  kernelChart obliqueProjection continuous_obliqueProjection obliqueProjection_idempotent 0

/-- The imaginary unit in the central kernel. -/
def imaginaryAxisVector : (obliqueProjection 0).ker := ⟨I, by simp⟩

@[simp]
theorem imaginaryAxisVector_val : (imaginaryAxisVector : ℂ) = I := rfl

/-- A nonzero vector on the quarter-parameter kernel line. -/
def quarterKernelPoint :
    KernelTotalSpace obliqueProjection (kernelChartDomain obliqueProjection 0) :=
  ⟨(quarterParameter, ((1 / 4 : ℝ) : ℂ) + I), by
    change obliqueProjection (1 / 4) (((1 / 4 : ℝ) : ℂ) + I) = 0
    norm_num⟩

@[simp]
theorem quarterKernelPoint_val : quarterKernelPoint.1 =
    (quarterParameter, ((1 / 4 : ℝ) : ℂ) + I) := rfl

/-- The chart sends a tilted vector to the imaginary axis at a nonzero base. -/
theorem obliqueKernelChart_quarter_apply :
    obliqueKernelChart.homeomorph quarterKernelPoint =
      (quarterParameter, imaginaryAxisVector) := by
  apply Prod.ext
  · exact obliqueKernelChart.isKernelChart.base_apply _
  · apply Subtype.ext
    rw [obliqueKernelChart.isKernelChart.vector_apply]
    change Ring.inverse (kernelTransport obliqueProjection 0 (1 / 4))
      (((1 / 4 : ℝ) : ℂ) + I) = I
    rw [kernelTransport_obliqueProjection, inverse_realShear]
    apply Complex.ext <;> norm_num [realShear_apply]

/-- The inverse chart recovers the tilted quarter-parameter vector. -/
theorem obliqueKernelChart_quarter_symm_apply :
    (obliqueKernelChart.homeomorph.symm (quarterParameter, imaginaryAxisVector)).1.2 =
      ((1 / 4 : ℝ) : ℂ) + I := by
  rw [KernelChart.symm_apply_val]
  simp [add_comm]

/-- Two parameters inside the chart neighborhood give different kernels. -/
theorem obliqueProjection_quarter_ker_ne :
    (obliqueProjection (1 / 4)).ker ≠ (obliqueProjection 0).ker := by
  intro h
  have hi : I ∈ (obliqueProjection (1 / 4)).ker := by rw [h]; simp
  norm_num at hi

/-- The Euclidean norm of the sheared imaginary unit detects the parameter. -/
theorem norm_realShear_I_sq (t : ℝ) : ‖realShear t I‖ ^ 2 = 1 + t ^ 2 := by
  rw [RCLike.norm_sq_eq_def]
  simp [realShear_apply]
  ring

/-- Nonzero parameters give a fibre map that does not preserve Euclidean norms. -/
theorem obliqueKernelEquiv_symm_norm_ne (t : ℝ) (ht : t ≠ 0) :
    ‖((obliqueKernelEquiv t).symm imaginaryAxisVector : ℂ)‖ ≠
      ‖(imaginaryAxisVector : ℂ)‖ := by
  change ‖realShear t I‖ ≠ ‖I‖
  intro h
  have hs := norm_realShear_I_sq t
  rw [h, norm_I] at hs
  nlinarith [sq_pos_of_ne_zero ht]

/-- The inverse fibre equivalence is not an isometry away from zero. -/
theorem not_isometry_obliqueKernelEquiv_symm (t : ℝ) (ht : t ≠ 0) :
    ¬ Isometry (obliqueKernelEquiv t).symm := by
  intro h
  have hd := h.dist_eq imaginaryAxisVector 0
  simp only [map_zero, dist_zero_right] at hd
  exact obliqueKernelEquiv_symm_norm_ne t ht hd

end Complex

