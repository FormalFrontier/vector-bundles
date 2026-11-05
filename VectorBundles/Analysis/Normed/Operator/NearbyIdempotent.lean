/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import VectorBundles.Analysis.Normed.Ring.Units
import VectorBundles.Analysis.Normed.Algebra.Units
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nearby idempotents and kernel coordinates

Finite-dimensional compression gives range and kernel equivalences for
norm-close bounded idempotents. For continuous families, the kernel graph
has based product coordinates with the original subspace topology.
The quadratic error identity bounds the inverse on the fixed range.
Neither scalar nor ambient completeness is required.
-/

@[expose] public section
universe uK uA uX uV uW uY
namespace ContinuousLinearMap
variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
variable (P Q : A →L[K] A)

/-- The fixed operator with its inherited range norm. -/
def fixedRangeComponent : A →L[K] (LinearMap.range (P : A →ₗ[K] A)) :=
  P.rangeRestrict

/-- Compression to the original range of the fixed operator. -/
def fixedRangeCompression :
    (LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)) where
  toFun e := fixedRangeComponent P (Q e)
  map_add' := by intro e f; simp
  map_smul' := by intro c e; simp
  cont := (fixedRangeComponent P).continuous.comp
    (Q.continuous.comp continuous_subtype_val)

@[simp] theorem fixedRangeComponent_apply (a : A) :
    (fixedRangeComponent P a : A) = P a := rfl

@[simp] theorem fixedRangeCompression_apply (e : (LinearMap.range (P : A →ₗ[K] A))) :
    (fixedRangeCompression P Q e : A) = P (Q e) := rfl

private theorem fixedRange_fixed (hP : IsIdempotentElem P) (e : (LinearMap.range (P : A →ₗ[K] A))) :
    P (e : A) = e :=
  (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp e.property

/-- The error of compression on the fixed range is quadratic. -/
theorem sub_fixedRangeCompression_eq_square
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (e : (LinearMap.range (P : A →ₗ[K] A))) :
    (e : A) - (fixedRangeCompression P Q e : A) =
      (P - Q) ((P - Q) (e : A)) := by
  have hPe := fixedRange_fixed P hP e
  change Q * Q = Q at hQ
  have hQQ : Q (Q (e : A)) = Q e :=
    congrArg (fun T : A →L[K] A => T (e : A)) hQ
  change (e : A) - P (Q e) = (P - Q) ((P - Q) (e : A))
  simp only [_root_.sub_apply, map_sub, hPe, hQQ]
  abel

/-- The compression error has norm at most the squared gap. -/
theorem norm_sub_fixedRangeCompression_le
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (e : (LinearMap.range (P : A →ₗ[K] A))) :
    ‖e - fixedRangeCompression P Q e‖ ≤ ‖Q - P‖ ^ 2 * ‖e‖ := by
  calc
    ‖e - fixedRangeCompression P Q e‖ = ‖(P - Q) ((P - Q) (e : A))‖ :=
      congrArg norm (sub_fixedRangeCompression_eq_square P Q hP hQ e)
    _ ≤ ‖P - Q‖ * ‖(P - Q) (e : A)‖ := (P - Q).le_opNorm _
    _ ≤ ‖P - Q‖ * (‖P - Q‖ * ‖e‖) :=
      mul_le_mul_of_nonneg_left ((P - Q).le_opNorm e) (norm_nonneg _)
    _ = ‖Q - P‖ ^ 2 * ‖e‖ := by rw [norm_sub_rev P Q]; ring

/-- The compression is bounded below by one minus the squared gap. -/
theorem one_sub_sq_mul_norm_le_norm_compression
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (e : (LinearMap.range (P : A →ₗ[K] A))) :
    (1 - ‖Q - P‖ ^ 2) * ‖e‖ ≤ ‖fixedRangeCompression P Q e‖ := by
  have hb := norm_sub_fixedRangeCompression_le P Q hP hQ e
  have ht : ‖e‖ ≤ ‖e - fixedRangeCompression P Q e‖ + ‖fixedRangeCompression P Q e‖ := by
    calc
      ‖e‖ = ‖(e - fixedRangeCompression P Q e) + fixedRangeCompression P Q e‖ :=
        by rw [sub_add_cancel]
      _ ≤ ‖e - fixedRangeCompression P Q e‖ + ‖fixedRangeCompression P Q e‖ :=
        norm_add_le _ _
  nlinarith only [hb, ht]

private theorem compressionGap_pos (h : ‖Q - P‖ < 1) :
    0 < 1 - ‖Q - P‖ ^ 2 := by
  have hn := norm_nonneg (Q - P)
  have hp : 0 < 1 + ‖Q - P‖ := by linarith
  have hm := mul_pos (sub_pos.mpr h) hp
  nlinarith only [hm]

/-- A gap less than one makes compression injective. -/
theorem fixedRangeCompression_injective
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) : Function.Injective (fixedRangeCompression P Q) := by
  let t : ℝ := 1 - ‖Q - P‖ ^ 2
  have ht : 0 < t := compressionGap_pos P Q h
  have hb (e : LinearMap.range (P : A →ₗ[K] A)) :
      ‖e‖ ≤ (⟨t⁻¹, inv_nonneg.mpr ht.le⟩ : NNReal) * ‖fixedRangeCompression P Q e‖ := by
    change ‖e‖ ≤ t⁻¹ * ‖fixedRangeCompression P Q e‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ ht).2 (by
      simpa only [mul_comm] using one_sub_sq_mul_norm_le_norm_compression P Q hP hQ e)
  exact (AddMonoidHomClass.antilipschitz_of_bound (fixedRangeCompression P Q) hb).injective

/-- Algebraic finite dimension turns injectivity into surjectivity. -/
theorem fixedRangeCompression_surjective [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) : Function.Surjective (fixedRangeCompression P Q) := by
  exact LinearMap.injective_iff_surjective.mp
      (fixedRangeCompression_injective P Q hP hQ h)

section Inverse
variable [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
variable (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (h : ‖Q - P‖ < 1)

include hP hQ h in
/-- Each nearby idempotent induces an invertible compression on the fixed range. -/
theorem isUnit_fixedRangeCompression : IsUnit (fixedRangeCompression P Q) := by
  let R := LinearMap.range (P : A →ₗ[K] A)
  let : FiniteDimensional K (R →L[K] R) :=
    FiniteDimensional.of_injective
      (ContinuousLinearMap.coeLM K : (R →L[K] R) →ₗ[K] (R →ₗ[K] R))
      ContinuousLinearMap.coe_injective
  apply FiniteDimensional.isUnit_of_norm_one_sub_lt_one K
  have hb : ‖1 - fixedRangeCompression P Q‖ ≤ ‖Q - P‖ ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
    intro e
    exact norm_sub_fixedRangeCompression_le P Q hP hQ e
  have hp := compressionGap_pos P Q h
  linarith

/-- Compression is a unit in the bounded endomorphism algebra of the fixed range. -/
noncomputable def fixedRangeCompressionUnit :
    ((LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)))ˣ :=
  (isUnit_fixedRangeCompression P Q hP hQ h).unit

@[simp] theorem fixedRangeCompressionUnit_val :
    (fixedRangeCompressionUnit P Q hP hQ h).val = fixedRangeCompression P Q :=
  (isUnit_fixedRangeCompression P Q hP hQ h).unit_spec

/-- The inverse is continuous and has an explicit reciprocal-gap bound. -/
noncomputable def fixedRangeCompressionInverse :
    (LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)) :=
  ↑((fixedRangeCompressionUnit P Q hP hQ h)⁻¹)

@[simp] theorem fixedRangeCompressionUnit_inv :
    (↑((fixedRangeCompressionUnit P Q hP hQ h)⁻¹) :
      (LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A))) =
      fixedRangeCompressionInverse P Q hP hQ h := rfl

@[simp] theorem compression_fixedRangeCompressionInverse (e : (LinearMap.range (P : A →ₗ[K] A))) :
    fixedRangeCompression P Q (fixedRangeCompressionInverse P Q hP hQ h e) = e := by
  exact congrArg (fun T : (LinearMap.range (P : A →ₗ[K] A)) →L[K]
    (LinearMap.range (P : A →ₗ[K] A)) => T e)
      (isUnit_fixedRangeCompression P Q hP hQ h).mul_val_inv

@[simp] theorem fixedRangeCompressionInverse_compression (e : (LinearMap.range (P : A →ₗ[K] A))) :
    fixedRangeCompressionInverse P Q hP hQ h (fixedRangeCompression P Q e) = e := by
  exact congrArg (fun T : (LinearMap.range (P : A →ₗ[K] A)) →L[K]
    (LinearMap.range (P : A →ₗ[K] A)) => T e)
      (isUnit_fixedRangeCompression P Q hP hQ h).val_inv_mul

/-- The inverse operator norm is controlled by the squared gap. -/
theorem norm_fixedRangeCompressionInverse_le :
    ‖fixedRangeCompressionInverse P Q hP hQ h‖ ≤ (1 - ‖Q - P‖ ^ 2)⁻¹ := by
  have hp := compressionGap_pos P Q h
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hp.le)
  intro e
  have hb := one_sub_sq_mul_norm_le_norm_compression P Q hP hQ
    (fixedRangeCompressionInverse P Q hP hQ h e)
  rw [compression_fixedRangeCompressionInverse] at hb
  calc
    ‖fixedRangeCompressionInverse P Q hP hQ h e‖ ≤ ‖e‖ / (1 - ‖Q - P‖ ^ 2) :=
      (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hb)
    _ = (1 - ‖Q - P‖ ^ 2)⁻¹ * ‖e‖ := by rw [div_eq_mul_inv, mul_comm]

end Inverse
end ContinuousLinearMap

namespace ContinuousLinearMap
variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
variable (P Q : A →L[K] A)

private theorem eq_zero_of_fixed_of_norm_sub_lt_one (w : A)
    (hQw : Q w = w) (hPw : P w = 0)
    (hgap : ‖P - Q‖ < 1) : w = 0 := by
  have hi := (AntilipschitzWith.id : AntilipschitzWith 1 (id : A → A)).add_lipschitzWith
    (P - Q).lipschitzWith (by simpa using (show ‖P - Q‖₊ < 1 from NNReal.coe_lt_coe.mp hgap))
  apply hi.injective
  change w + (P - Q) w = 0 + (P - Q) 0
  simp only [_root_.sub_apply, hPw, hQw, zero_sub, add_neg_cancel, map_zero, add_zero]

private theorem apply_sub_eq_zero (v c : A)
    (hPQ : P (Q c) = P (Q v))
    (hQQ : Q (Q (v - c)) = Q (v - c))
    (hgap : ‖P - Q‖ < 1) : Q (v - c) = 0 := by
  have hPk : P (Q (v - c)) = 0 := by
    calc
      P (Q (v - c)) = P (Q v) - P (Q c) := by rw [map_sub, map_sub]
      _ = 0 := sub_eq_zero.mpr hPQ.symm
  exact eq_zero_of_fixed_of_norm_sub_lt_one P Q (Q (v - c)) hQQ hPk hgap

private theorem sub_sub_projection (v c : A)
    (hv : P v = 0) (hc : P c = c) :
    (v - c) - P (v - c) = v := by
  rw [map_sub, hv, hc, zero_sub, sub_neg_eq_add, sub_add_cancel]


private theorem idempotent_apply (hP : IsIdempotentElem P) (a : A) :
    P (P a) = P a :=
  congrArg (fun R : A →L[K] A => R a) hP

theorem sub_self_apply_mem_kernel (hP : IsIdempotentElem P) (a : A) :
    a - P a ∈ LinearMap.ker (P : A →ₗ[K] A) := by
  change P (a - P a) = 0
  rw [map_sub, idempotent_apply P hP, sub_self]

theorem continuous_kernelCoordinate (hP : IsIdempotentElem P) :
    Continuous (fun a : A =>
      (⟨a - P a, sub_self_apply_mem_kernel P hP a⟩ : (LinearMap.ker (P : A →ₗ[K] A)))) :=
  (continuous_id.sub P.continuous).subtype_mk _

/-- Fixed-kernel coordinates with the inherited norm. -/
def kernelCoordinate (hP : IsIdempotentElem P) : A →L[K] (LinearMap.ker (P : A →ₗ[K] A)) where
  toFun a := ⟨a - P a, sub_self_apply_mem_kernel P hP a⟩
  map_add' := by intro a b; apply Subtype.ext; simp [sub_add_sub_comm]
  map_smul' := by intro c a; apply Subtype.ext; simp [smul_sub]
  cont := continuous_kernelCoordinate P hP

@[simp] theorem kernelCoordinate_apply (hP : IsIdempotentElem P) (a : A) :
    (kernelCoordinate P hP a : A) = a - P a := rfl

/-- The finite-range correction to a fixed-kernel vector. -/
noncomputable def kernelCorrection [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) :
    (LinearMap.ker (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)) where
  toFun v := fixedRangeCompressionInverse P Q hP hQ h
    (fixedRangeComponent P (Q v))
  map_add' := by intro v w; simp
  map_smul' := by intro c v; simp
  cont := (fixedRangeCompressionInverse P Q hP hQ h).continuous.comp
    ((fixedRangeComponent P).continuous.comp
      (Q.continuous.comp continuous_subtype_val))

@[simp] theorem kernelCorrection_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (v : (LinearMap.ker (P : A →ₗ[K] A))) :
    kernelCorrection P Q hP hQ h v =
      fixedRangeCompressionInverse P Q hP hQ h (fixedRangeComponent P (Q v)) := rfl

/-- Transport into the nearby kernel in the original ambient space. -/
noncomputable def kernelTransport [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) : (LinearMap.ker (P : A →ₗ[K] A)) →L[K] A where
  toFun v := (v : A) - (kernelCorrection P Q hP hQ h v : A)
  map_add' := by intro v w; simp [sub_add_sub_comm]
  map_smul' := by intro c v; simp [smul_sub]
  cont := continuous_subtype_val.sub
    (continuous_subtype_val.comp (kernelCorrection P Q hP hQ h).continuous)

@[simp] theorem kernelTransport_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (v : (LinearMap.ker (P : A →ₗ[K] A))) :
    kernelTransport P Q hP hQ h v =
      (v : A) - (kernelCorrection P Q hP hQ h v : A) := rfl

theorem kernelTransport_mem [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (v : (LinearMap.ker (P : A →ₗ[K] A))) :
    Q (kernelTransport P Q hP hQ h v) = 0 := by
  have hB := compression_fixedRangeCompressionInverse
    P Q hP hQ h (fixedRangeComponent P (Q v))
  have hPQ : P (Q (kernelCorrection P Q hP hQ h v : A)) = P (Q v) :=
    congrArg (fun e : (LinearMap.range (P : A →ₗ[K] A)) => (e : A)) hB
  exact apply_sub_eq_zero P Q v
    (kernelCorrection P Q hP hQ h v) hPQ
    (idempotent_apply Q hQ _) (by simpa only [norm_sub_rev] using h)

theorem kernelCoordinate_kernelTransport [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (v : (LinearMap.ker (P : A →ₗ[K] A))) :
    kernelCoordinate P hP (kernelTransport P Q hP hQ h v) = v := by
  apply Subtype.ext
  exact sub_sub_projection P v
    (kernelCorrection P Q hP hQ h v) v.property
    (fixedRange_fixed P hP _)

theorem kernelTransport_kernelCoordinate [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (u : A) (hu : Q u = 0) :
    kernelTransport P Q hP hQ h (kernelCoordinate P hP u) = u := by
  have hB : fixedRangeComponent P (Q (kernelCoordinate P hP u)) =
      fixedRangeCompression P Q (-fixedRangeComponent P u) := by
    apply Subtype.ext
    change P (Q (u - P u)) = P (Q (-P u))
    simp only [map_sub, map_neg, hu, zero_sub]
  have hc : kernelCorrection P Q hP hQ h (kernelCoordinate P hP u) =
      -fixedRangeComponent P u := by
    change fixedRangeCompressionInverse P Q hP hQ h
      (fixedRangeComponent P (Q (kernelCoordinate P hP u))) = _
    rw [hB, fixedRangeCompressionInverse_compression]
  change (u - P u) -
    (kernelCorrection P Q hP hQ h (kernelCoordinate P hP u) : A) = u
  rw [hc]
  change (u - P u) - (-P u) = u
  rw [sub_neg_eq_add, sub_add_cancel]

theorem continuous_kernelTransport_subtype [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) :
    Continuous (fun v : (LinearMap.ker (P : A →ₗ[K] A)) =>
      (⟨kernelTransport P Q hP hQ h v, kernelTransport_mem P Q hP hQ h v⟩ :
        LinearMap.ker (Q : A →ₗ[K] A))) :=
  (kernelTransport P Q hP hQ h).continuous.subtype_mk _

/-- Nearby kernels with their inherited norms and topologies. -/
noncomputable def nearbyKernelEquiv [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) : (LinearMap.ker (P : A →ₗ[K] A)) ≃L[K] LinearMap.ker (Q : A →ₗ[K] A) where
  toLinearEquiv :=
    { toFun := fun v => ⟨kernelTransport P Q hP hQ h v,
        kernelTransport_mem P Q hP hQ h v⟩
      invFun := fun u => kernelCoordinate P hP u
      left_inv := kernelCoordinate_kernelTransport P Q hP hQ h
      right_inv := by
        intro u; apply Subtype.ext
        exact kernelTransport_kernelCoordinate P Q hP hQ h u u.property
      map_add' := by
        intro v w; apply Subtype.ext
        exact (kernelTransport P Q hP hQ h).map_add v w
      map_smul' := by
        intro c v; apply Subtype.ext
        exact (kernelTransport P Q hP hQ h).map_smul c v }
  continuous_toFun := continuous_kernelTransport_subtype P Q hP hQ h
  continuous_invFun := (kernelCoordinate P hP).continuous.comp
    continuous_subtype_val

@[simp] theorem nearbyKernelEquiv_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (v : (LinearMap.ker (P : A →ₗ[K] A))) :
    (nearbyKernelEquiv P Q hP hQ h v : A) =
      (v : A) - (kernelCorrection P Q hP hQ h v : A) := rfl

@[simp] theorem nearbyKernelEquiv_symm_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (u : LinearMap.ker (Q : A →ₗ[K] A)) :
    ((nearbyKernelEquiv P Q hP hQ h).symm u : A) = (u : A) - P u := rfl

theorem continuous_nearbyRangeForward :
    Continuous (fun e : (LinearMap.range (P : A →ₗ[K] A)) => (⟨Q e, ⟨(e : A), rfl⟩⟩ :
      LinearMap.range (Q : A →ₗ[K] A))) :=
  (Q.continuous.comp continuous_subtype_val).subtype_mk _

theorem nearbyRange_right_inv [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (u : LinearMap.range (Q : A →ₗ[K] A)) :
    Q (fixedRangeCompressionInverse P Q hP hQ h (fixedRangeComponent P u) : A) = u := by
  let c := fixedRangeCompressionInverse P Q hP hQ h (fixedRangeComponent P u)
  have hPQ : P (Q (c : A)) = P u :=
    congrArg (fun e : (LinearMap.range (P : A →ₗ[K] A)) => (e : A))
      (compression_fixedRangeCompressionInverse P Q hP hQ h (fixedRangeComponent P u))
  have hQu : Q (u : A) = u := fixedRange_fixed Q hQ u
  have hQQ : Q (Q (c : A) - u) = Q (c : A) - u := by
    rw [map_sub, idempotent_apply Q hQ, hQu]
  have hPk : P (Q (c : A) - u) = 0 := by
    rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_fixed_of_norm_sub_lt_one
    P Q (Q (c : A) - u) hQQ hPk (by simpa only [norm_sub_rev] using h))

/-- Q identifies the fixed range with the nearby range. -/
noncomputable def nearbyRangeEquiv [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) :
    (LinearMap.range (P : A →ₗ[K] A)) ≃L[K] LinearMap.range (Q : A →ₗ[K] A) where
  toLinearEquiv :=
    { toFun := fun e => ⟨Q e, ⟨e, rfl⟩⟩
      invFun := fun u => fixedRangeCompressionInverse P Q hP hQ h
        (fixedRangeComponent P u)
      left_inv := fixedRangeCompressionInverse_compression P Q hP hQ h
      right_inv := by
        intro u; apply Subtype.ext
        exact nearbyRange_right_inv P Q hP hQ h u
      map_add' := by intro e f; apply Subtype.ext; simp
      map_smul' := by intro c e; apply Subtype.ext; simp }
  continuous_toFun := continuous_nearbyRangeForward P Q
  continuous_invFun := (fixedRangeCompressionInverse P Q hP hQ h).continuous.comp
    ((fixedRangeComponent P).continuous.comp continuous_subtype_val)

@[simp] theorem nearbyRangeEquiv_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (e : (LinearMap.range (P : A →ₗ[K] A))) :
    (nearbyRangeEquiv P Q hP hQ h e : A) = Q e := rfl

@[simp] theorem nearbyRangeEquiv_symm_apply [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) (u : LinearMap.range (Q : A →ₗ[K] A)) :
    (nearbyRangeEquiv P Q hP hQ h).symm u =
      fixedRangeCompressionInverse P Q hP hQ h (fixedRangeComponent P u) := rfl

/-- Nearby range dimension is a consequence, not a hypothesis. -/
theorem finiteDimensional_range_of_norm_sub_lt_one
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : ‖Q - P‖ < 1) : FiniteDimensional K (LinearMap.range (Q : A →ₗ[K] A)) :=
  FiniteDimensional.of_injective
    (nearbyRangeEquiv P Q hP hQ h).symm.toLinearEquiv.toLinearMap
    (nearbyRangeEquiv P Q hP hQ h).symm.injective

end ContinuousLinearMap

namespace ContinuousLinearMap
variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
variable (P : A →L[K] A)
section Family
variable {X : Type uX} [TopologicalSpace X] (q : X → A →L[K] A)

private theorem continuous_operator_application
    {V : Type uV} {W : Type uW} {Y : Type uY}
    [NormedAddCommGroup V] [NormedSpace K V]
    [NormedAddCommGroup W] [NormedSpace K W] [TopologicalSpace Y]
    (T : Y → V →L[K] W) (v : Y → V) (hT : Continuous T) (hv : Continuous v) :
    Continuous (fun y => T y (v y)) :=
  hT.clm_apply hv

/-- The compression inverse depends continuously on the base point. -/
theorem continuous_fixedRangeCompressionInverse
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) :
    Continuous (fun x : {x : X // ‖q x - P‖ < 1} =>
      fixedRangeCompressionInverse P (q x) hP (hq x) x.property) := by
  have hB : Continuous (fun x : {x : X // ‖q x - P‖ < 1} => fixedRangeCompression P (q x)) := by
    change Continuous (fun x : {x : X // ‖q x - P‖ < 1} =>
      (fixedRangeComponent P).comp ((q x).comp (LinearMap.range (P : A →ₗ[K] A)).subtypeL))
    have hright : Continuous (fun x : {x : X // ‖q x - P‖ < 1} =>
        (q x).comp (LinearMap.range (P : A →ₗ[K] A)).subtypeL) :=
      ((ContinuousLinearMap.compL K (LinearMap.range (P : A →ₗ[K] A)) A A).flip
        (LinearMap.range (P : A →ₗ[K] A)).subtypeL).continuous.comp
          (hc.comp continuous_subtype_val)
    exact ((ContinuousLinearMap.compL K (LinearMap.range (P : A →ₗ[K] A)) A
      (LinearMap.range (P : A →ₗ[K] A))) (fixedRangeComponent P)).continuous.comp hright
  let u : {x : X // ‖q x - P‖ < 1} →
      ((LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)))ˣ := fun x =>
    fixedRangeCompressionUnit P (q x) hP (hq x) x.property
  have hu : Continuous u :=
    (Units.isEmbedding_val_seminormedRing).continuous_iff.mpr (by
      simpa only [Function.comp_def, u, fixedRangeCompressionUnit_val] using hB)
  have hi : Continuous (fun x : {x : X // ‖q x - P‖ < 1} =>
      (↑((u x)⁻¹) : (LinearMap.range (P : A →ₗ[K] A)) →L[K] (LinearMap.range (P : A →ₗ[K] A)))) :=
    Units.isEmbedding_val_seminormedRing.continuous.comp hu.inv
  simpa only [u, fixedRangeCompressionUnit_inv] using hi

/-- Kernel transport is jointly continuous in the base and the vector. -/
theorem continuous_kernelTransport_family [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P)
    (hq : ∀ x, IsIdempotentElem (q x)) (hc : Continuous q) :
    Continuous (fun z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) =>
      kernelTransport P (q z.1) hP (hq z.1) z.1.property z.2) := by
  have hv : Continuous (fun z : {x : X // ‖q x - P‖ < 1} ×
      (LinearMap.ker (P : A →ₗ[K] A)) => q z.1 (z.2 : A)) :=
    by
      have hq' : Continuous (fun z : {x : X // ‖q x - P‖ < 1} ×
          (LinearMap.ker (P : A →ₗ[K] A)) => q z.1) :=
        (hc.comp continuous_subtype_val).comp continuous_fst
      have hv' : Continuous (fun z : {x : X // ‖q x - P‖ < 1} ×
          (LinearMap.ker (P : A →ₗ[K] A)) => (z.2 : A)) :=
        continuous_subtype_val.comp continuous_snd
      exact continuous_operator_application _ _ hq' hv'
  have hcorr : Continuous (fun z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) =>
      kernelCorrection P (q z.1) hP (hq z.1) z.1.property z.2) := by
    change Continuous (fun z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) =>
      fixedRangeCompressionInverse P (q z.1) hP (hq z.1) z.1.property
        (fixedRangeComponent P (q z.1 z.2)))
    have hC : Continuous (fun z : {x : X // ‖q x - P‖ < 1} ×
        (LinearMap.ker (P : A →ₗ[K] A)) =>
        fixedRangeCompressionInverse P (q z.1) hP (hq z.1) z.1.property) :=
      (continuous_fixedRangeCompressionInverse P q hP hq hc).comp continuous_fst
    have hV := (fixedRangeComponent P).continuous.comp hv
    exact continuous_operator_application _ _ hC hV
  change Continuous (fun z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) =>
    (z.2 : A) - (kernelCorrection P (q z.1) hP (hq z.1) z.1.property z.2 : A))
  exact (continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp hcorr)

/-- Forward kernel coordinates on the open norm neighborhood. -/
noncomputable def nearbyKernelGraphForward [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x)) :
    {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) →
      {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0} :=
  fun z =>
    let v := nearbyKernelEquiv P (q z.1) hP (hq z.1) z.1.property z.2
    ⟨(z.1, (v : A)), v.property⟩

/-- The graph coordinate map does not invert a varying operator. -/
def nearbyKernelGraphBackward (hP : IsIdempotentElem P) :
    {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0} →
      {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) :=
  fun z => (z.val.1, kernelCoordinate P hP z.val.2)

omit [TopologicalSpace X] in
theorem nearbyKernelGraph_left_inv [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x)) :
    Function.LeftInverse (nearbyKernelGraphBackward P q hP)
      (nearbyKernelGraphForward P q hP hq) := by
  intro z
  apply Prod.ext
  · rfl
  · exact kernelCoordinate_kernelTransport P (q z.1) hP (hq z.1) z.1.property z.2

omit [TopologicalSpace X] in
theorem nearbyKernelGraph_right_inv [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x)) :
    Function.RightInverse (nearbyKernelGraphBackward P q hP)
      (nearbyKernelGraphForward P q hP hq) := by
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact kernelTransport_kernelCoordinate P (q z.val.1) hP
      (hq z.val.1) z.val.1.property z.val.2 z.property

theorem continuous_nearbyKernelGraphForward [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) :
    Continuous (nearbyKernelGraphForward P q hP hq) := by
  exact (continuous_fst.prodMk
    (continuous_kernelTransport_family P q hP hq hc)).subtype_mk _

theorem continuous_nearbyKernelGraphBackward (hP : IsIdempotentElem P) :
    Continuous (nearbyKernelGraphBackward P q hP) := by
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    ((kernelCoordinate P hP).continuous.comp
      (continuous_snd.comp continuous_subtype_val))

/-- Based product coordinates on the original kernel graph subspace. -/
noncomputable def nearbyKernelGraphHomeomorph
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) :
    {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A)) ≃ₜ
      {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0} where
  toFun := nearbyKernelGraphForward P q hP hq
  invFun := nearbyKernelGraphBackward P q hP
  left_inv := nearbyKernelGraph_left_inv P q hP hq
  right_inv := nearbyKernelGraph_right_inv P q hP hq
  continuous_toFun := continuous_nearbyKernelGraphForward P q hP hq hc
  continuous_invFun := continuous_nearbyKernelGraphBackward P q hP

@[simp] theorem nearbyKernelGraphHomeomorph_apply_fst
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) (z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A))) :
    (nearbyKernelGraphHomeomorph P q hP hq hc z).val.1 = z.1 := rfl

@[simp] theorem nearbyKernelGraphHomeomorph_apply_snd
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) (z : {x : X // ‖q x - P‖ < 1} × (LinearMap.ker (P : A →ₗ[K] A))) :
    (nearbyKernelGraphHomeomorph P q hP hq hc z).val.2 =
      kernelTransport P (q z.1) hP (hq z.1) z.1.property z.2 := rfl

@[simp] theorem nearbyKernelGraphHomeomorph_symm_apply
    [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) (z : {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0}) :
    (nearbyKernelGraphHomeomorph P q hP hq hc).symm z =
      (z.val.1, kernelCoordinate P hP z.val.2) := rfl

/-- A kernel section is continuous exactly when its fixed coordinate is. -/
theorem continuous_iff_kernelCoordinate [FiniteDimensional K (LinearMap.range (P : A →ₗ[K] A))]
    (hP : IsIdempotentElem P) (hq : ∀ x, IsIdempotentElem (q x))
    (hc : Continuous q) (s : {x : X // ‖q x - P‖ < 1} → A)
    (hs : ∀ x : {x : X // ‖q x - P‖ < 1}, q x (s x) = 0) :
    Continuous s ↔ Continuous (fun x => kernelCoordinate P hP (s x)) := by
  constructor
  · intro h
    exact (kernelCoordinate P hP).continuous.comp h
  · intro h
    let H := nearbyKernelGraphHomeomorph P q hP hq hc
    have ht : Continuous (fun x : {x : X // ‖q x - P‖ < 1} => (x, kernelCoordinate P hP (s x))) :=
      continuous_id.prodMk h
    have hcurve := continuous_snd.comp
      (continuous_subtype_val.comp (H.continuous_toFun.comp ht))
    have he : (fun x : {x : X // ‖q x - P‖ < 1} =>
        (H (x, kernelCoordinate P hP (s x))).val.2) = s := by
      funext x
      exact congrArg (fun z : {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0} => z.val.2)
        (H.apply_symm_apply
          (⟨(x, s x), hs x⟩ : {z : {x : X // ‖q x - P‖ < 1} × A // q z.1 z.2 = 0}))
    exact he ▸ hcurve
end Family
end ContinuousLinearMap
