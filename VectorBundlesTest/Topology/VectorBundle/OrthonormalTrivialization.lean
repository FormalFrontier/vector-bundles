/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import VectorBundles.Topology.VectorBundle.OrthonormalTrivialization

/-!
# A varying metric on the trivial real line bundle

`VariableMetricLine.metric` weights the usual real inner product by `1 + b²` at the base
point `b : ℝ`. It is continuous as a section of the iterated Hom bundle, while the model
fiber, fiber norms, and total-space topology remain those of the usual trivial real line.

The bounded-sublevel and Hom-coordinate continuity proofs follow
`Bundle.ContinuousHermitianMetric.trivial`.
-/

@[expose] public section

open Bundle Bornology

namespace VariableMetricLine

private theorem weight_pos (b : ℝ) : 0 < 1 + b ^ 2 := by positivity

private theorem bounded_sublevel (b : ℝ) :
    IsVonNBounded ℝ {v : ℝ | (1 + b ^ 2) * v * v < 1} := by
  apply NormedSpace.isVonNBounded_of_isBounded ℝ
  apply Metric.isBounded_ball.subset (t := Metric.ball (0 : ℝ) 1)
  intro v hv
  change (1 + b ^ 2) * v * v < 1 at hv
  have hv' : v ^ 2 < 1 := by
    have h := mul_nonneg (sq_nonneg b) (sq_nonneg v)
    nlinarith
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
    (sq_lt_one_iff_abs_lt_one v).mp hv'

private theorem continuous_form :
    Continuous (fun b : ℝ ↦ (1 + b ^ 2) • innerSL ℝ (E := ℝ)) := by
  fun_prop

/-- A continuous Hermitian metric on the usual trivial real line bundle whose squared lengths
at `b` are multiplied by `1 + b²`. No norm or topology is replaced. -/
@[no_expose] noncomputable def metric :
    Bundle.ContinuousHermitianMetric ℝ ℝ (Bundle.Trivial ℝ ℝ) where
  inner b := (1 + b ^ 2) • innerSL ℝ
  symm b v w := by simp [mul_comm]
  pos b v hv := by
    simpa [Real.inner_apply, pow_two, mul_assoc] using
      mul_pos (weight_pos b) (sq_pos_of_ne_zero hv)
  isVonNBounded b := by
    simpa [pow_two, mul_assoc] using bounded_sublevel b
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_id, ?_⟩
    convert! continuous_form.continuousAt (x := x)
    ext v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]

/-- The metric evaluates to the weighted product `(1 + b²) * v * w`. -/
@[simp]
theorem metric_inner_apply (b v w : ℝ) :
    metric.inner b v w = (1 + b ^ 2) * v * w := by
  simp only [metric, smul_apply, smul_eq_mul, innerSL_apply_apply,
    Real.inner_apply, mul_assoc]

/-- The same nonzero vector has different squared lengths at base points zero and one. -/
theorem metric_at_zero_and_one : metric.inner 0 1 1 = 1 ∧ metric.inner 1 1 1 = 2 := by
  norm_num

end VariableMetricLine

namespace OrthonormalTrivializationExamples

/-- One normalized chart for the varying metric sends the original unit vector to coordinates
with squared norms one and two at zero and one. The metric itself is proved independently. -/
private theorem varyingMetric_orthonormalization :
    let e := Bundle.Trivial.trivialization ℝ ℝ
    let c := VariableMetricLine.metric.orthonormalizeTrivialization e
    c.baseSet = Set.univ ∧
      (∀ b : ℝ, IsLinearMap ℝ (fun v : ℝ ↦ (c (TotalSpace.mk' ℝ b v)).2)) ∧
      ‖(c (TotalSpace.mk' ℝ 0 1)).2‖ ^ 2 = 1 ∧
      ‖(c (TotalSpace.mk' ℝ 1 1)).2‖ ^ 2 = 2 := by
  dsimp only
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro b
    exact VariableMetricLine.metric.orthonormalizeTrivialization_isLinearMap
      (Bundle.Trivial.trivialization ℝ ℝ) (b := b) (by simp)
  · rw [← real_inner_self_eq_norm_sq]
    exact (VariableMetricLine.metric.orthonormalizeTrivialization_inner
      (Bundle.Trivial.trivialization ℝ ℝ) (b := 0) (by simp) 1 1).trans
        VariableMetricLine.metric_at_zero_and_one.1
  · rw [← real_inner_self_eq_norm_sq]
    exact (VariableMetricLine.metric.orthonormalizeTrivialization_inner
      (Bundle.Trivial.trivialization ℝ ℝ) (b := 1) (by simp) 1 1).trans
        VariableMetricLine.metric_at_zero_and_one.2

/-- Normalization also applies to the trivial rank-zero bundle, without any
nonempty-coordinate hypothesis. -/
private theorem rankZero_orthonormalization :
    let V := EuclideanSpace ℝ (Fin 0)
    let g := ContinuousHermitianMetric.trivial ℝ ℝ V
    let e := Bundle.Trivial.trivialization ℝ V
    let c := g.orthonormalizeTrivialization e
    c.baseSet = Set.univ ∧
      ∀ b : ℝ, Inner.inner ℝ (c (TotalSpace.mk' V b 0)).2
        (c (TotalSpace.mk' V b 0)).2 = 0 := by
  dsimp only
  refine ⟨by simp, ?_⟩
  intro b
  simpa using
    ContinuousHermitianMetric.orthonormalizeTrivialization_inner
      (ContinuousHermitianMetric.trivial ℝ ℝ (EuclideanSpace ℝ (Fin 0)))
        (Bundle.Trivial.trivialization ℝ (EuclideanSpace ℝ (Fin 0)))
        (b := b) (by simp) 0 0

end OrthonormalTrivializationExamples
