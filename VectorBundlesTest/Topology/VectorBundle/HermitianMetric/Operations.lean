/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric.Operations
public import VectorBundles.Topology.VectorBundle.MetricModel
public import VectorBundles.Topology.VectorBundle.TrivialMetric
public import VectorBundles.Topology.VectorBundle.WeightedForm

/-!
# Varying metrics on the original real and complex planes

For either `κ = ℝ` or `κ = ℂ`, the model `κ × κ` keeps its stock supremum norm.
A compatible model form is chosen by `Bundle.HermitianMetric.ofFiniteDimensional` and
extended constantly over the real line. Adding this metric to its positive rescaling
by `1 + t²` gives the pairing `(2 + t²)` times the chosen model pairing.
The real diagonal on `(1, 0)` increases strictly between `t = 0` and `t = 1`.

No inner-product structure on the stock plane norm is assumed, and no coordinate formula
for the chosen model form or equality with the stock norm is asserted. Constant vector
sections are continuous through the original trivial-bundle homeomorphism.

## References

* The compatible model and constant-extension constructions in `MetricModel` and
  `TrivialMetric`.
* The canonical-chart identity in `WeightedForm` and Mathlib's trivial-bundle homeomorphism.
-/

open Bundle

namespace HermitianMetricOperationsExamples

universe uκ

-- Select the original trivial-bundle structures, not the fiberwise-product structures.
attribute [local instance 2000] Bundle.Trivial.topologicalSpace Bundle.Trivial.fiberBundle
  Bundle.Trivial.vectorBundle

private noncomputable def modelMetric (κ : Type uκ) [RCLike κ] :
    HermitianMetric κ (Bundle.Trivial Unit (κ × κ)) :=
  HermitianMetric.ofFiniteDimensional κ (κ × κ)

private noncomputable def constantMetric (κ : Type uκ) [RCLike κ] :
    ContinuousHermitianMetric κ (κ × κ) (Bundle.Trivial ℝ (κ × κ)) :=
  ContinuousHermitianMetric.trivialOfHermitianMetric κ ℝ (κ × κ) (modelMetric κ)

private def weight : C(ℝ, ℝ) :=
  ⟨fun t ↦ 1 + t ^ 2, continuous_const.add (continuous_id.pow 2)⟩

private theorem weight_pos (t : ℝ) : 0 < weight t := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg t)

/-- On the stock plane over the real line, add the constant compatible metric to its
rescaling by the continuous positive function `1 + t²`. -/
noncomputable def planeMetric (κ : Type uκ) [RCLike κ] :
    ContinuousHermitianMetric κ (κ × κ) (Bundle.Trivial ℝ (κ × κ)) :=
  (constantMetric κ).add ((constantMetric κ).rescale weight weight_pos)

/-- The combined metric has coefficient `2 + t²` relative to the chosen model form. -/
theorem planeMetric_inner_apply (κ : Type uκ) [RCLike κ] (t : ℝ) (v w : κ × κ) :
    (planeMetric κ).inner t v w =
      ((2 + t ^ 2 : ℝ) : κ) * (HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () v w := by
  simp only [planeMetric, ContinuousHermitianMetric.add_inner_apply,
    ContinuousHermitianMetric.rescale_inner_apply, constantMetric,
    ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply, modelMetric, weight,
    ContinuousMap.coe_mk, RCLike.ofReal_add, RCLike.ofReal_one, RCLike.ofReal_ofNat,
    add_mul, one_mul, two_mul, add_assoc]

/-- On the global trivial chart, the rescaled constant metric is the weighted model form.
This uses the chart identity without changing its topological-support continuity theorem. -/
theorem rescale_constant_inner_eq_weightedForm (κ : Type uκ) [RCLike κ] (t : ℝ) :
    ((constantMetric κ).rescale weight weight_pos).inner t =
      (Bundle.Trivial.trivialization ℝ (κ × κ)).weightedSesquilinearForm
        ((modelMetric κ).inner ()) (fun s ↦ (weight s : κ)) t := by
  rw [Bundle.Trivialization.weightedSesquilinearForm_trivialization]
  apply DFunLike.ext _ _
  intro v
  apply DFunLike.ext _ _
  intro w
  simp only [ContinuousHermitianMetric.rescale_inner_apply, constantMetric,
    ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply, smul_apply, smul_eq_mul]

/-- The first coordinate vector has strictly positive diagonal in the chosen model form. -/
theorem coordinate_pos (κ : Type uκ) [RCLike κ] :
    0 < RCLike.re ((HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () (1, 0) (1, 0)) := by
  exact (HermitianMetric.ofFiniteDimensional κ (κ × κ)).pos () (1, 0) (by simp)

/-- Every constant vector section is continuous for the original trivial total topology. -/
theorem continuous_constant_section (κ : Type uκ) [RCLike κ] (v : κ × κ) :
    Continuous (fun t : ℝ ↦ TotalSpace.mk' (κ × κ) (E := Bundle.Trivial ℝ (κ × κ)) t v) := by
  exact (Bundle.Trivial.homeomorphProd ℝ (κ × κ)).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

/-- Pairing any two constant vector sections is continuous, using metric evaluation. -/
theorem continuous_planeMetric_inner (κ : Type uκ) [RCLike κ] (v w : κ × κ) :
    Continuous (fun t : ℝ ↦ (planeMetric κ).inner t v w) :=
  (planeMetric κ).continuous_inner (continuous_constant_section κ v)
    (continuous_constant_section κ w)

/-- On a nonzero coordinate vector the real diagonal is `2Q` at zero and `3Q` at one,
where `Q` is strictly positive, so the metric genuinely varies. -/
theorem planeMetric_coordinate_variation (κ : Type uκ) [RCLike κ] :
    let Q := RCLike.re ((HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () (1, 0) (1, 0))
    0 < Q ∧
      RCLike.re ((planeMetric κ).inner 0 (1, 0) (1, 0)) = 2 * Q ∧
      RCLike.re ((planeMetric κ).inner 1 (1, 0) (1, 0)) = 3 * Q ∧
      RCLike.re ((planeMetric κ).inner 0 (1, 0) (1, 0)) <
        RCLike.re ((planeMetric κ).inner 1 (1, 0) (1, 0)) := by
  dsimp only
  have h0 := congrArg (RCLike.re (K := κ))
    (planeMetric_inner_apply κ 0 (1, 0) (1, 0))
  have h1 := congrArg (RCLike.re (K := κ))
    (planeMetric_inner_apply κ 1 (1, 0) (1, 0))
  norm_num only [RCLike.re_ofReal_mul] at h0 h1
  refine ⟨coordinate_pos κ, h0, h1, ?_⟩
  rw [h0, h1]
  exact mul_lt_mul_of_pos_right (by norm_num) (coordinate_pos κ)

-- The same construction genuinely varies on the stock real plane.
example :
    RCLike.re ((planeMetric ℝ).inner 0 (1, 0) (1, 0)) <
      RCLike.re ((planeMetric ℝ).inner 1 (1, 0) (1, 0)) := by
  exact (planeMetric_coordinate_variation ℝ).2.2.2

-- The same construction genuinely varies on the stock complex plane.
example :
    RCLike.re ((planeMetric ℂ).inner 0 (1, 0) (1, 0)) <
      RCLike.re ((planeMetric ℂ).inner 1 (1, 0) (1, 0)) := by
  exact (planeMetric_coordinate_variation ℂ).2.2.2

end HermitianMetricOperationsExamples
