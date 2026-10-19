/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.MetricExistence
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Examples of Hermitian fiber metrics

The standard metric on a trivial complex line is constructed directly, independently of the
finite-dimensional existence construction. Its values check the conjugate-linear/linear
convention. The existence construction also applies with the raw product norm on `ℂ × ℂ`,
which cannot be induced by an inner product. A zero-dimensional model gives a boundary example.
The standard metric constructor follows Mathlib's trivial Riemannian-bundle construction by
Sébastien Gouëzel.
-/

@[expose] public section

open Bundle
open scoped ComplexConjugate

namespace HermitianMetricExamples

/-- The standard metric on the trivial complex line over `ℝ`, proved without the existence
construction. -/
noncomputable def complexLine :
    Bundle.ContinuousHermitianMetric ℂ ℂ (Bundle.Trivial ℝ ℂ) :=
  Bundle.ContinuousHermitianMetric.trivial ℂ ℝ ℂ

private theorem complexLine_inner_one_I : complexLine.inner 0 1 Complex.I = Complex.I := by
  simp [complexLine]

private theorem complexLine_inner_I_one : complexLine.inner 0 Complex.I 1 = -Complex.I := by
  simp [complexLine]

/-- A real specialization can be used directly as Mathlib continuous Riemannian metric data. -/
noncomputable def realLine : Bundle.ContinuousRiemannianMetric ℝ (Bundle.Trivial ℝ ℝ) :=
  (Bundle.ContinuousHermitianMetric.trivial ℝ ℝ ℝ).toRiemannianMetric

private theorem realLine_inner_three_four : realLine.inner 2 3 4 = 12 := by
  norm_num [realLine]

/-- The existence construction on the trivial complex line gives a positive Hermitian form Core
on each fiber. This example depends on that construction. -/
@[reducible] noncomputable def complexLineCore (b : ℝ) : InnerProductSpace.Core ℂ ℂ :=
  (VectorBundle.continuousHermitianMetric ℂ ℂ (Bundle.Trivial ℝ ℂ)).toHermitianMetric.toCore b

private theorem core_inner_one_ne_zero (b : ℝ) : (complexLineCore b).inner (1 : ℂ) 1 ≠ 0 := by
  exact ((VectorBundle.continuousHermitianMetric ℂ ℂ (Bundle.Trivial ℝ ℂ)).toHermitianMetric
    |>.inner_self_eq_zero_iff b 1).not.mpr one_ne_zero

/-- A continuous metric with the raw sup-norm product as its model. In particular, the existence
construction does not require the model norm to be induced by an inner product. -/
noncomputable def productMetric :
    Bundle.ContinuousHermitianMetric ℂ (ℂ × ℂ) (Bundle.Trivial ℝ (ℂ × ℂ)) :=
  VectorBundle.continuousHermitianMetric ℂ (ℂ × ℂ) (Bundle.Trivial ℝ (ℂ × ℂ))

/-- The standard norm on the raw product is not an inner-product norm. -/
theorem product_not_innerProductSpace : IsEmpty (InnerProductSpace ℂ (ℂ × ℂ)) := by
  refine ⟨fun h ↦ ?_⟩
  let := h
  have hpar := parallelogram_law_with_norm ℂ ((1, 0) : ℂ × ℂ) (0, 1)
  norm_num [Prod.norm_def] at hpar

private theorem productMetric_inner_ne_zero : productMetric.inner 0 (1, 0) (1, 0) ≠ 0 := by
  exact (productMetric.toHermitianMetric.inner_self_eq_zero_iff 0 (1, 0)).not.mpr (by simp)

/-- The existence construction also applies to zero-dimensional complex bundles. -/
noncomputable def rankZero : Bundle.ContinuousHermitianMetric ℂ (EuclideanSpace ℂ (Fin 0))
    (Bundle.Trivial ℝ (EuclideanSpace ℂ (Fin 0))) :=
  VectorBundle.continuousHermitianMetric ℂ (EuclideanSpace ℂ (Fin 0))
    (Bundle.Trivial ℝ (EuclideanSpace ℂ (Fin 0)))

private theorem fin0_inner (b : ℝ) (v w : EuclideanSpace ℂ (Fin 0)) : rankZero.inner b v w = 0 := by
  have : v = 0 := Subsingleton.elim _ _
  simp [this]

end HermitianMetricExamples
