/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric

/-!
# Constant Hermitian metrics on trivial bundles

`Bundle.ContinuousHermitianMetric.trivialOfHermitianMetric` extends a compatible Hermitian
form on a normed model, packaged as a fiber metric over a point, to a constant continuous
metric on the trivial bundle over any topological base. Finite dimensionality is not required
when the compatible model form is supplied.

The characteristic pairing is the supplied model pairing. The model keeps its original norm
and topology; the norm induced by the metric need not equal that norm. The comparison with
`Bundle.ContinuousHermitianMetric.trivial` uses the original inner-product structure when one
is already given, without replacing that constructor or any instances.

## References

* Sébastien Gouëzel, Mathlib's `Topology.VectorBundle.Riemannian`, for the constant metric on
  a trivial bundle with an inner-product model.
* Heather Macbeth and Floris van Doorn, Mathlib's `Topology.VectorBundle.Hom`, for the
  continuous semilinear Hom-bundle topology.
-/

@[expose] public section

namespace Bundle.ContinuousHermitianMetric

universe uκ uB uH

/-- Extend a compatible Hermitian model form constantly over a topological base.
The original norm and topologies are retained, with the usual trivial-bundle structures.
No finite-dimensionality or separation hypothesis is required. -/
def trivialOfHermitianMetric (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace κ H]
    (gModel : HermitianMetric κ (Bundle.Trivial Unit H)) :
    ContinuousHermitianMetric κ H (Bundle.Trivial B H) := by
  refine
    { inner := fun _ ↦ gModel.inner ()
      symm := fun _ ↦ gModel.symm ()
      pos := fun _ ↦ gModel.pos ()
      isVonNBounded := fun _ ↦ gModel.isVonNBounded ()
      continuous := ?_ }
  rw [continuous_iff_continuousAt]
  intro b
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! continuousAt_const (y := gModel.inner ())
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]

/-- The pairing of the constant metric is exactly the supplied model pairing. -/
@[simp]
theorem trivialOfHermitianMetric_inner_apply (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace κ H]
    (gModel : HermitianMetric κ (Bundle.Trivial Unit H)) (b : B) (v w : H) :
    (trivialOfHermitianMetric κ B H gModel).inner b v w = gModel.inner () v w := by
  rfl

/-- For an inner-product model, constant extension recovers the standard trivial metric. -/
theorem trivial_eq_trivialOfHermitianMetric (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace κ H] :
    trivial κ B H =
      trivialOfHermitianMetric κ B H ((trivial κ Unit H).toHermitianMetric) := by
  refine Bundle.ContinuousHermitianMetric.ext fun b v w ↦ ?_
  simp only [trivialOfHermitianMetric_inner_apply, toHermitianMetric_inner, trivial_inner]

end Bundle.ContinuousHermitianMetric
