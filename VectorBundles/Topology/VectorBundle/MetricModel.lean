/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.PositiveForm
public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# A compatible metric on a finite-dimensional model

`Bundle.HermitianMetric.ofFiniteDimensional` equips an arbitrary finite-dimensional normed
space over an `RCLike` field with a positive-definite continuous Hermitian form. It does not
require the given norm to come from an inner product, and does not replace any existing
instances on the space. The form is packaged as a metric on the trivial bundle over a point.
`Bundle.RiemannianMetric.ofFiniteDimensional` is its real specialization.

The construction pulls back the Euclidean inner product along
`ContinuousLinearEquiv.toEuclidean`, a version of Mathlib's `toEuclidean` over complete
nontrivially normed fields.
The bounded unit sublevel follows from the finite-dimensional positive-form bound in
`InnerProductSpace.Core.isVonNBounded_unit_sublevel`, for the original topology and norm.

## References

* Yury Kudryashov, Mathlib's `Analysis.InnerProductSpace.EuclideanDist`, for `toEuclidean`.
* Mathlib's `ContinuousLinearEquiv.ofFinrankEq`, continuous sesquilinear composition,
  and `InnerProductSpace.Core` constructions.
-/

@[expose] public section

namespace ContinuousLinearEquiv

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  (F : Type*) [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A continuous linear equivalence from a finite-dimensional Hausdorff topological vector space
over a complete nontrivially normed field to the Euclidean space of the same dimension.
Over `ℝ`, this is Mathlib's `toEuclidean`. -/
noncomputable def toEuclidean : F ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F)) :=
  ofFinrankEq ((WithLp.linearEquiv 2 𝕜 (Fin (Module.finrank 𝕜 F) → 𝕜)).finrank_eq.trans
    (Module.finrank_fin_fun 𝕜)).symm

/-- The real Euclidean equivalence agrees with Mathlib's construction. -/
@[simp] theorem toEuclidean_real (F : Type*) [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [T2Space F] [Module ℝ F] [ContinuousSMul ℝ F]
    [FiniteDimensional ℝ F] : toEuclidean ℝ F = _root_.toEuclidean (E := F) := rfl

end ContinuousLinearEquiv

namespace Bundle.HermitianMetric

open ContinuousLinearEquiv (toEuclidean)

variable (𝕜 : Type*) [RCLike 𝕜]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A positive-definite continuous Hermitian form on a finite-dimensional normed space,
compatible with its existing topology. It is expressed as a metric on the trivial bundle over a
point, without changing the norm on the model space. -/
noncomputable def ofFiniteDimensional : HermitianMetric 𝕜 (Bundle.Trivial Unit F) where
  inner _ := (innerSL 𝕜).bilinearComp (toEuclidean 𝕜 F).toContinuousLinearMap
    (toEuclidean 𝕜 F).toContinuousLinearMap
  symm _ v w := inner_conj_symm (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F w)
  pos _ v hv := by
    change 0 < RCLike.re (Inner.inner 𝕜 (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F v))
    exact re_inner_self_pos.mpr (by
      simpa only [map_zero] using (toEuclidean 𝕜 F).injective.ne hv)
  continuousAt _ := by fun_prop
  isVonNBounded _ := by
    let c : InnerProductSpace.Core 𝕜 F :=
      { inner v w := Inner.inner 𝕜 (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F w)
        conj_inner_symm v w := inner_conj_symm _ _
        re_inner_nonneg v := inner_self_nonneg
        add_left v w x := by simp only [map_add, inner_add_left]
        smul_left v w r := by simp only [map_smul, inner_smul_left]
        definite v hv := (toEuclidean 𝕜 F).injective (by
          simpa only [map_zero] using inner_self_eq_zero.mp hv) }
    exact c.isVonNBounded_unit_sublevel

/-- The model metric is the pullback of the Euclidean inner product. -/
@[simp] theorem ofFiniteDimensional_inner_apply (v w : F) :
    (ofFiniteDimensional 𝕜 F).inner () v w =
      Inner.inner 𝕜 (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F w) := rfl

/-- The quadratic form of the model metric is the squared Euclidean norm, as a scalar. -/
theorem ofFiniteDimensional_inner_self (v : F) :
    (ofFiniteDimensional 𝕜 F).inner () v v = (‖toEuclidean 𝕜 F v‖ : 𝕜) ^ 2 := by
  rw [ofFiniteDimensional_inner_apply, inner_self_eq_norm_sq_to_K]

/-- The real part of the model's quadratic form is the squared Euclidean norm. -/
theorem ofFiniteDimensional_re_inner_self (v : F) :
    RCLike.re ((ofFiniteDimensional 𝕜 F).inner () v v) = ‖toEuclidean 𝕜 F v‖ ^ 2 := by
  rw [ofFiniteDimensional_inner_apply, inner_self_eq_norm_sq]

end Bundle.HermitianMetric

namespace Bundle.RiemannianMetric

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A positive symmetric continuous bilinear form on a finite-dimensional real normed space,
compatible with the existing topology. It is expressed as a metric on the trivial bundle over a
point, without changing the norm on the model space. -/
noncomputable def ofFiniteDimensional : RiemannianMetric (Bundle.Trivial Unit F) :=
  (HermitianMetric.ofFiniteDimensional ℝ F).toRiemannianMetric

/-- The model metric is the pullback of the Euclidean inner product. -/
@[simp] theorem ofFiniteDimensional_inner_apply (v w : F) :
    (ofFiniteDimensional F).inner () v w = Inner.inner ℝ (toEuclidean v) (toEuclidean w) :=
  rfl

/-- The quadratic form of the model metric is the squared Euclidean norm. -/
theorem ofFiniteDimensional_inner_self (v : F) :
    (ofFiniteDimensional F).inner () v v = ‖toEuclidean v‖ ^ 2 :=
  HermitianMetric.ofFiniteDimensional_re_inner_self ℝ F v

end Bundle.RiemannianMetric

/-- The real finite-dimensional model metric is the exact real specialization of the Hermitian
construction. -/
@[simp] theorem Bundle.HermitianMetric.ofFiniteDimensional_toRiemannianMetric
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    (ofFiniteDimensional ℝ F).toRiemannianMetric = RiemannianMetric.ofFiniteDimensional F := rfl
