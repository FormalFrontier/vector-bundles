/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.MetricModel
public import VectorBundles.Topology.VectorBundle.TrivialMetric

/-!
# Constant metrics with the original model norm

Finite powers of an arbitrary finite-dimensional normed model acquire constant compatible
metrics over any topological base. The scalar, base and original model have independent
universes. No inner-product structure on the original model norm is assumed.

The ordinary max-norm real plane over a Boolean base has the chosen model pairing in every
fiber, and that pairing is positive on `(1, 0)`. The Boolean topology is arbitrary. Zero powers,
zero-dimensional models and empty bases give boundary cases of the same construction.
-/

@[expose] public section

open Bundle

namespace TrivialMetricExamples

universe uκ uB uF

/-- A constant metric on a finite power with its original supremum norm, over any base. -/
noncomputable def finiteFunctionsMetric (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] (m : ℕ) :
    ContinuousHermitianMetric κ (Fin m → F) (Bundle.Trivial B (Fin m → F)) :=
  ContinuousHermitianMetric.trivialOfHermitianMetric κ B (Fin m → F)
    (HermitianMetric.ofFiniteDimensional κ (Fin m → F))

/-- Every fiber uses exactly the chosen finite-dimensional model form. -/
theorem finiteFunctionsMetric_inner_apply (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] (m : ℕ) (b : B) (v w : Fin m → F) :
    (finiteFunctionsMetric κ B F m).inner b v w =
      (HermitianMetric.ofFiniteDimensional κ (Fin m → F)).inner () v w := by
  exact ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply κ B (Fin m → F)
    (HermitianMetric.ofFiniteDimensional κ (Fin m → F)) b v w

section MaxNorm

-- Use the trivial-bundle structures rather than the fiberwise-product bundle structures.
-- The model remains the ordinary max-norm plane, with its original fiber topology.
attribute [local instance 2000] Bundle.Trivial.topologicalSpace Bundle.Trivial.fiberBundle
  Bundle.Trivial.vectorBundle

/-- A constant compatible metric on the ordinary max-norm plane over any Boolean topology. -/
noncomputable def maxNormMetric [TopologicalSpace Bool] :=
  ContinuousHermitianMetric.trivialOfHermitianMetric ℝ Bool (ℝ × ℝ)
    (HermitianMetric.ofFiniteDimensional ℝ (ℝ × ℝ))

/-- The plane's constant pairing is the chosen model form, not a prescribed coordinate formula. -/
theorem maxNormMetric_inner_apply [TopologicalSpace Bool] (b : Bool) (v w : ℝ × ℝ) :
    maxNormMetric.inner b v w =
      (HermitianMetric.ofFiniteDimensional ℝ (ℝ × ℝ)).inner () v w := by
  exact ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply ℝ Bool (ℝ × ℝ)
    (HermitianMetric.ofFiniteDimensional ℝ (ℝ × ℝ)) b v w

/-- The first coordinate vector has strictly positive diagonal pairing in every fiber. -/
theorem maxNormMetric_pos [TopologicalSpace Bool] (b : Bool) :
    0 < RCLike.re (maxNormMetric.inner b (1, 0) (1, 0)) := by
  rw [maxNormMetric_inner_apply]
  exact (HermitianMetric.ofFiniteDimensional ℝ (ℝ × ℝ)).pos () (1, 0) (by simp)

end MaxNorm

/-- The zero power is allowed, and all of its pairings vanish. -/
theorem finiteFunctionsMetric_zero_inner (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] (b : B) (v w : Fin 0 → F) :
    (finiteFunctionsMetric κ B F 0).inner b v w = 0 := by
  have hv : v = 0 := Subsingleton.elim _ _
  rw [finiteFunctionsMetric_inner_apply, hv, map_zero, zero_apply]

/-- A zero-dimensional original model gives zero pairings in every finite power. -/
theorem finiteFunctionsMetric_inner_of_finrank_eq_zero (κ : Type uκ) [RCLike κ]
    (B : Type uB) [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] (hF : Module.finrank κ F = 0)
    (m : ℕ) (b : B) (v w : Fin m → F) :
    (finiteFunctionsMetric κ B F m).inner b v w = 0 := by
  have hss : Subsingleton F := Module.finrank_zero_iff.mp hF
  have hv : v = 0 := funext fun i ↦ hss.elim (v i) 0
  rw [finiteFunctionsMetric_inner_apply, hv, map_zero, zero_apply]

/-- Constant metrics also exist over an empty base, with no choice of a base point. -/
noncomputable def emptyBaseMetric (κ : Type uκ) [RCLike κ]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] (m : ℕ) :
    ContinuousHermitianMetric κ (Fin m → F) (Bundle.Trivial Empty (Fin m → F)) :=
  finiteFunctionsMetric κ Empty F m

end TrivialMetricExamples
