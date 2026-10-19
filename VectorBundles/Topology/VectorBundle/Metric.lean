/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.MetricExistence

/-!
# Continuous real metrics on finite-dimensional vector bundles

A finite-dimensional real vector bundle over a paracompact Hausdorff space admits a
continuous positive-definite fiber metric, compatible with its existing fiber topologies.
The model's given norm need not be induced by an inner product.

This is the real specialization of the Hermitian metric construction in `MetricExistence`.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Proposition 1.2.
* Mathlib's real Riemannian-bundle and partition-of-unity constructions.

## Limitations

Continuous orthogonal-complement subbundles are separate constructions.
-/

@[expose] public section

open Bundle

namespace VectorBundle

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- A continuous real fiber metric on a finite-dimensional vector bundle over a paracompact
Hausdorff base. This is the real assertion of Hatcher's Proposition 1.2. The induced norms
are compatible with the pre-existing fiber topologies, but need not equal any given fiber norm.

The choice uses local trivializations and a subordinate partition of unity. -/
noncomputable def continuousRiemannianMetric
    [T2Space B] [ParacompactSpace B] [FiniteDimensional ℝ F] :
    Bundle.ContinuousRiemannianMetric F E :=
  (continuousHermitianMetric ℝ F E).toRiemannianMetric

/-- The real specialization of the Hermitian construction agrees with the Riemannian metric
constructor. -/
@[simp] theorem continuousHermitianMetric_toRiemannianMetric
    [T2Space B] [ParacompactSpace B] [FiniteDimensional ℝ F] :
    (continuousHermitianMetric ℝ F E).toRiemannianMetric = continuousRiemannianMetric F E := rfl

/-- A finite-dimensional real vector bundle over a paracompact Hausdorff base admits a
continuous Riemannian metric. -/
theorem nonempty_continuousRiemannianMetric
    [T2Space B] [ParacompactSpace B] [FiniteDimensional ℝ F] :
    Nonempty (Bundle.ContinuousRiemannianMetric F E) :=
  ⟨continuousRiemannianMetric F E⟩

end VectorBundle
