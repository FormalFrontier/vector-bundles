/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact families of continuous semilinear maps

For a finite-dimensional seminormed domain and a proper seminormed target, a closed family
of continuous semilinear maps is compact if and only if every fixed-vector image is
metrically bounded. The scalar field of the domain may be incomplete, and the isometric
scalar homomorphism need not be surjective.

The space of maps carries its topology of uniform convergence on bounded sets; no operator
metric is required. The target may be nonseparated, so closedness of the family remains an
explicit assumption.
-/

@[expose] public section

universe uK uL uA uG

namespace ContinuousLinearMap

/-- A closed family of continuous semilinear maps from a finite-dimensional seminormed
space to a proper seminormed space is compact exactly when each fixed-vector image is
metrically bounded. The scalar fields may be incomplete and the target need not be separated. -/
theorem isCompact_iff_forall_isBounded_image_apply_of_isClosed
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    [pG : ProperSpace G]
    (s : Set (A →SL[σ] G)) (hs : IsClosed s) :
    IsCompact s ↔
      ∀ v : A, Bornology.IsBounded ((fun T : A →SL[σ] G => T v) '' s) := by
  constructor
  · intro h v
    exact (h.image (continuous_eval_const v)).isBounded
  · intro h
    have ht : TotallyBounded s :=
      (totallyBounded_iff_apply_of_finiteDimensionalₛₗ s).2 fun v =>
        (h v).isCompact_closure.totallyBounded.subset subset_closure
    exact ht.isCompact_of_isClosed hs

end ContinuousLinearMap
