/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates
public import VectorBundles.Topology.Module.FiniteCoordinates.OperatorNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import VectorBundles.Analysis.Normed.Module.Completion
public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Finite-source coordinates and operator-norm bounds

A finite-dimensional seminormed domain admits a finite-evaluation bound for operator norms,
uniformly over all seminormed targets. The scalar field may be incomplete, and the domain
and target need not be separated or complete. The sample vectors and constant depend only
on the given domain, without requiring its algebraic coordinates to be continuous.
For such a domain, continuity in the original operator-norm topology is equivalent to
continuity of every fixed-vector evaluation for any operator-valued family. These results are
provided by `VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic` and
are also available through this module.

The finite scalar-source equivalence `ContinuousLinearEquiv.piRingOfFinite` also agrees with
Mathlib's `ContinuousLinearEquiv.piRing` over a complete nontrivially normed field and a normed
target. Both equivalences use the given norms, scalar actions and topologies. No completeness
or finite-dimensionality assumption on the target is needed.

## References

The comparison is with Mathlib's `ContinuousLinearEquiv.piRing` from
`Mathlib.Analysis.Normed.Module.FiniteDimension`. The finite-evaluation estimate follows
Formal Frontier Agents, *Operator-norm continuity over an incomplete scalar field*, using
coefficient bounds over the completed field before establishing closedness of finite spans.
-/

@[expose] public section

universe uK uF uι

namespace ContinuousLinearEquiv

/-- Over a complete scalar field and a normed target, finite-source coordinates agree with
Mathlib's continuous linear equivalence at the same scalar field, target and index type. -/
theorem piRingOfFinite_eq_piRing (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] :
    piRingOfFinite K F ι = ContinuousLinearEquiv.piRing (𝕜 := K) (E := F) ι := by
  ext T i
  calc
    piRingOfFinite K F ι T i = T (Pi.single i (1 : K)) :=
      piRingOfFinite_apply K F ι T i
    _ = ContinuousLinearEquiv.piRing (𝕜 := K) (E := F) ι T i := rfl

end ContinuousLinearEquiv

