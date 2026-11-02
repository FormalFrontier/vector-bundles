/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite scalar-source coordinates over a complete field

The finite scalar-source equivalence `ContinuousLinearEquiv.piRingOfFinite` agrees with
Mathlib's `ContinuousLinearEquiv.piRing` over a complete nontrivially normed field and a normed
target. Both equivalences use the given norms, scalar actions and topologies. No completeness
or finite-dimensionality assumption on the target is needed.

## References

The comparison is with Mathlib's `ContinuousLinearEquiv.piRing` from
`Mathlib.Analysis.Normed.Module.FiniteDimension`.
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
