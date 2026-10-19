/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.LocallyCompact

/-!
# Local compactness of the real plane bundle

The trivial real-line bundle over the real line is homeomorphic to the usual real plane
via `Bundle.Trivial.homeomorphProd ℝ ℝ`.

The example uses Mathlib's existing `FiberBundle.chartedSpace'` and
`ChartedSpace.locallyCompactSpace` to obtain local compactness of the total space from the
locally compact product `ℝ × ℝ`. From that same total-space local compactness, it recovers
the model at the origin and uses the equivalence to recover local compactness of the base.
-/

open Bundle

example :
    LocallyCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) ∧
      LocallyCompactSpace ℝ ∧ LocallyCompactSpace ℝ := by
  have htotal : LocallyCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    ChartedSpace.locallyCompactSpace (ℝ × ℝ) (TotalSpace ℝ (Trivial ℝ ℝ))
  let : LocallyCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := htotal
  have hmodel := FiberBundle.locallyCompactSpace_model ℝ (Trivial ℝ ℝ) (0 : ℝ)
  have hbase :=
    ((FiberBundle.locallyCompactSpace_totalSpace_iff ℝ (Trivial ℝ ℝ)).mp htotal).1
  exact ⟨htotal, hbase, hmodel⟩
