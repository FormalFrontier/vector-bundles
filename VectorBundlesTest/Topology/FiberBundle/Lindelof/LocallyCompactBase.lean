/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Lindelof.LocallyCompactBase
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

/-!
# Direct clients of Lindelöf bundles over locally compact bases

These four clients retain Mathlib's original trivial-bundle topologies and
data. The real cylinder over `[0, 1]` uses the chart preimage theorem with
`isCompact_Icc.isSigmaCompact`. The real plane, the real-model bundle over
the empty base, and the empty-model bundle over the real base invoke the
locally compact Lindelöf-base theorem directly.
-/

@[expose] public section

open Bundle

example : IsLindelof ((π ℝ (Trivial ℝ ℝ)) ⁻¹' Set.Icc (0 : ℝ) 1) := by
  exact (Trivial.trivialization ℝ ℝ).isLindelof_preimage
    (Set.Icc (0 : ℝ) 1) isCompact_Icc.isSigmaCompact (Set.subset_univ _)

example : LindelofSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := by
  exact FiberBundle.lindelofSpace_of_locallyCompactSpace_base ℝ (Trivial ℝ ℝ)

example : LindelofSpace (TotalSpace ℝ (Trivial Empty ℝ)) := by
  exact FiberBundle.lindelofSpace_of_locallyCompactSpace_base ℝ (Trivial Empty ℝ)

example : LindelofSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact FiberBundle.lindelofSpace_of_locallyCompactSpace_base Empty (Trivial ℝ Empty)
