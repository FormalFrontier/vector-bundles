/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Trivialization.SigmaCompact
public import VectorBundles.Topology.FiberBundle.SigmaCompact.LocallyCompactBase
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Separation.Regular

/-!
# Sigma-compact cylinders and bundles over locally compact bases

The real trivialization gives a sigma-compact cylinder over the compact interval
`[-1, 1]`. The locally compact base theorem gives sigma-compactness of the real-plane
trivial bundle, the real-model bundle over the empty base, and the empty-model bundle
over the real base. All four examples retain Mathlib's original trivial-bundle
topologies and data.

## References

These AI-assisted examples use Mathlib's trivial-bundle and compactness APIs and follow
Formal Frontier's fiber-bundle sigma-compactness approach.
-/

@[expose] public section

open Bundle

example : IsSigmaCompact ((π ℝ (Trivial ℝ ℝ)) ⁻¹' Set.Icc (-1 : ℝ) 1) := by
  have hcylinder :=
    (Trivial.trivialization ℝ ℝ).isSigmaCompact_preimage
      (s := Set.Icc (-1 : ℝ) 1) isCompact_Icc.isSigmaCompact (Set.subset_univ _)
  exact hcylinder

example : IsSigmaCompact (Set.univ : Set (TotalSpace ℝ (Trivial ℝ ℝ))) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.sigmaCompactSpace_of_locallyCompactSpace_base ℝ (Trivial ℝ ℝ)
  exact isSigmaCompact_univ

example : IsSigmaCompact (Set.univ : Set (TotalSpace ℝ (Trivial Empty ℝ))) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial Empty ℝ)) :=
    FiberBundle.sigmaCompactSpace_of_locallyCompactSpace_base ℝ (Trivial Empty ℝ)
  exact isSigmaCompact_univ

example : IsSigmaCompact (Set.univ : Set (TotalSpace Empty (Trivial ℝ Empty))) := by
  let : SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) :=
    FiberBundle.sigmaCompactSpace_of_locallyCompactSpace_base Empty (Trivial ℝ Empty)
  exact isSigmaCompact_univ
