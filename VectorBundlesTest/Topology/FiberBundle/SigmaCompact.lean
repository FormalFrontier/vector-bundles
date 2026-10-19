/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SigmaCompact
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Sigma-compactness of trivial bundles over the real line

The trivial real-line bundle over the real line is the real plane through
`Bundle.Trivial.homeomorphProd ℝ ℝ`. The first example applies
`FiberBundle.sigmaCompactSpace` to this noncompact total space and uses
`isSigmaCompact_univ` to obtain sigma-compactness of its underlying set.

The second example applies the same instance to the trivial bundle with empty model
over the same real base. No nonempty model is needed. Both examples use Mathlib's
trivial-bundle topologies and `Bundle.Trivial.fiberBundle`.
-/

@[expose] public section

open Bundle

example : IsSigmaCompact (Set.univ : Set (TotalSpace ℝ (Trivial ℝ ℝ))) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.sigmaCompactSpace ℝ (Trivial ℝ ℝ)
  exact isSigmaCompact_univ

example : IsSigmaCompact (Set.univ : Set (TotalSpace Empty (Trivial ℝ Empty))) := by
  let : SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) :=
    FiberBundle.sigmaCompactSpace Empty (Trivial ℝ Empty)
  exact isSigmaCompact_univ
