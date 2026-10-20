/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SigmaCompact.Proper
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order

/-!
# Sigma-compact trivial bundles with compact model

The canonical two-point trivial bundle over the noncompact real line has
sigma-compact total space. The empty-model bundle over the same base shows that
no nonemptiness of the model or surjectivity of the projection is required.
Both examples use Mathlib's original trivial-bundle topologies and structure.
-/

@[expose] public section

open Bundle

/-- The compact two-point model gives a sigma-compact original total space over `ℝ`. -/
example : SigmaCompactSpace (TotalSpace (Fin 2) (Trivial ℝ (Fin 2))) := by
  let : SigmaCompactSpace ℝ := inferInstance
  let : CompactSpace (Fin 2) := Finite.compactSpace
  exact FiberBundle.sigmaCompactSpace_totalSpace (Fin 2) (Trivial ℝ (Fin 2))

/-- The same theorem allows an empty model over a nonempty noncompact base. -/
example : SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  let : SigmaCompactSpace ℝ := inferInstance
  let : CompactSpace Empty := Finite.compactSpace
  exact FiberBundle.sigmaCompactSpace_totalSpace Empty (Trivial ℝ Empty)
