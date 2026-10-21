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
sigma-compact total space. The compact one-point real cylinder also reflects
sigma-compactness to its base. The empty-model bundle over an arbitrary base
needs no sigma-compactness assumption on that base. These examples use Mathlib's
original trivial-bundle topologies and structure.
-/

@[expose] public section

open Bundle

/-- The compact two-point model gives a sigma-compact original total space over `ℝ`. -/
example : SigmaCompactSpace (TotalSpace (Fin 2) (Trivial ℝ (Fin 2))) := by
  let : SigmaCompactSpace ℝ := inferInstance
  let : CompactSpace (Fin 2) := Finite.compactSpace
  exact FiberBundle.sigmaCompactSpace_totalSpace (Fin 2) (Trivial ℝ (Fin 2))

/-- Reflection recovers the base of the compact one-point real cylinder. -/
example : SigmaCompactSpace ℝ := by
  let : CompactSpace PUnit.{1} := Finite.compactSpace
  have h : SigmaCompactSpace (TotalSpace PUnit.{1} (Trivial ℝ PUnit.{1})) :=
    FiberBundle.sigmaCompactSpace_totalSpace PUnit.{1} (Trivial ℝ PUnit.{1})
  rcases (FiberBundle.sigmaCompactSpace_totalSpace_iff_of_compactSpace_model
    PUnit.{1} (Trivial ℝ PUnit.{1})).mp h with hempty | hbase
  · exact (hempty.false PUnit.unit).elim
  · exact hbase

/-- The empty-model alternative needs no sigma-compactness of the original base. -/
example (B : Type*) [TopologicalSpace B] :
    SigmaCompactSpace (TotalSpace Empty (Trivial B Empty)) := by
  let : CompactSpace Empty := Finite.compactSpace
  exact (FiberBundle.sigmaCompactSpace_totalSpace_iff_of_compactSpace_model
    Empty (Trivial B Empty)).mpr (Or.inl inferInstance)
