/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Metrizable
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Metrizability of the trivial real-line bundle

The trivial real-line bundle over the real line is the real plane, via
`Bundle.Trivial.homeomorphProd ℝ ℝ`. Its topology and bundle structure are Mathlib's
`Bundle.Trivial.topologicalSpace` and `Bundle.Trivial.fiberBundle`.

The first example obtains metrizability of this total space from the base and model,
then uses that total-space metrizability to recover metrizability of the model at the origin.
The second example applies the total-space theorem over the empty base, showing that the
forward direction needs no base point. The model theorem cannot be applied there without
such a point.
-/

@[expose] public section

open Bundle TopologicalSpace

universe uF

example :
    MetrizableSpace (TotalSpace ℝ (Trivial ℝ ℝ)) ∧ MetrizableSpace ℝ := by
  have htotal : MetrizableSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.metrizableSpace_totalSpace ℝ (Trivial ℝ ℝ)
  let : MetrizableSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := htotal
  have hmodel : MetrizableSpace ℝ :=
    FiberBundle.metrizableSpace_model ℝ (Trivial ℝ ℝ) (0 : ℝ)
  exact ⟨htotal, hmodel⟩

example (F : Type uF) [TopologicalSpace F] [MetrizableSpace F] :
    MetrizableSpace (TotalSpace F (Trivial Empty F)) := by
  exact FiberBundle.metrizableSpace_totalSpace F (Trivial Empty F)
