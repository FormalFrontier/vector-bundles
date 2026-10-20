/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Real.Basic
public import VectorBundles.Topology.FiberBundle.Lindelof.Reflection
import Mathlib.Data.Fintype.Sets
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.WithTopology

/-!
# Lindelöf model reflection for trivial bundles

The real plane supplies a closed-singleton chart example. The two-point indiscrete
base is R₀ but not T₁; it supports both a real model and an empty model. The canonical
Sierpiński base and model show that the chart theorem requires neither to be R₀.
In each case the total space is independently second countable via the stock product
homeomorphism. For the Sierpiński square this is the finite four-point total space.
-/

@[expose] public section

open Bundle

namespace Bundle.Trivial

/-- The real-plane chart reflects Lindelöfness using the closed base singleton `{0}`. -/
theorem lindelofSpace_real_of_realPlane : LindelofSpace ℝ := by
  let : SecondCountableTopology (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    (homeomorphProd ℝ ℝ).secondCountableTopology
  let : LindelofSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := inferInstance
  exact (trivialization ℝ ℝ).lindelofSpace_model_of_isClosed
    (FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ))
    (s := {(0 : ℝ)}) isClosed_singleton ⟨0, rfl⟩
    (by intro x _; exact Set.mem_univ x)

/-- The real model is reflected over the canonical two-point indiscrete base.
Here `⊤` is the indiscrete topology, so this base is R₀ but not T₁. -/
theorem lindelofSpace_real_of_indiscreteTwoPoint : LindelofSpace ℝ := by
  let : R0Space (WithTopology (Fin 2) ⊤) := {
    specializes_symm := ⟨fun {_ _} _ => specializes_iff_nhds.mpr (by
      simp only [IndiscreteTopology.nhds_eq, le_refl])⟩ }
  let : SecondCountableTopology
      (TotalSpace ℝ (Trivial (WithTopology (Fin 2) ⊤) ℝ)) :=
    (homeomorphProd (WithTopology (Fin 2) ⊤) ℝ).secondCountableTopology
  let : LindelofSpace
      (TotalSpace ℝ (Trivial (WithTopology (Fin 2) ⊤) ℝ)) := inferInstance
  exact FiberBundle.lindelofSpace_model ℝ (Trivial (WithTopology (Fin 2) ⊤) ℝ)
    (WithTopology.toTopology ⊤ (0 : Fin 2))

/-- The same two-point indiscrete base also permits an empty model and empty total space. -/
theorem lindelofSpace_empty_of_indiscreteTwoPoint : LindelofSpace Empty := by
  let : R0Space (WithTopology (Fin 2) ⊤) := {
    specializes_symm := ⟨fun {_ _} _ => specializes_iff_nhds.mpr (by
      simp only [IndiscreteTopology.nhds_eq, le_refl])⟩ }
  let : SecondCountableTopology
      (TotalSpace Empty (Trivial (WithTopology (Fin 2) ⊤) Empty)) :=
    (homeomorphProd (WithTopology (Fin 2) ⊤) Empty).secondCountableTopology
  let : LindelofSpace
      (TotalSpace Empty (Trivial (WithTopology (Fin 2) ⊤) Empty)) := inferInstance
  exact FiberBundle.lindelofSpace_model Empty (Trivial (WithTopology (Fin 2) ⊤) Empty)
    (WithTopology.toTopology ⊤ (0 : Fin 2))

/-- The global chart of the four-point Sierpiński square reflects Lindelöfness.
Both the base and model have their canonical non-R₀ Sierpiński topology. -/
theorem lindelofSpace_prop_of_sierpinskiSquare : LindelofSpace Prop := by
  let : SecondCountableTopology (TotalSpace Prop (Trivial Prop Prop)) :=
    (homeomorphProd Prop Prop).secondCountableTopology
  let : LindelofSpace (TotalSpace Prop (Trivial Prop Prop)) := inferInstance
  exact (trivialization Prop Prop).lindelofSpace_model_of_isClosed
    (FiberBundle.continuous_proj Prop (Trivial Prop Prop))
    (s := Set.univ) isClosed_univ ⟨True, Set.mem_univ True⟩
    (by intro x _; exact Set.mem_univ x)

end Bundle.Trivial
