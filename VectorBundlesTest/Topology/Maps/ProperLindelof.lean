/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Lindelöf preimages under a compact-fiber projection

The usual projection from `ℝ × Fin 2` to `ℝ` is proper. Its preimage of the noncompact
half-line `[0, ∞)` is Lindelöf, beyond the scope of compact-preimage transfer alone.
The empty-set example uses the same projection and the original product topology.
-/

@[expose] public section

open Set

example : IsLindelof ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' Ici 0) := by
  have hf : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hs : IsLindelof (Ici (0 : ℝ)) := isClosed_Ici.isLindelof
  exact hf.isLindelof_preimage hs

example : IsLindelof ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' (∅ : Set ℝ)) := by
  exact (isProperMap_fst_of_compactSpace (X := ℝ) (Y := Fin 2)).isLindelof_preimage
    (isLindelof_empty : IsLindelof (∅ : Set ℝ))
