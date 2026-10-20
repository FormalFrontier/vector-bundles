/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.WithTopology

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

/-- The visible part of the whole target of the proper real sum inclusion is Lindelöf. -/
theorem isLindelof_real_inl_univ_inter_range :
    IsLindelof
      ((Set.univ : Set (ℝ ⊕ WithTopology ℝ ⊥)) ∩
        Set.range (Sum.inl : ℝ → ℝ ⊕ WithTopology ℝ ⊥)) := by
  exact (IsProperMap.isLindelof_preimage_iff
    (f := (Sum.inl : ℝ → ℝ ⊕ WithTopology ℝ ⊥))
    Topology.IsClosedEmbedding.inl.isProperMap
    (Set.univ : Set (ℝ ⊕ WithTopology ℝ ⊥))).mp (by
      simpa only [Set.preimage_univ] using
        (isLindelof_univ_iff.mpr (inferInstance : LindelofSpace ℝ)))

/-- The same proper, non-surjective inclusion handles the empty target-set boundary. -/
theorem isLindelof_real_inl_preimage_empty :
    IsLindelof
      ((Sum.inl : ℝ → ℝ ⊕ WithTopology ℝ ⊥) ⁻¹'
        (∅ : Set (ℝ ⊕ WithTopology ℝ ⊥))) := by
  exact (IsProperMap.isLindelof_preimage_iff
    (f := (Sum.inl : ℝ → ℝ ⊕ WithTopology ℝ ⊥))
    Topology.IsClosedEmbedding.inl.isProperMap
    (∅ : Set (ℝ ⊕ WithTopology ℝ ⊥))).mpr (by
      simpa only [Set.empty_inter] using
        (isLindelof_empty : IsLindelof (∅ : Set (ℝ ⊕ WithTopology ℝ ⊥))))
