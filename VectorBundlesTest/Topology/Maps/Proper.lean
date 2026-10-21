/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.Maps.Proper
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Compact preimages and ranges of proper maps

The two-sheeted real projection has compact inverse image of the closed unit interval.
The closed-unit-interval inclusion has compact range and compact inverse image of the
whole real line, although the target is not compact. This nonsurjective example shows
why the range intersection in the compact-preimage characterization is necessary.
All maps carry their usual given topologies.
-/

@[expose] public section

open Set

example : IsCompact ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' Icc 0 1) := by
  have hf : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hs : Icc (0 : ℝ) 1 ⊆ range (Prod.fst : ℝ × Fin 2 → ℝ) := by
    intro x _
    exact ⟨(x, 0), rfl⟩
  exact (hf.isCompact_preimage_iff_of_subset_range (Icc 0 1) hs).mpr isCompact_Icc

example :
    IsProperMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
      ¬ Function.Surjective (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
      IsCompact ((Subtype.val : Icc (0 : ℝ) 1 → ℝ) ⁻¹' (univ : Set ℝ)) ∧
      IsCompact (range (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ∧
      ¬ IsCompact (univ : Set ℝ) := by
  have hf : IsProperMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
    isClosed_Icc.isProperMap_subtypeVal
  have hr : IsCompact (range (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    hf.compactSpace_iff_isCompact_range.mp inferInstance
  refine ⟨hf, ?_, ?_, hr, noncompact_univ ℝ⟩
  · intro hsurj
    have hrange : range (Subtype.val : Icc (0 : ℝ) 1 → ℝ) = univ := by
      ext y
      exact ⟨fun _ ↦ mem_univ y, fun _ ↦ hsurj y⟩
    exact noncompact_univ ℝ (hrange ▸ hr)
  · exact (hf.isCompact_preimage_iff (univ : Set ℝ)).mpr (by
      simpa only [univ_inter] using hr)
