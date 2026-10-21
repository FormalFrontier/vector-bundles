/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.Compactness.CountablyCompact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

/-!
# Countably compact preimages and ranges of proper maps

The two-sheeted real projection has countably compact inverse image of the closed unit
interval. The closed-interval inclusion is proper but not surjective; its countably compact
range gives a countably compact inverse image of the whole real line. These examples use
all three proper-map characterizations with the usual given topologies.
-/

@[expose] public section

open Set

-- A noninjective projection with a nonempty two-point fiber.
example : IsCountablyCompact ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' Icc 0 1) := by
  have hf : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hs : Icc (0 : ℝ) 1 ⊆ range (Prod.fst : ℝ × Fin 2 → ℝ) := by
    intro y _
    exact ⟨(y, 0), rfl⟩
  exact (hf.isCountablyCompact_preimage_iff_of_subset_range (Icc 0 1) hs).2
    isCompact_Icc.isCountablyCompact

-- The range correction applies to a proper inclusion which is not surjective.
example :
    IsCountablyCompact ((Subtype.val : Icc (0 : ℝ) 1 → ℝ) ⁻¹' (univ : Set ℝ)) ∧
      ¬ Function.Surjective (Subtype.val : Icc (0 : ℝ) 1 → ℝ) := by
  have hf : IsProperMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
    isClosed_Icc.isProperMap_subtypeVal
  constructor
  · have hr : IsCountablyCompact (range (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
      hf.countablyCompactSpace_iff_isCountablyCompact_range.1 inferInstance
    exact (hf.isCountablyCompact_preimage_iff univ).2 (by
      simpa only [univ_inter] using hr)
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj 2
    have hle : (2 : ℝ) ≤ 1 := hx ▸ x.property.2
    norm_num at hle
