/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Lindelof
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

/-!
# Lindelöf products and trivial bundles over the real line

The standard trivial real bundle admits a singleton cover by its original selected chart.
The empty-model example retains the same nonempty real base and the standard bundle topology.
-/

@[expose] public section

open Set

example (a b : ℝ) : IsLindelof ((univ : Set ℝ) ×ˢ Icc a b) := by
  exact isLindelof_univ.prod_of_isCompact isCompact_Icc

example : IsLindelof ((univ : Set ℝ) ×ˢ (univ : Set ℝ)) := by
  exact isLindelof_univ.prod_of_isSigmaCompact isSigmaCompact_univ

/-- The standard trivial real bundle is Lindelöf using one original selected chart. -/
theorem FiberBundle.lindelofSpace_real_model_from_countable_cover :
    LindelofSpace (Bundle.TotalSpace ℝ (Bundle.Trivial ℝ ℝ)) := by
  refine FiberBundle.lindelofSpace_of_countable_trivializationAt_cover
    (F := ℝ) (E := Bundle.Trivial ℝ ℝ) ({0} : Set ℝ) (countable_singleton 0) ?_ ?_
  · rw [biUnion_singleton,
      Bundle.Trivial.eq_trivialization ℝ ℝ (trivializationAt ℝ (Bundle.Trivial ℝ ℝ) 0)]
    simp
  · intro b _hb
    exact HereditarilyLindelofSpace.isLindelof _

example : LindelofSpace (Bundle.TotalSpace ℝ (Bundle.Trivial ℝ ℝ)) := by
  exact FiberBundle.lindelofSpace_of_hereditarilyLindelof

-- An empty model does not require an empty base.
example : LindelofSpace (Bundle.TotalSpace Empty (Bundle.Trivial ℝ Empty)) := by
  exact FiberBundle.lindelofSpace_of_hereditarilyLindelof
