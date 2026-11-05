/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.ShrinkingLemma
public import VectorBundles.Topology.ContinuousMap.Cutoff

/-!
# Finite real weights on normal spaces

Finite subordinate partitions of unity on normal spaces provide continuous real weights
with closed supports subordinate to a finite open cover.
-/

@[expose] public section

open Set Function

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- A closed subset of an open set in a normal space admits a continuous real
cutoff, equal to one on the closed set, with values in `[0, 1]` and closed support
contained in the open set. -/
theorem IsClosed.exists_continuous_one_tsupport_subset [NormalSpace X]
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      EqOn g 1 C ∧ tsupport g ⊆ U := by
  obtain ⟨g, hgone, hgbounds, hgsupport⟩ :=
    ContinuousMap.exists_one_on_closed_with_closure_subset hC hU hCU
  exact ⟨g, g.continuous, hgbounds, hgone, hgsupport⟩

namespace PartitionOfUnity

/-- The component functions of a finite subordinate partition of unity are continuous
nonnegative real weights, with sum at most one everywhere, sum equal to one on the
specified set, and closed supports in the corresponding sets. -/
theorem finite_continuous_weights [Fintype ι] {s : Set X}
    (f : PartitionOfUnity ι X s) {U : ι → Set X} (hsub : f.IsSubordinate U) :
    (∀ i, Continuous (fun x => f i x)) ∧
      (∀ i x, 0 ≤ f i x) ∧
      (∀ x, ∑ i, f i x ≤ 1) ∧
      (∀ x ∈ s, ∑ i, f i x = 1) ∧
      (∀ i, tsupport (fun x => f i x) ⊆ U i) := by
  refine ⟨?_, f.nonneg, ?_, ?_, ?_⟩
  · intro i
    simpa only [smul_eq_mul, mul_one] using
      (f.continuous_smul (g := fun _ : X => (1 : ℝ)) (i := i)
        fun _ _ => continuousAt_const)
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using f.sum_le_one x
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one hx
  · intro i
    exact hsub i

end PartitionOfUnity

/-- A finite open cover of a closed subset of a normal space admits nonnegative
continuous real weights with closed supports in the corresponding open sets.
Their sum is at most one everywhere and equals one on the closed subset. -/
theorem IsClosed.exists_finite_continuous_partition_of_unity [Fintype ι] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ w : ι → X → ℝ,
      (∀ i, Continuous (w i)) ∧
      (∀ i x, 0 ≤ w i x) ∧
      (∀ x, ∑ i, w i x ≤ 1) ∧
      (∀ x ∈ s, ∑ i, w i x = 1) ∧
      (∀ i, tsupport (w i) ⊆ U i) := by
  classical
  obtain ⟨f, hsub⟩ :=
    PartitionOfUnity.exists_isSubordinate_of_locallyFinite hs U hU
      (locallyFinite_of_finite U) hcover
  exact ⟨fun i x => f i x, PartitionOfUnity.finite_continuous_weights f hsub⟩
