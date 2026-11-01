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
public import Mathlib.Topology.UrysohnsLemma

/-!
# Finite real weights on normal spaces

Bounded real cutoffs and normalization by the maximum of one and a finite sum
produce continuous weights with closed supports subordinate to a finite open cover.
-/

@[expose] public section

open Set Function

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

private theorem exists_normalized_weights [Fintype ι] {s : Set X}
    (g : ι → X → ℝ) (hg : ∀ i, Continuous (g i))
    (hg₀ : ∀ i x, 0 ≤ g i x) (hgs : ∀ x ∈ s, 1 ≤ ∑ i, g i x) :
    ∃ w : ι → X → ℝ,
      (∀ i, Continuous (w i)) ∧
      (∀ i x, 0 ≤ w i x) ∧
      (∀ x, ∑ i, w i x ≤ 1) ∧
      (∀ x ∈ s, ∑ i, w i x = 1) ∧
      (∀ i x, w i x ≠ 0 ↔ g i x ≠ 0) ∧
      (∀ i, tsupport (w i) ⊆ tsupport (g i)) := by
  classical
  let S : X → ℝ := fun x => ∑ i, g i x
  let D : X → ℝ := fun x => max 1 (S x)
  have hS : Continuous S := continuous_finsetSum _ fun i _ => hg i
  have hD : Continuous D := continuous_const.max hS
  have hDpos (x : X) : 0 < D x :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let w : ι → X → ℝ := fun i x => g i x / D x
  have hw (i : ι) : Continuous (w i) :=
    (hg i).div hD fun x => ne_of_gt (hDpos x)
  have hw₀ (i : ι) (x : X) : 0 ≤ w i x :=
    div_nonneg (hg₀ i x) (le_of_lt (hDpos x))
  have hsum (x : X) : (∑ i, w i x) = S x / D x := by
    change (∑ i, g i x / D x) = (∑ i, g i x) / D x
    simp only [Finset.sum_div]
  have hsum_le (x : X) : (∑ i, w i x) ≤ 1 := by
    rw [hsum x]
    exact (div_le_one₀ (hDpos x)).2 (le_max_right _ _)
  have hsum_eq (x : X) (hx : x ∈ s) : (∑ i, w i x) = 1 := by
    rw [hsum x]
    have hSx : 1 ≤ S x := hgs x hx
    have hDx : D x = S x := max_eq_right hSx
    rw [hDx, div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one hSx))]
  have hcozero (i : ι) (x : X) : w i x ≠ 0 ↔ g i x ≠ 0 := by
    constructor
    · intro h hzero
      apply h
      change g i x / D x = 0
      rw [hzero, zero_div]
    · intro h
      exact div_ne_zero h (ne_of_gt (hDpos x))
  have hsupp (i : ι) : tsupport (w i) ⊆ tsupport (g i) := by
    change tsupport (fun x => g i x / D x) ⊆ tsupport (g i)
    simpa only [div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := g i) (g := fun x => (D x)⁻¹))
  exact ⟨w, hw, hw₀, hsum_le, hsum_eq, hcozero, hsupp⟩

/-- A closed subset of an open set in a normal space admits a continuous real
cutoff, equal to one on the closed set, with values in `[0, 1]` and closed support
contained in the open set. -/
theorem IsClosed.exists_continuous_one_tsupport_subset [NormalSpace X]
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      EqOn g 1 C ∧ tsupport g ⊆ U := by
  classical
  obtain ⟨O, hO, hCO, hOU⟩ := normal_exists_closure_subset hC hU hCU
  have hdisj : Disjoint Oᶜ C :=
    Set.disjoint_left.2 fun _ hxO hxC => hxO (hCO hxC)
  obtain ⟨g, hzero, hone, hrange⟩ :=
    exists_continuous_zero_one_of_isClosed hO.isClosed_compl hC hdisj
  have hcozero : {x | g x ≠ 0} ⊆ O := by
    intro x hx
    by_contra hxO
    exact hx (hzero hxO)
  have hsupp : tsupport (g : X → ℝ) ⊆ closure O := closure_mono hcozero
  exact ⟨g, g.continuous, hrange, hone, hsupp.trans hOU⟩

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
  obtain ⟨V, hsV, _, hVU⟩ :=
    exists_subset_iUnion_closure_subset hs hU (fun _ _ => Set.toFinite _) hcover
  choose g hg hrange hone hsupp using fun i =>
    (isClosed_closure : IsClosed (closure (V i))).exists_continuous_one_tsupport_subset
      (hU i) (hVU i)
  have hsum_ge (x : X) (hx : x ∈ s) : 1 ≤ ∑ i, g i x := by
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hsV hx)
    have hgi : g i x = 1 := hone i (subset_closure hxi)
    have hle : g i x ≤ ∑ j, g j x :=
      Finset.single_le_sum (fun j _ => (hrange j x).1) (Finset.mem_univ i)
    rw [hgi] at hle
    exact hle
  obtain ⟨w, hw, hw₀, hsum_le, hsum_eq, _, hwsupp⟩ :=
    exists_normalized_weights g hg (fun i x => (hrange i x).1) hsum_ge
  exact ⟨w, hw, hw₀, hsum_le, hsum_eq, fun i => (hwsupp i).trans (hsupp i)⟩

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
