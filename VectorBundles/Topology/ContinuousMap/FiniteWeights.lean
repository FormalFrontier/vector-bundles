/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.UrysohnsLemma
public import VectorBundles.Topology.ShrinkingLemma

/-!
# Finite partitions of unity on normal spaces

A finite open cover of a normal space admits continuous real weights with values in `[0, 1]`,
summing to one, whose closed cozero sets lie in the corresponding cover sets. The family is
indexed by an arbitrary type and vanishes outside the chosen finite index set. Only the sets
at active indices must be open. No compactness, nonemptiness, T1 or Hausdorff assumption is
required in addition to normality.

The construction applies finite normal shrinking to the open cover, uses Urysohn's lemma to
obtain bumps equal to one on the resulting closed cover, and divides them by their positive
sum. The main result is `ContinuousMap.exists_finite_weights`.

## References

- Urysohn's lemma, as formalized by Yury Kudryashov in Mathlib's
  `Mathlib.Topology.UrysohnsLemma`.
- The finite normal shrinking lemma, `Set.Finite.exists_open_cover_shrinking`.
- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), printed p. 20
  (PDF p. 24), motivates finite subordinate weights in bundle constructions.
-/

@[expose] public section

open Set
open scoped BigOperators

universe u v

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X] [NormalSpace X]

/-- A continuous bump equal to one on a closed set, with its closed cozero set in a given
open neighborhood. -/
private theorem exists_one_on_closed_with_closure_subset {K U : Set X}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : C(X, ℝ), EqOn g 1 K ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      closure {x | g x ≠ 0} ⊆ U := by
  classical
  obtain ⟨W, hW, hKW, hWU⟩ := normal_exists_closure_subset hK hU hKU
  have hdisj : Disjoint (Wᶜ) K :=
    Set.disjoint_left.mpr fun x hxW hxK => hxW (hKW hxK)
  obtain ⟨g, hgzero, hgone, hgbounds⟩ :=
    exists_continuous_zero_one_of_isClosed hW.isClosed_compl hK hdisj
  refine ⟨g, hgone, hgbounds, (closure_mono ?_).trans hWU⟩
  intro x hx
  by_contra hxW
  exact hx (hgzero hxW)

/-- A prescribed finite closed cover inside an open family gives continuous weights with
subordinate closed cozero sets, extended by zero at all inactive indices. -/
private theorem exists_finite_weights_of_closed_cover {J : Type v}
    (s : Finset J) (U K : J → Set X)
    (hU : ∀ i ∈ s, IsOpen (U i)) (hK : ∀ i ∈ s, IsClosed (K i))
    (hKU : ∀ i ∈ s, K i ⊆ U i) (hcover : ∀ x, ∃ i ∈ s, x ∈ K i) :
    ∃ w : J → C(X, ℝ),
      (∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) ∧
      (∀ i, i ∉ s → w i = 0) ∧
      (∀ x, ∑ i ∈ s, w i x = 1) ∧
      ∀ i, closure {x | w i x ≠ 0} ⊆ U i := by
  classical
  have hbump : ∀ i : J, ∃ g : C(X, ℝ),
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      (i ∉ s → g = 0) ∧ (i ∈ s → EqOn g 1 (K i)) ∧
      closure {x | g x ≠ 0} ⊆ U i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨g, hgone, hgbounds, hgsupport⟩ :=
        exists_one_on_closed_with_closure_subset (hK i hi) (hU i hi) (hKU i hi)
      exact ⟨g, hgbounds, fun h => (h hi).elim, fun _ => hgone, hgsupport⟩
    · refine ⟨0, ?_, fun _ => rfl, ?_, ?_⟩
      · intro x
        simp
      · exact fun h => (hi h).elim
      · simp
  choose g hgbounds hgzero hgone hgsupport using hbump
  let S : X → ℝ := fun x => ∑ i ∈ s, g i x
  have hS : Continuous S := continuous_finsetSum s fun i _ => (g i).continuous
  have hS_one (x : X) : 1 ≤ S x := by
    obtain ⟨i, hi, hxi⟩ := hcover x
    calc
      1 = g i x := (hgone i hi hxi).symm
      _ ≤ S x := Finset.single_le_sum (fun j _ => (hgbounds j x).1) hi
  have hS_pos (x : X) : 0 < S x := lt_of_lt_of_le zero_lt_one (hS_one x)
  have hS_ne (x : X) : S x ≠ 0 := ne_of_gt (hS_pos x)
  let w : J → C(X, ℝ) := fun i =>
    ⟨fun x => g i x / S x, (g i).continuous.div₀ hS hS_ne⟩
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i x
    change 0 ≤ g i x / S x ∧ g i x / S x ≤ 1
    exact ⟨div_nonneg (hgbounds i x).1 (hS_pos x).le,
      (div_le_one (hS_pos x)).2 ((hgbounds i x).2.trans (hS_one x))⟩
  · intro i hi
    ext x
    change g i x / S x = 0
    simp [hgzero i hi]
  · intro x
    change (∑ i ∈ s, g i x / S x) = 1
    rw [← Finset.sum_div]
    exact div_self (hS_ne x)
  · intro i
    refine (closure_mono ?_).trans (hgsupport i)
    intro x hx
    change g i x ≠ 0
    intro hzero
    apply hx
    change g i x / S x = 0
    rw [hzero, zero_div]

/-- A finite open cover of a normal space admits a partition of unity with closed cozero
sets subordinate to the cover. The weights lie in `[0, 1]`, are zero as continuous maps off
`s`, and sum to one over `s`. Subordination holds at every index, although openness is needed
only on `s` and the index type is arbitrary. No compactness, nonemptiness or separation
hypothesis beyond `NormalSpace X` is required.

The proof combines finite normal shrinking with Urysohn's lemma. The latter is used via
Yury Kudryashov's formalization in Mathlib. -/
theorem exists_finite_weights {J : Type v}
    (s : Finset J) (U : J → Set X)
    (hU : ∀ i ∈ s, IsOpen (U i)) (hcover : (⋃ i ∈ s, U i) = Set.univ) :
    ∃ w : J → C(X, ℝ),
      (∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) ∧
      (∀ i, i ∉ s → w i = 0) ∧
      (∀ x, ∑ i ∈ s, w i x = 1) ∧
      ∀ i, closure {x | w i x ≠ 0} ⊆ U i := by
  classical
  have hpointcover : ∀ x : X, ∃ i, i ∈ (s : Set J) ∧ x ∈ U i := by
    intro x
    have hx : x ∈ ⋃ i ∈ s, U i := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi, hxi⟩
  obtain ⟨V, _, _, hVU, hVcover⟩ :=
    Set.Finite.exists_open_cover_shrinking s.finite_toSet U hU hpointcover
  let K : J → Set X := fun i => closure (V i)
  refine exists_finite_weights_of_closed_cover s U K hU
    (fun _ _ => isClosed_closure) (fun i _ => hVU i) ?_
  intro x
  obtain ⟨i, hi, hxi⟩ := hVcover x
  exact ⟨i, hi, subset_closure hxi⟩

end ContinuousMap
