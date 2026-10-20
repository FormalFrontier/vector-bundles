/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Mixed Lindelöf products

A Lindelöf set times a compact set is Lindelöf. Decomposing a σ-compact set into
compact sets gives the same conclusion for a Lindelöf set times a σ-compact set.
Neither result requires separation assumptions on the ambient spaces.

These auxiliary product arguments use Mathlib's Lindelöf formalization by Josha Dekker
and contributors. The compact-factor argument combines its countable-subcover API with
Mathlib's `generalized_tube_lemma` to pass from a finite cover of each compact slice to a
neighborhood in the first factor. The σ-compact-factor argument then uses Mathlib's
countable-union API.

## References

* Josha Dekker and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Lindelof`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Lindelof.lean):
  the countable-subcover and countable-union formalization of Lindelöfness.
* Mathlib contributors,
  [`Mathlib.Topology.Compactness.Compact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Compact.lean):
  `generalized_tube_lemma`.
-/

@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {t : Set Y}

/-- A Lindelöf set times a compact set is Lindelöf. -/
theorem IsLindelof.prod_of_isCompact (hs : IsLindelof s) (ht : IsCompact t) :
    IsLindelof (s ×ˢ t) := by
  classical
  apply isLindelof_of_countable_subcover
  intro ι U hU hcover
  have hlocal : ∀ x : s, ∃ (a : Set X) (r : Finset ι),
      IsOpen a ∧ x.1 ∈ a ∧ a ×ˢ t ⊆ ⋃ i ∈ r, U i := by
    intro x
    have hcompact : IsCompact (({x.1} : Set X) ×ˢ t) := isCompact_singleton.prod ht
    obtain ⟨r, hr⟩ := hcompact.elim_finite_subcover U hU (by
      rintro ⟨z, y⟩ ⟨hz, hy⟩
      have hzx : z = x.1 := mem_singleton_iff.mp hz
      subst z
      exact hcover ⟨x.2, hy⟩)
    obtain ⟨a, b, hao, _, hxa, htb, hab⟩ :=
      generalized_tube_lemma isCompact_singleton ht (isOpen_biUnion fun i _ => hU i) hr
    exact ⟨a, r, hao, hxa (by simp), fun p hp => hab ⟨hp.1, htb hp.2⟩⟩
  choose a r hao hxa har using hlocal
  obtain ⟨c, hc, hsc⟩ := hs.elim_countable_subcover a hao (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxa ⟨x, hx⟩⟩)
  refine ⟨⋃ x ∈ c, (r x : Set ι), hc.biUnion (fun x _ => (r x).finite_toSet.countable), ?_⟩
  intro p hp
  rcases mem_iUnion.mp (hsc hp.1) with ⟨x, hx⟩
  rcases mem_iUnion.mp hx with ⟨hxc, hpx⟩
  rcases mem_iUnion.mp (har x ⟨hpx, hp.2⟩) with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨hir, hpi⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
    ⟨mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxc, hir⟩⟩, hpi⟩⟩

/-- A Lindelöf set times a σ-compact set is Lindelöf. -/
theorem IsLindelof.prod_of_isSigmaCompact (hs : IsLindelof s) (ht : IsSigmaCompact t) :
    IsLindelof (s ×ˢ t) := by
  rcases ht with ⟨K, hK, rfl⟩
  rw [prod_iUnion]
  exact isLindelof_iUnion fun n => hs.prod_of_isCompact (hK n)
