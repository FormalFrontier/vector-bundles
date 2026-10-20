/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Lindelöf preimages and mixed products

The preimage of a Lindelöf set under a proper map is Lindelöf. The set need not be
closed, and neither space needs to satisfy a separation axiom. This extends Mathlib's
Lindelöf-preimage theorem for closed embeddings to proper maps.

A Lindelöf set times a compact set is Lindelöf. Decomposing a σ-compact set into
compact sets gives the same conclusion for a Lindelöf set times a σ-compact set.
Neither result requires separation assumptions on the ambient spaces.

These auxiliary product arguments use Mathlib's Lindelöf formalization by Josha Dekker
and contributors. The compact-factor argument applies the proper-preimage theorem to
the first projection with the compact subtype as its second factor, then takes a
continuous image in the original product. The σ-compact-factor argument uses Mathlib's
countable-union API.

## References

* Josha Dekker and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Lindelof`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Lindelof.lean):
  Lindelöf continuous images, countable subcovers, and countable unions.
* Anatole Dedecker, Etienne Marion, and Mathlib contributors,
  [`Mathlib.Topology.Maps.Proper.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Proper/Basic.lean):
  proper maps, compact fibers, and compact-factor projections.
-/

@[expose] public section

universe u v

open Set

/-- The preimage of a Lindelöf set under a proper map is Lindelöf, without separation
assumptions on either space or a closedness assumption on the set. -/
theorem IsProperMap.isLindelof_preimage
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) {s : Set Y} (hs : IsLindelof s) :
    IsLindelof (f ⁻¹' s) := by
  classical
  apply isLindelof_of_countable_subcover
  intro ι U hU hcover
  have hlocal : ∀ y : s, ∃ (a : Set Y) (r : Finset ι),
      IsOpen a ∧ y.1 ∈ a ∧ f ⁻¹' a ⊆ ⋃ i ∈ r, U i := by
    intro y
    have hcompact : IsCompact (f ⁻¹' ({y.1} : Set Y)) :=
      hf.isCompact_preimage isCompact_singleton
    obtain ⟨r, hr⟩ := hcompact.elim_finite_subcover U hU (by
      intro x hx
      have hxy : f x = y.1 := mem_singleton_iff.mp hx
      exact hcover (show f x ∈ s from hxy.symm ▸ y.2))
    -- Closedness makes the set of points whose fibers lie in the finite union open.
    refine ⟨kernImage f (⋃ i ∈ r, U i), r,
      (isClosedMap_iff_kernImage.mp hf.isClosedMap) (isOpen_biUnion fun i _ => hU i),
      ?_, ?_⟩
    · intro x hxy
      exact hr (mem_singleton_iff.mpr hxy)
    · intro x hx
      exact hx rfl
  choose a r hao hya har using hlocal
  obtain ⟨c, hc, hsc⟩ := hs.elim_countable_subcover a hao (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hya ⟨y, hy⟩⟩)
  refine ⟨⋃ y ∈ c, (r y : Set ι), hc.biUnion (fun y _ => (r y).finite_toSet.countable), ?_⟩
  intro x hx
  rcases mem_iUnion.mp (hsc hx) with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨hyc, hxy⟩
  rcases mem_iUnion.mp (har y hxy) with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨hir, hxi⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
    ⟨mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyc, hir⟩⟩, hxi⟩⟩

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {t : Set Y}

/-- A Lindelöf set times a compact set is Lindelöf. -/
theorem IsLindelof.prod_of_isCompact (hs : IsLindelof s) (ht : IsCompact t) :
    IsLindelof (s ×ˢ t) := by
  let : CompactSpace t := isCompact_iff_compactSpace.mp ht
  have hpre : IsLindelof ((Prod.fst : X × t → X) ⁻¹' s) :=
    (isProperMap_fst_of_compactSpace (X := X) (Y := t)).isLindelof_preimage hs
  have himage :
      (fun p : X × t => (p.1, (p.2 : Y))) ''
        ((Prod.fst : X × t → X) ⁻¹' s) = s ×ˢ t := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hx, rfl⟩
      exact ⟨hx, y.2⟩
    · rintro ⟨hx, hy⟩
      exact ⟨(p.1, ⟨p.2, hy⟩), hx, rfl⟩
  rw [← himage]
  exact hpre.image (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- A Lindelöf set times a σ-compact set is Lindelöf. -/
theorem IsLindelof.prod_of_isSigmaCompact (hs : IsLindelof s) (ht : IsSigmaCompact t) :
    IsLindelof (s ×ˢ t) := by
  rcases ht with ⟨K, hK, rfl⟩
  rw [prod_iUnion]
  exact isLindelof_iUnion fun n => hs.prod_of_isCompact (hK n)
