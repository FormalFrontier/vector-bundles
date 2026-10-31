/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
# Finite open rectangular covers of compact products

An ambient open cover of the product of two compact sets admits finite ambient
open covers of the two factors whose full pairwise products refine the original
cover. Either finite family may be empty; no separation or nonemptiness
assumptions are needed.

## References

- Mathlib's `Topology.Compactness.Compact` (Johannes Hölzl, Mario Carneiro and
  Yury Kudryashov), for compactness, tubes and finite subcovers.
- Mathlib's `Topology.Compactness.Paracompact` (Reid Barton and Yury Kudryashov),
  for the finite slice-neighbourhood construction, following Dan Ma's
  [compact-times-paracompact exposition][ma].
- Mathlib's finite Pi and finite-equivalence formalizations (Mario Carneiro).

[ma]: https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-is-paracompact/
-/

@[expose] public section

open Set

universe uX uY uJ

-- Choose original members pointwise on S, then shrink only the finitely selected
-- second-factor neighbourhoods. Empty S needs neither an ambient point nor a cover index.
private theorem IsCompact.exists_fin_open_cover_prod_nhds_subset
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} (hS : IsCompact S) {ι : Sort uJ} (U : ι → Set (X × Y))
    (hU : ∀ i, IsOpen (U i)) (y : Y) (hcover : S ×ˢ {y} ⊆ ⋃ i, U i) :
    ∃ N : Set Y, IsOpen N ∧ y ∈ N ∧ ∃ m : ℕ, ∃ V : Fin m → Set X,
      (∀ j, IsOpen (V j)) ∧ S ⊆ ⋃ j, V j ∧
      ∃ c : Fin m → ι, ∀ j, V j ×ˢ N ⊆ U (c j) := by
  classical
  have hlocal : ∀ x : S, ∃ i : ι, ∃ A : Set X, ∃ N : Set Y,
      IsOpen A ∧ IsOpen N ∧ x.val ∈ A ∧ y ∈ N ∧ A ×ˢ N ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      (hcover (show (x.val, y) ∈ S ×ˢ {y} from ⟨x.property, mem_singleton y⟩))
    have hxy : ({x.val} : Set X) ×ˢ {y} ⊆ U i := by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      obtain rfl := mem_singleton_iff.mp hz
      obtain rfl := mem_singleton_iff.mp hw
      exact hi
    obtain ⟨A, N, hA, hN, hxA, hyN, hAN⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_singleton (hU i) hxy
    exact ⟨i, A, N, hA, hN, hxA (mem_singleton _), hyN (mem_singleton _), hAN⟩
  choose c A N hA hN hxA hyN hAN using hlocal
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover A hA (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩)
  let e := Fintype.equivFin T
  refine ⟨⋂ z : T, N z.val, isOpen_iInter_of_finite (fun z ↦ hN z.val),
    mem_iInter.mpr (fun z ↦ hyN z.val), Fintype.card T,
    (fun j ↦ A (e.symm j).val), (fun j ↦ hA (e.symm j).val), ?_,
    (fun j ↦ c (e.symm j).val), ?_⟩
  · intro x hx
    obtain ⟨z, hz, hxA⟩ := mem_iUnion₂.mp (hT hx)
    refine mem_iUnion.mpr ⟨e ⟨z, hz⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hxA
  · intro j z hz
    exact hAN (e.symm j).val ⟨hz.1, mem_iInter.mp hz.2 (e.symm j)⟩

/-- An ambient open cover of a product of two compact sets admits finite ambient
open covers of both factors such that every full product of selected open sets
lies in a selected member of the original cover. Either finite family may be empty.
The factor spaces have independent universes, and the original labels may belong
to any sort; no separation or nonemptiness assumptions are required.

The proof follows the finite slice-neighbourhood construction of Reid Barton and
Yury Kudryashov in Mathlib's `Topology.Compactness.Paracompact`, based on Dan Ma's
compact-times-paracompact argument. Finite subcovers and a common finite
intersection refinement give the two factor covers. -/
theorem IsCompact.exists_fin_open_cover_prod_subset
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} (hS : IsCompact S) (hT : IsCompact T)
    {ι : Sort uJ} (U : ι → Set (X × Y)) (hU : ∀ i, IsOpen (U i))
    (hcover : S ×ˢ T ⊆ ⋃ i, U i) :
    ∃ m : ℕ, ∃ V : Fin m → Set X,
      (∀ j, IsOpen (V j)) ∧ S ⊆ ⋃ j, V j ∧
      ∃ n : ℕ, ∃ W : Fin n → Set Y,
        (∀ k, IsOpen (W k)) ∧ T ⊆ ⋃ k, W k ∧
        ∃ c : Fin m → Fin n → ι, ∀ j k, V j ×ˢ W k ⊆ U (c j k) := by
  classical
  have hslice : ∀ y : T,
      ∃ N : Set Y, IsOpen N ∧ y.val ∈ N ∧ ∃ m : ℕ, ∃ V : Fin m → Set X,
        (∀ j, IsOpen (V j)) ∧ S ⊆ ⋃ j, V j ∧
        ∃ c : Fin m → ι, ∀ j, V j ×ˢ N ⊆ U (c j) := by
    intro y
    apply hS.exists_fin_open_cover_prod_nhds_subset U hU y.val
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    obtain rfl := mem_singleton_iff.mp hz
    exact hcover ⟨hx, y.property⟩
  choose N hN hyN m V hV hSV c hVU using hslice
  obtain ⟨R, hR⟩ := hT.elim_finite_subcover N hN (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyN ⟨y, hy⟩⟩)
  let eT := Fintype.equivFin R
  let n := Fintype.card R
  let t : Fin n → T := fun k ↦ (eT.symm k).val
  -- Intersect one member of each selected slice's base cover. Coordinate witnesses
  -- are chosen only after fixing x ∈ S, so the finite product may be empty.
  let P := ∀ k : Fin n, Fin (m (t k))
  let e := Fintype.equivFin P
  refine ⟨Fintype.card P, (fun q ↦ ⋂ k : Fin n, V (t k) (e.symm q k)), ?_, ?_,
    n, (fun k ↦ N (t k)), (fun k ↦ hN (t k)), ?_,
    (fun q k ↦ c (t k) (e.symm q k)), ?_⟩
  · intro q
    exact isOpen_iInter_of_finite (fun k ↦ hV (t k) (e.symm q k))
  · intro x hx
    have hxV : ∀ k : Fin n, ∃ r, x ∈ V (t k) r := fun k ↦
      mem_iUnion.mp (hSV (t k) hx)
    choose p hp using hxV
    refine mem_iUnion.mpr ⟨e p, ?_⟩
    simpa only [Equiv.symm_apply_apply] using
      (mem_iInter.mpr hp : x ∈ ⋂ k : Fin n, V (t k) (p k))
  · intro y hy
    obtain ⟨z, hz, hyN⟩ := mem_iUnion₂.mp (hR hy)
    refine mem_iUnion.mpr ⟨eT ⟨z, hz⟩, ?_⟩
    simpa only [t, Equiv.symm_apply_apply] using hyN
  · intro q k z hz
    exact hVU (t k) (e.symm q k) ⟨mem_iInter.mp hz.1 k, hz.2⟩
