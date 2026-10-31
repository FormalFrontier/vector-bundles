/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.UnitInterval
public import VectorBundles.Order.Interval.Fin
public import VectorBundles.Topology.Compactness.Product

/-!
# Finite subdivisions subordinate to open covers

An open cover of any closed real interval admits a finite monotone subdivision whose
closed slabs lie in selected members of the original cover and cover the whole interval.
There is at least one slab, including when the interval is a singleton.

An open cover of `X × I` admits such a subdivision near each point of `X`.
The neighbourhood in `X` is common to all the finitely many slabs.

An ambient open cover of the product of a compact subset of `X` and a closed real
interval admits one finite subdivision and one finite ambient open base cover common
to all slabs. Each full rectangle lies in a member of the original cover. This follows
from `IsCompact.exists_fin_open_cover_prod_subset` and the finite interval subdivision:
the ambient open base family is retained while the interval cover is subdivided.

## References

- Mathlib's `Topology.UnitInterval` (Patrick Massot and Kim Morrison),
  `exists_monotone_Icc_subset_open_cover_Icc`.
- Mathlib's `Topology.Compactness.Compact` (Johannes Hölzl, Mario Carneiro and
  Yury Kudryashov), `generalized_tube_lemma` and `IsCompact.elim_finite_subcover`.
- Mathlib's `Topology.Compactness.Paracompact` (Reid Barton and Yury Kudryashov),
  the finite slice-neighbourhood construction in the compact-product argument.
-/

@[expose] public section

open Set
open scoped unitInterval

universe uX uJ

-- Keep the Nat-indexed sequence for consumers that need more than the finite restriction.
-- Both subdivision theorems share the positive truncation and finite cover selection.
private theorem exists_pos_nat_monotone_Icc_subset_open_cover_Icc
    {ι : Sort uJ} {a b : ℝ} (hab : a ≤ b) {c : ι → Set (Icc a b)}
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : univ ⊆ ⋃ i, c i) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ t : ℕ → Icc a b,
      (t 0 : ℝ) = a ∧ Monotone t ∧ (t n : ℝ) = b ∧
        ∃ j : Fin n → ι, ∀ k, Icc (t k.val) (t (k.val + 1)) ⊆ c (j k) := by
  classical
  have hcCover' : univ ⊆ ⋃ i : PLift ι, c i.down := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcCover hs)
    exact mem_iUnion.mpr ⟨PLift.up i, hi⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab (fun i : PLift ι ↦ hcOpen i.down) hcCover'
  choose j hj using (fun k : Fin (n + 1) ↦ hsub k.val)
  exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), t, ht0, hmono,
    hn (n + 1) (Nat.le_succ n), (fun k ↦ (j k).down), hj⟩

/-- Any open cover of a closed real interval admits a finite monotone subdivision
whose whole closed slabs lie in selected members of that same cover. The slabs cover
the interval exactly. There is at least one slab; repeated cuts allow `a = b`.

This is the finite-indexed form of Mathlib's
`exists_monotone_Icc_subset_open_cover_Icc`, allowing a cover indexed by any sort. -/
theorem exists_fin_monotone_Icc_subset_open_cover_Icc
    {ι : Sort uJ} {a b : ℝ} (hab : a ≤ b) {c : ι → Set (Icc a b)}
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : univ ⊆ ⋃ i, c i) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ g : Fin (n + 1) → Icc a b,
      (g 0 : ℝ) = a ∧ Monotone g ∧ (g (Fin.last n) : ℝ) = b ∧
        (∃ j : Fin n → ι, ∀ k, Icc (g k.castSucc) (g k.succ) ⊆ c (j k)) ∧
        (⋃ k : Fin n, Icc (g k.castSucc) (g k.succ)) = univ := by
  obtain ⟨n, hn, t, ht0, hmono, htn, j, hj⟩ :=
    exists_pos_nat_monotone_Icc_subset_open_cover_Icc hab hcOpen hcCover
  have hg : Monotone (fun k : Fin (n + 1) ↦ t k.val) := fun _ _ h ↦ hmono h
  refine ⟨n, hn, (fun k ↦ t k.val), ht0, hg, htn, ⟨j, hj⟩, ?_⟩
  rw [hg.iUnion_Icc_castSucc_succ hn]
  ext s
  simp only [mem_Icc, mem_univ, iff_true]
  change (t 0 : ℝ) ≤ s.val ∧ s.val ≤ (t n : ℝ)
  simpa only [ht0, htn, mem_Icc] using s.property

/-- Near any `x : X`, an open cover of `X × I` admits a finite monotone subdivision
of `I` such that each closed slab over one common open neighbourhood of `x` lies in
one member of the original cover. The subdivision has at least one slab; repeated
cuts are allowed. No separation or compactness assumption on `X` is needed. -/
theorem exists_open_nhds_prod_Icc_subset_open_cover_unitInterval
    {X : Type uX} [TopologicalSpace X] {J : Type uJ}
    (W : J → Set (X × I)) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : X × I, ∃ j, b ∈ W j) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ t N = 1 ∧
          ∃ j : Fin N → J, ∀ k,
            U ×ˢ Icc (t k.val) (t (k.val + 1)) ⊆ W (j k) := by
  classical
  let c : J → Set I := fun j ↦ (fun s : I ↦ (x, s)) ⁻¹' W j
  have hcOpen : ∀ j, IsOpen (c j) := fun j ↦
    (hW j).preimage (continuous_const.prodMk continuous_id)
  have hcCover : univ ⊆ ⋃ j, c j := by
    intro s _
    obtain ⟨j, hj⟩ := hcover (x, s)
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨N, hN, t, ht0, hmono, htN, j, hj⟩ :=
    exists_pos_nat_monotone_Icc_subset_open_cover_Icc zero_le_one hcOpen hcCover
  have ht0' : t 0 = 0 := Subtype.ext ht0
  have htN' : t N = 1 := Subtype.ext htN
  have hlocal : ∀ k : Fin N,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        U ×ˢ Icc (t k.val) (t (k.val + 1)) ⊆ W (j k) := by
    intro k
    have hslab : ({x} : Set X) ×ˢ Icc (t k.val) (t (k.val + 1)) ⊆ W (j k) := by
      rintro ⟨y, s⟩ ⟨hy, hs⟩
      have hyx : y = x := mem_singleton_iff.mp hy
      subst y
      exact hj k hs
    obtain ⟨U, V, hU, _hV, hxU, hIV, hUV⟩ :=
      generalized_tube_lemma (isCompact_singleton : IsCompact ({x} : Set X))
        (isClosed_Icc.isCompact : IsCompact (Icc (t k.val) (t (k.val + 1))))
        (hW (j k)) hslab
    refine ⟨U, hU, hxU (mem_singleton x), ?_⟩
    intro b hb
    exact hUV ⟨hb.1, hIV hb.2⟩
  choose U hU hxU hUW using hlocal
  refine ⟨⋂ k : Fin N, U k, isOpen_iInter_of_finite hU, ?_,
    N, hN, t, ht0', hmono, htN', j, ?_⟩
  · exact mem_iInter.mpr hxU
  · intro k b hb
    exact hUW k ⟨mem_iInter.mp hb.1 k, hb.2⟩

/-- An open cover of `S ×ˢ Icc a b`, with `S` compact in an arbitrary topological
space, admits one finite monotone grid from `a` to `b` and one finite family of
ambient open sets covering `S`, common to every slab. Each full rectangle lies
in a selected member of the original ambient cover, and the real closed slabs
cover `Icc a b` exactly.

There is at least one slab, even when `a = b`; repeated cuts are allowed. The
finite base family may be empty, so an empty compact set requires no cover index.
No separation assumption on the ambient space is needed.

The proof applies `IsCompact.exists_fin_open_cover_prod_subset` to the compact
factors, then applies `exists_fin_monotone_Icc_subset_open_cover_Icc` to the
induced interval cover. The ambient open base family is unchanged. -/
theorem IsCompact.exists_fin_open_cover_prod_Icc_subset
    {X : Type uX} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {ι : Sort uJ} {a b : ℝ} (hab : a ≤ b) (U : ι → Set (X × ℝ))
    (hU : ∀ i, IsOpen (U i)) (hcover : S ×ˢ Icc a b ⊆ ⋃ i, U i) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ g : Fin (n + 1) → Icc a b,
      (g 0 : ℝ) = a ∧ Monotone g ∧ (g (Fin.last n) : ℝ) = b ∧
      (⋃ k : Fin n, Icc (g k.castSucc : ℝ) (g k.succ : ℝ)) = Icc a b ∧
      ∃ m : ℕ, ∃ V : Fin m → Set X,
        (∀ j, IsOpen (V j)) ∧ S ⊆ ⋃ j, V j ∧
        ∃ c : Fin m → Fin n → ι, ∀ j k,
          V j ×ˢ Icc (g k.castSucc : ℝ) (g k.succ : ℝ) ⊆ U (c j k) := by
  obtain ⟨m, V, hV, hSV, r, W, hW, hTW, c, hVW⟩ :=
    hS.exists_fin_open_cover_prod_subset isCompact_Icc U hU hcover
  let C : Fin r → Set (Icc a b) := fun k ↦ Subtype.val ⁻¹' W k
  have hC : ∀ k, IsOpen (C k) := fun k ↦ (hW k).preimage continuous_subtype_val
  have hcoverC : univ ⊆ ⋃ k, C k := by
    intro t _
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hTW t.property)
    exact mem_iUnion.mpr ⟨k, hk⟩
  obtain ⟨n, hn, g, hg0, hg, hgn, ⟨d, hd⟩, _⟩ :=
    exists_fin_monotone_Icc_subset_open_cover_Icc hab hC hcoverC
  have hslab : ∀ k : Fin n,
      Icc (g k.castSucc : ℝ) (g k.succ : ℝ) ⊆ W (d k) := by
    intro k s hs
    have hsab : s ∈ Icc a b :=
      ⟨(g k.castSucc).property.1.trans hs.1, hs.2.trans (g k.succ).property.2⟩
    exact hd k (show (⟨s, hsab⟩ : Icc a b) ∈ Icc (g k.castSucc) (g k.succ) from hs)
  refine ⟨n, hn, g, hg0, hg, hgn, ?_, m, V, hV, hSV, (fun j k ↦ c j (d k)), ?_⟩
  · have hgReal : Monotone (fun k ↦ (g k : ℝ)) := fun _ _ h ↦ hg h
    simpa only [hg0, hgn] using hgReal.iUnion_Icc_castSucc_succ hn
  · intro j k z hz
    exact hVW j (d k) ⟨hz.1, hslab k hz.2⟩
