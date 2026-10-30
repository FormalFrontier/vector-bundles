/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.UnitInterval
public import VectorBundles.Order.Interval.Fin

/-!
# Finite subdivisions subordinate to open covers

An open cover of any closed real interval admits a finite monotone subdivision whose
closed slabs lie in selected members of the original cover and cover the whole interval.
There is at least one slab, including when the interval is a singleton.

An open cover of `X × I` admits such a subdivision near each point of `X`.
The neighbourhood in `X` is common to all the finitely many slabs.

## References

- The Mathlib contributors, `exists_monotone_Icc_subset_open_cover_Icc`
  and `generalized_tube_lemma`.
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
