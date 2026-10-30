/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Uniform subdivisions near a point of a product

An open cover of `X × I` admits, near each point of `X`, a finite monotone subdivision
of the unit interval whose closed slabs lie in selected members of the original cover.
The neighbourhood in `X` is common to all the finitely many slabs.

## References

- The Mathlib contributors, `exists_monotone_Icc_subset_open_cover_unitInterval`
  and `generalized_tube_lemma`.
-/

@[expose] public section

open Set
open scoped unitInterval

universe uX uJ

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
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  let N := n + 1
  have hN : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le n)
  have htN : t N = 1 := hn N (Nat.le_succ n)
  choose j hj using (fun k : Fin N ↦ hsub k.val)
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
    N, hN, t, ht0, hmono, htN, j, ?_⟩
  · exact mem_iInter.mpr hxU
  · intro k b hb
    exact hUW k ⟨mem_iInter.mp hb.1 k, hb.2⟩
