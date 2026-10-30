/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking finitely supported open covers

A finite subfamily covering a normal space admits an open shrinking supported
on the same set of indices. Only the original sets with indices in that finite
set need be open. Normality is used without a T1 assumption.

The construction extends the original family by the empty set off its finite
support and applies `exists_iUnion_eq_closure_subset`. Applying the resulting
finite-support statement twice gives nested open buffers.

## References

The proofs use Mathlib's point-finite shrinking theorem
`exists_iUnion_eq_closure_subset` from `Mathlib.Topology.ShrinkingLemma`.
-/

@[expose] public section

universe u v

namespace Set.Finite

/-- Finite-support form of Mathlib's `exists_iUnion_eq_closure_subset`:
shrink an open cover indexed by a finite subset of an arbitrary index type,
with an open, finitely supported output and closure containment at every index. -/
theorem exists_open_cover_shrinking {X : Type u} {I : Type v}
    [TopologicalSpace X] [NormalSpace X] {s : Set I} (hs : s.Finite)
    (U : I → Set X) (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, i ∈ s ∧ x ∈ U i) :
    ∃ V : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      (∀ i, i ∉ s → V i = ∅) ∧
      (∀ i, closure (V i) ⊆ U i) ∧
      (∀ x : X, ∃ i, i ∈ s ∧ x ∈ V i) := by
  -- The union over the membership proof is `U i` on `s` and empty off `s`.
  let padded : I → Set X := fun i => ⋃ (_ : i ∈ s), U i
  have mem_padded (i : I) (x : X) :
      x ∈ padded i ↔ i ∈ s ∧ x ∈ U i := by
    simp only [padded, Set.mem_iUnion, exists_prop]
  have hopen (i : I) : IsOpen (padded i) :=
    isOpen_iUnion fun hi => hU i hi
  have hfinite (x : X) : {i | x ∈ padded i}.Finite :=
    hs.subset fun i hi => ((mem_padded i x).mp hi).1
  have hfull : (⋃ i, padded i) = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨i, his, hxi⟩ := hcover x
    exact ⟨i, (mem_padded i x).mpr ⟨his, hxi⟩⟩
  obtain ⟨V, hVfull, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset hopen hfinite hfull
  have hVmem (i : I) (x : X) (hx : x ∈ V i) : i ∈ s :=
    ((mem_padded i x).mp (hVclosure i (subset_closure hx))).1
  refine ⟨V, hVopen, ?_, ?_, ?_⟩
  · intro i his
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => his (hVmem i x hx)
  · intro i x hx
    exact ((mem_padded i x).mp (hVclosure i hx)).2
  · intro x
    obtain ⟨i, hxi⟩ := Set.iUnion_eq_univ_iff.mp hVfull x
    exact ⟨i, hVmem i x hxi, hxi⟩

/-- Two successive shrinkings give nested, finitely supported open covers,
with closure containment at both levels and at every index. -/
theorem exists_nested_open_cover_shrinking {X : Type u} {I : Type v}
    [TopologicalSpace X] [NormalSpace X] {s : Set I} (hs : s.Finite)
    (U : I → Set X) (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, i ∈ s ∧ x ∈ U i) :
    ∃ V W : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      (∀ i, IsOpen (W i)) ∧
      (∀ i, i ∉ s → V i = ∅) ∧
      (∀ i, i ∉ s → W i = ∅) ∧
      (∀ i, closure (V i) ⊆ W i) ∧
      (∀ i, closure (W i) ⊆ U i) ∧
      (∀ x : X, ∃ i, i ∈ s ∧ x ∈ V i) ∧
      (∀ x : X, ∃ i, i ∈ s ∧ x ∈ W i) := by
  obtain ⟨W, hWopen, hWsupport, hWclosure, hWcover⟩ :=
    hs.exists_open_cover_shrinking U hU hcover
  obtain ⟨V, hVopen, hVsupport, hVclosure, hVcover⟩ :=
    hs.exists_open_cover_shrinking W (fun i _ => hWopen i) hWcover
  exact ⟨V, W, hVopen, hWopen, hVsupport, hWsupport,
    hVclosure, hWclosure, hVcover, hWcover⟩

end Set.Finite
