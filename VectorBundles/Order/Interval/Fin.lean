/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Closed intervals between consecutive terms of a finite monotone sequence

The closed intervals between consecutive terms of a finite monotone sequence with at
least two terms cover the closed interval between its first and last terms. Repeated terms
are allowed.

## References

- The Mathlib contributors, `Set.Icc_union_Icc_eq_Icc`.
-/

@[expose] public section

open Set

universe u

/-- The closed intervals between consecutive values of a monotone map on `Fin (n + 1)`
cover the interval between its endpoints, provided there is at least one interval.
Repeated values, including a constant map, are allowed. -/
theorem Monotone.iUnion_Icc_castSucc_succ {α : Type u} [LinearOrder α] {n : ℕ}
    {g : Fin (n + 1) → α} (hg : Monotone g) (hn : 1 ≤ n) :
    (⋃ k : Fin n, Icc (g k.castSucc) (g k.succ)) = Icc (g 0) (g (Fin.last n)) := by
  refine Subset.antisymm (iUnion_subset fun k x hx ↦ ?_) ?_
  · exact ⟨(hg (Fin.zero_le _)).trans hx.1, hx.2.trans (hg (Fin.le_last _))⟩
  · intro x hx
    have hcover : ∀ i : Fin (n + 1), x ∈ Icc (g 0) (g i) →
        x ∈ ⋃ k : Fin n, Icc (g k.castSucc) (g k.succ) := by
      intro i
      induction i using Fin.induction with
      | zero =>
          intro hx
          refine mem_iUnion.mpr ⟨⟨0, hn⟩, hx.1, ?_⟩
          exact hx.2.trans (hg (Fin.castSucc_le_succ ⟨0, hn⟩))
      | succ i ih =>
          intro hx
          rw [← Icc_union_Icc_eq_Icc (hg (Fin.zero_le i.castSucc))
            (hg (Fin.castSucc_le_succ i))] at hx
          exact hx.elim ih (fun hs ↦ mem_iUnion.mpr ⟨i, hs⟩)
    exact hcover (Fin.last n) hx
