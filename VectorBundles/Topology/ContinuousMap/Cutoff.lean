/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous cutoffs on normal spaces

A closed set in an open neighborhood of a normal space admits a continuous real cutoff
with values in `[0, 1]`, equal to one on the closed set, whose closed cozero set is contained
in the neighborhood.

## References

- Urysohn's lemma, as formalized by Yury Kudryashov in Mathlib's
  `Mathlib.Topology.UrysohnsLemma`.
-/

@[expose] public section

open Set

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X] [NormalSpace X]

/-- A continuous bump equal to one on a closed set, with its closed cozero set in a given
open neighborhood. -/
theorem exists_one_on_closed_with_closure_subset {K U : Set X}
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

end ContinuousMap
