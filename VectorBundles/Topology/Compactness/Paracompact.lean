/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Paracompact

/-!
# Paracompactness of continuous retracts

A continuous retract of a paracompact space is paracompact. The ambient space and
its retract may belong to different universes, and neither separation nor
nonemptiness assumptions are needed.

An open cover of the retract pulls back along the retraction to an open cover of
the ambient space. Mathlib's `precise_refinement` gives a locally finite open
refinement indexed by the original cover, even when its index type belongs to a
different universe. Pulling this refinement back along the continuous section
preserves local finiteness; the left-inverse identity gives the required
refinement of the original cover.

## References

* Reid Barton, Yury Kudryashov, and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Paracompact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Paracompact.lean):
  paracompactness and precise locally finite refinements.
-/

@[expose] public section

universe uX uY

/-- A continuous retract of a paracompact space is paracompact, without separation
or nonemptiness assumptions. -/
theorem ParacompactSpace.of_continuous_leftInverse
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    [ParacompactSpace X] {r : X → Y} {j : Y → X}
    (hr : Continuous r) (hj : Continuous j) (hjr : Function.LeftInverse r j) :
    ParacompactSpace Y := by
  constructor
  intro α s hsopen hscover
  obtain ⟨t, htopen, htcover, htfinite, htrefine⟩ :=
    precise_refinement (fun a => r ⁻¹' s a) (fun a => (hsopen a).preimage hr)
      (by rw [← Set.preimage_iUnion, hscover, Set.preimage_univ])
  refine ⟨α, (fun a => j ⁻¹' t a), (fun a => (htopen a).preimage hj), ?_,
    htfinite.preimage_continuous hj, ?_⟩
  · rw [← Set.preimage_iUnion, htcover, Set.preimage_univ]
  · intro a
    refine ⟨a, ?_⟩
    intro y hy
    have hmem : r (j y) ∈ s a := htrefine a hy
    simpa only [hjr y] using hmem
