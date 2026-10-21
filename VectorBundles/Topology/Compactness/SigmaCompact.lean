/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Sigma-compact inverse images under proper maps

The inverse image of a sigma-compact subset under a proper map is sigma-compact.
In particular, a proper map to a sigma-compact space has sigma-compact domain.
The domain and codomain retain their given topologies and may belong to independent
universes. The subset need not be closed, and neither separation, surjectivity nor
nonemptiness is required.

The compact-cover formulation of sigma-compactness and compact inverse images under
proper maps give these statements without local compactness assumptions.

## References

* Johannes Hölzl, Mario Carneiro, Yury Kudryashov, and Mathlib contributors,
  [`Mathlib.Topology.Compactness.SigmaCompact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/SigmaCompact.lean):
  sigma-compact sets, countable compact covers and `SigmaCompactSpace`.
* Anatole Dedecker, Etienne Marion, and Mathlib contributors,
  [`Mathlib.Topology.Maps.Proper.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Proper/Basic.lean):
  `IsProperMap.isCompact_preimage`.
-/

@[expose] public section

universe uX uY

/-- The inverse image of a sigma-compact subset under a proper map is sigma-compact.
The subset need not be closed; no separation or surjectivity assumption is needed. -/
theorem IsProperMap.isSigmaCompact_preimage
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) {s : Set Y} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f ⁻¹' s) := by
  rcases hs with ⟨K, hK, hcover⟩
  refine ⟨fun n => f ⁻¹' K n, fun n => hf.isCompact_preimage (hK n), ?_⟩
  rw [← Set.preimage_iUnion, hcover]

/-- A space admitting a proper map to a sigma-compact space is sigma-compact.
No separation, surjectivity or nonemptiness assumption is needed. -/
theorem IsProperMap.sigmaCompactSpace
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) [SigmaCompactSpace Y] : SigmaCompactSpace X := by
  apply isSigmaCompact_univ_iff.mp
  simpa only [Set.preimage_univ] using
    hf.isSigmaCompact_preimage (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set Y))

/-- For a proper map, a preimage is sigma-compact exactly when the part of the set in the
range is sigma-compact. No separation or surjectivity assumption is needed. -/
theorem IsProperMap.isSigmaCompact_preimage_iff
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) (s : Set Y) :
    IsSigmaCompact (f ⁻¹' s) ↔ IsSigmaCompact (s ∩ Set.range f) := by
  constructor
  · intro hs
    simpa only [Set.image_preimage_eq_inter_range] using
      (IsSigmaCompact.image hf.continuous hs)
  · intro hs
    simpa only [Set.preimage_inter_range] using hf.isSigmaCompact_preimage hs
