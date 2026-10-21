/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Countable compactness and proper maps

For a proper map, countable compactness of a preimage is equivalent to countable compactness
of the part of the target set lying in the range. In particular, its domain is countably
compact if and only if its range is countably compact. The spaces retain their given
topologies and independent universes, without separation or surjectivity assumptions.

Countable compactness uses cluster points of nonbottom countably generated filters, not
convergent subsequences. The reverse implication maps such a filter to the target and
lifts its cluster point using properness; the forward implication uses continuity.

## References

* Michał Świętek, Yongxi Lin, and Mathlib contributors,
  [`Mathlib.Topology.Compactness.CountablyCompact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/CountablyCompact.lean):
  filter countable compactness and its continuous-image API.
* Anatole Dedecker, Etienne Marion, and Mathlib contributors,
  [`Mathlib.Topology.Maps.Proper.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Proper/Basic.lean):
  proper maps and their cluster-point lifting field.
-/

@[expose] public section

universe u v

open Set Filter

namespace IsProperMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- A set has countably compact preimage under a proper map if and only if its intersection
with the range is countably compact. -/
theorem isCountablyCompact_preimage_iff (hf : IsProperMap f) (s : Set Y) :
    IsCountablyCompact (f ⁻¹' s) ↔ IsCountablyCompact (s ∩ range f) := by
  constructor
  · intro hs
    simpa only [image_preimage_eq_inter_range] using hs.image hf.continuous
  · intro hs ℱ _ _ hℱ
    have hmap : map f ℱ ≤ 𝓟 (s ∩ range f) := by
      simpa only [map_principal, image_preimage_eq_inter_range] using
        (map_mono hℱ : map f ℱ ≤ map f (𝓟 (f ⁻¹' s)))
    obtain ⟨y, hy, hcluster⟩ := hs hmap
    obtain ⟨x, hxy, hx⟩ := hf.clusterPt_of_mapClusterPt hcluster
    refine ⟨x, ?_, hx⟩
    change f x ∈ s
    exact hxy.symm ▸ hy.1

/-- For a set contained in the range of a proper map, countable compactness is equivalent
to countable compactness of its preimage. -/
theorem isCountablyCompact_preimage_iff_of_subset_range (hf : IsProperMap f) (s : Set Y)
    (hs : s ⊆ range f) : IsCountablyCompact (f ⁻¹' s) ↔ IsCountablyCompact s := by
  simpa only [inter_eq_left.mpr hs] using hf.isCountablyCompact_preimage_iff s

/-- The domain of a proper map is countably compact if and only if its range is
countably compact in the target. -/
theorem countablyCompactSpace_iff_isCountablyCompact_range (hf : IsProperMap f) :
    CountablyCompactSpace X ↔ IsCountablyCompact (range f) := by
  simpa only [preimage_univ, univ_inter, isCountablyCompact_univ_iff] using
    hf.isCountablyCompact_preimage_iff (univ : Set Y)

end IsProperMap
