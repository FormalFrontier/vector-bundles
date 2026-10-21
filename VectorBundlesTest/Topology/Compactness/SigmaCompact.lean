/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Compact

/-!
# Sigma-compact inverse images of the real two-sheeted projection

The first projection `ℝ × Fin 2 → ℝ` is proper because its second factor is finite.
The noncompact closed ray `Ici 0` is sigma-compact as a closed subset of the
sigma-compact real line. The examples apply the proper-map results to this ray,
to the empty subset, and to the whole product. Range-relative reflection also
handles the real identity on a closed interval and an empty-source map with
an arbitrary target subset.
-/

@[expose] public section

/-- The two-sheeted projection over a noncompact real ray uses sigma-compactness,
not compactness, of the target subset. -/
example : IsSigmaCompact ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' Set.Ici (0 : ℝ)) := by
  have hp : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hs : IsSigmaCompact (Set.Ici (0 : ℝ)) :=
    (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set ℝ)).of_isClosed_subset
      isClosed_Ici (Set.subset_univ _)
  exact hp.isSigmaCompact_preimage hs

/-- An empty target subset is permitted for the same proper projection. -/
example : IsSigmaCompact ((Prod.fst : ℝ × Fin 2 → ℝ) ⁻¹' (∅ : Set ℝ)) := by
  exact (isProperMap_fst_of_compactSpace (X := ℝ) (Y := Fin 2)).isSigmaCompact_preimage
    isSigmaCompact_empty

/-- The whole two-sheeted space is sigma-compact by its proper projection to the real line. -/
example : SigmaCompactSpace (ℝ × Fin 2) := by
  exact IsProperMap.sigmaCompactSpace
    (isProperMap_fst_of_compactSpace (X := ℝ) (Y := Fin 2))

/-- The range-relative criterion recovers a compact real interval under the identity. -/
example : IsSigmaCompact ((id : ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) := by
  apply ((isProperMap_id : IsProperMap (id : ℝ → ℝ)).isSigmaCompact_preimage_iff
    (Set.Icc (0 : ℝ) 1)).mpr
  simpa only [Set.range_id, Set.inter_univ] using
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).isSigmaCompact

/-- No sigma-compactness of the target subset is needed outside an empty range. -/
example (s : Set ℝ) : IsSigmaCompact ((fun _ : Empty ↦ (0 : ℝ)) ⁻¹' s) := by
  let : CompactSpace Empty := Finite.compactSpace
  apply ((isProperMap_const (X := Empty) (0 : ℝ)).isSigmaCompact_preimage_iff s).mpr
  simpa only [Set.range_eq_empty, Set.inter_empty] using
    (isSigmaCompact_empty : IsSigmaCompact (∅ : Set ℝ))
