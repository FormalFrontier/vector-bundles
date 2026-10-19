/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Local compactness transfer for fiber bundles

Mathlib's `LocallyCompactSpace` requires every neighborhood to contain a compact
neighborhood. Local compactness of the total space from locally compact base and model is
already supplied by Mathlib: `FiberBundle.chartedSpace'` gives charts in `B × F`,
`Prod.locallyCompactSpace` makes this product locally compact, and
`ChartedSpace.locallyCompactSpace` transfers local compactness through the charts.

This file recovers local compactness of the model from a locally compact total space and a
specified base point, and gives the equivalence for nonempty base and model. Both the existing
forward construction and these results use the given topologies on the base, model, total
space, and fibers, together with their `FiberBundle` structure. No scalar, vector-space, or
separation assumption is imposed; the forward construction needs no inhabitation assumption.

## References

* Mathlib's fiber-bundle charted-space structure and local-compactness developments.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- If the total space of a fiber bundle is locally compact and the base has a point, then
the model is locally compact. The model need not be inhabited, and no separation assumption
is needed. A base point is essential: an empty base cannot detect local compactness of the model. -/
theorem locallyCompactSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [LocallyCompactSpace (TotalSpace F E)] (b : B) :
    LocallyCompactSpace F := by
  let e := trivializationAt F E b
  let : LocallyCompactSpace e.source := e.open_source.locallyCompactSpace
  let : LocallyCompactSpace (e.baseSet × F) :=
    e.sourceHomeomorphBaseSetProd.isOpenQuotientMap.locallyCompactSpace
  let : Nonempty e.baseSet := ⟨⟨b, mem_baseSet_trivializationAt F E b⟩⟩
  exact (isOpenQuotientMap_snd (X := e.baseSet) (Y := F)).locallyCompactSpace

/-- For a fiber bundle with nonempty base and model, local compactness of the total space is
equivalent to local compactness of the base and the model. No separation assumption is needed.
An empty base cannot detect the model, and an empty model cannot detect the base. -/
theorem locallyCompactSpace_totalSpace_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [Nonempty B] [Nonempty F] :
    LocallyCompactSpace (TotalSpace F E) ↔ LocallyCompactSpace B ∧ LocallyCompactSpace F := by
  constructor
  · intro htotal
    let : LocallyCompactSpace (TotalSpace F E) := htotal
    obtain ⟨b⟩ := ‹Nonempty B›
    have hproj : IsOpenQuotientMap (TotalSpace.proj (F := F) (E := E)) :=
      ⟨surjective_proj F E, continuous_proj F E, isOpenMap_proj F E⟩
    exact ⟨hproj.locallyCompactSpace, locallyCompactSpace_model F E b⟩
  · rintro ⟨hB, hF⟩
    let : LocallyCompactSpace B := hB
    let : LocallyCompactSpace F := hF
    exact ChartedSpace.locallyCompactSpace (B × F) (TotalSpace F E)

end FiberBundle
