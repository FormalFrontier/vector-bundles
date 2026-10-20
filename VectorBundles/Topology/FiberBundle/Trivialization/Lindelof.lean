/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Lindelöf preimages inside a bundle trivialization

A sigma-compact subset of a trivialization's base set has Lindelöf preimage
when the model is Lindelöf. The projection and all three topologies are the
original ones; no continuity outside the chart is assumed. Compact supported
subsets are included via `IsCompact.isSigmaCompact`.

The proof applies the mixed Lindelöf/sigma-compact product theorem with the
factors reversed, then transports along a factor swap and the chart
preimage homeomorphism.

## References

* Sébastien Gouëzel and Mathlib contributors,
  `Mathlib.Topology.FiberBundle.Trivialization`: chart preimage homeomorphisms.
* Josha Dekker and Mathlib contributors, `Mathlib.Topology.Compactness.Lindelof`:
  Lindelöf continuous images and the subtype characterization.
* `VectorBundles.Topology.Compactness.Lindelof`: the mixed
  Lindelöf/sigma-compact product theorem.
-/

@[expose] public section

universe uB uF uZ

namespace Bundle.Trivialization

/-- A sigma-compact subset of the base set of an original trivialization has
Lindelöf preimage when its model is Lindelöf. No separation or nonemptiness
hypothesis is needed. -/
theorem isLindelof_preimage
    {B : Type uB} {F : Type uF} {Z : Type uZ}
    [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
    {proj : Z → B} (e : Bundle.Trivialization F proj)
    [LindelofSpace F] (s : Set B) (hs : IsSigmaCompact s)
    (hbase : s ⊆ e.baseSet) : IsLindelof (proj ⁻¹' s) := by
  let : SigmaCompactSpace s := isSigmaCompact_iff_sigmaCompactSpace.mp hs
  have hprod : IsLindelof (Set.univ : Set (F × s)) := by
    simpa only [Set.univ_prod_univ] using
      (isLindelof_univ : IsLindelof (Set.univ : Set F)).prod_of_isSigmaCompact
        (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set s))
  let h : F × s ≃ₜ proj ⁻¹' s :=
    (Homeomorph.prodComm F s).trans (e.preimageHomeomorph hbase).symm
  rw [isLindelof_iff_isLindelof_univ]
  simpa only [Set.image_univ_of_surjective h.surjective] using hprod.image h.continuous

end Bundle.Trivialization
