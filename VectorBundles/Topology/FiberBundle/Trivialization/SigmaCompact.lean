/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Sigma-compact preimages inside a bundle trivialization

A sigma-compact subset of a trivialization's base set has sigma-compact preimage
when the model is sigma-compact. The projection and all three topologies are the
given ones; continuity of the projection outside the chart is not required.

## References

The statement uses Mathlib's `Bundle.Trivialization.preimageHomeomorph` and
sigma-compactness APIs. The formulation generalizes the chart-supported compact
subset argument in Formal Frontier's fiber-bundle sigma-compactness development,
which was developed with AI assistance.
-/

@[expose] public section

universe uB uF uZ

namespace Bundle.Trivialization

/-- A sigma-compact subset of a trivialization's base set has sigma-compact preimage
if the model is sigma-compact. No separation or nonemptiness assumption is needed. -/
theorem isSigmaCompact_preimage
    {B : Type uB} {F : Type uF} {Z : Type uZ}
    [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
    {proj : Z → B} (e : Bundle.Trivialization F proj)
    [SigmaCompactSpace F] (s : Set B) (hs : IsSigmaCompact s)
    (hbase : s ⊆ e.baseSet) : IsSigmaCompact (proj ⁻¹' s) := by
  let : SigmaCompactSpace s := isSigmaCompact_iff_sigmaCompactSpace.mp hs
  rw [isSigmaCompact_iff_isSigmaCompact_univ]
  simpa only [Set.image_univ_of_surjective (e.preimageHomeomorph hbase).symm.surjective] using
    (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set (s × F))).image
      (e.preimageHomeomorph hbase).symm.continuous

end Bundle.Trivialization
