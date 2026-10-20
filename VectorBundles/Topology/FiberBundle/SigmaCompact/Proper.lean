/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.SigmaCompact
public import VectorBundles.Topology.FiberBundle.Proper

/-!
# Sigma-compact total spaces of bundles with compact model

A fiber bundle with compact model over a sigma-compact base has sigma-compact total
space. Its canonical projection is proper, so sigma-compactness passes from the base
to the total space through inverse images of compact sets.

The given topologies on the base, model, total space and individual fibers, together
with their coupled `FiberBundle` structure, are retained. The base, model and fibers
may belong to independent universes. No separation, local compactness, scalar or
nonemptiness assumption is required.

## References

* Mathlib's fiber-bundle development, by Sébastien Gouëzel, Floris van Doorn,
  Heather Macbeth, and contributors.
* `FiberBundle.isProperMap_proj`, the compact-model proper-projection criterion.
* Mathlib's sigma-compactness and proper-map developments, by Johannes Hölzl,
  Mario Carneiro, Yury Kudryashov, Anatole Dedecker, Etienne Marion, and contributors.
-/

@[expose] public section

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle with compact model over a sigma-compact base has sigma-compact total
space, with all four given topologies and the coupled bundle structure retained.
No separation or nonemptiness assumption is needed. -/
theorem sigmaCompactSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SigmaCompactSpace B] [CompactSpace F] :
    SigmaCompactSpace (Bundle.TotalSpace F E) := by
  exact (isProperMap_proj F E).sigmaCompactSpace

end FiberBundle
