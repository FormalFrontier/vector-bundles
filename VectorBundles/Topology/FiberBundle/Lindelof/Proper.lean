/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import VectorBundles.Topology.FiberBundle.Proper

/-!
# Lindelöf total spaces with compact model fibers

A fiber bundle over a Lindelöf base with compact model fiber has a Lindelöf total space.
The result uses the given topologies on the base, model, total space, and fibers, together with
their `FiberBundle` structure. It requires no separation, local compactness, or nonemptiness
assumptions.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle over a Lindelöf base with compact model fiber has a Lindelöf total space,
with respect to the given total-space topology. -/
theorem lindelofSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [LindelofSpace B] [CompactSpace F] :
    LindelofSpace (TotalSpace F E) := by
  exact isLindelof_univ_iff.mp
    ((FiberBundle.isProperMap_proj F E).isLindelof_preimage
      (isLindelof_univ : IsLindelof (Set.univ : Set B)))

end FiberBundle
