/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Second countability of fiber-bundle total spaces

A fiber bundle with second-countable base and model has second-countable total space.
The given topologies on the base, model, total space, and individual fibers, together with
their coupled `FiberBundle` structure, are retained. Neither the base nor the model needs
to be nonempty, and no separation or vector-space assumptions are needed.

The converse transfers use existing Mathlib APIs. At a specified base point,
`FiberBundle.totalSpaceMk_isEmbedding` reflects second countability to the fiber, and
`FiberBundle.homeomorphAt`, in the reverse orientation, transfers it to the model.
For a nonempty model, the continuous, open, surjective bundle projection gives an
`IsOpenQuotientMap`, whose `Topology.IsOpenQuotientMap.secondCountableTopology` transfers
second countability to the base.

## References

* Mathlib's `TopologicalSpace.countable_cover_nhds` and
  `TopologicalSpace.secondCountableTopology_of_countable_cover`.
* Mathlib's trivializations and `OpenPartialHomeomorph.secondCountableTopology_source`.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- The original total space of a fiber bundle is second-countable when its base and model
are second-countable. No nonemptiness or separation assumption is required. -/
instance secondCountableTopology
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (TotalSpace F E) := by
  -- Select countably many trivializing neighborhoods on the base.
  obtain ⟨s, hs, hcover⟩ :=
    TopologicalSpace.countable_cover_nhds
      (f := fun b : B ↦ (trivializationAt F E b).baseSet)
      (fun b ↦ (trivializationAt F E b).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E b))
  let : Countable s := hs.to_subtype
  -- Each chart source inherits second countability from the original product B × F.
  let : ∀ b : s, SecondCountableTopology (trivializationAt F E b).source :=
    fun b ↦ (trivializationAt F E b).toOpenPartialHomeomorph.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun b : s ↦ (trivializationAt F E b).source)
    (fun b ↦ (trivializationAt F E b).open_source)
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.proj ∈ ⋃ b ∈ s, (trivializationAt F E b).baseSet := by
    rw [hcover]
    exact Set.mem_univ _
  obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, (trivializationAt F E b).mem_source.2 hxb⟩

end FiberBundle
