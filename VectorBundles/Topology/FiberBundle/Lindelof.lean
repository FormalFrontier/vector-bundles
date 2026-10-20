/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Lindelöf total spaces of fiber bundles

A countable cover by original trivialization base sets that are Lindelöf gives a
Lindelöf total space when the model is σ-compact. In particular, a hereditarily
Lindelöf base and a σ-compact model suffice.

The given topologies on the base, model, total space, and individual fibers, together
with their coupled `FiberBundle` data, are retained. No separation or nonemptiness
assumption is required. The proof transfers Lindelöfness of each original chart target
through its inverse, then takes a countable union of the original chart sources.

These auxiliary bundle arguments follow Mathlib's chosen-trivialization approach in
`Mathlib.Topology.FiberBundle.Basic` and the inverse-chart formalization in
`Mathlib.Topology.FiberBundle.Trivialization`. They combine the product results above
with the continuous-image, countable-union, and countable-subcover API from Mathlib's
Lindelöf formalization by Josha Dekker and contributors.

## References

* Josha Dekker and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Lindelof`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Lindelof.lean):
  Lindelöf images, countable unions, and countable subcovers.
* Mathlib contributors,
  [`Mathlib.Topology.FiberBundle.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/FiberBundle/Basic.lean):
  chosen trivializations and their base-set cover.
* Mathlib contributors,
  [`Mathlib.Topology.FiberBundle.Trivialization`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/FiberBundle/Trivialization.lean):
  chart targets, sources, and inverse partial homeomorphisms.
-/

@[expose] public section

universe uB uF uE

namespace FiberBundle

variable {B : Type uB} {F : Type uF} {E : B → Type uE}
  [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

/-- A countable cover by Lindelöf base sets of the original selected trivializations
and a σ-compact model give a Lindelöf total space. No global Lindelöf assumption on
the base is needed. -/
theorem lindelofSpace_of_countable_trivializationAt_cover [SigmaCompactSpace F]
    (C : Set B) (hC : C.Countable)
    (hcover : (⋃ b ∈ C, (trivializationAt F E b).baseSet) = Set.univ)
    (hL : ∀ b ∈ C, IsLindelof (trivializationAt F E b).baseSet) :
    LindelofSpace (Bundle.TotalSpace F E) := by
  have hsource : ∀ b ∈ C, IsLindelof (trivializationAt F E b).source := by
    intro b hb
    have htarget : IsLindelof (trivializationAt F E b).target := by
      rw [(trivializationAt F E b).target_eq]
      exact (hL b hb).prod_of_isSigmaCompact
        (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set F))
    simpa only [(trivializationAt F E b).toOpenPartialHomeomorph.symm_image_target_eq_source]
      using htarget.image_of_continuousOn
        (trivializationAt F E b).toOpenPartialHomeomorph.continuousOn_symm
  have hsourcecover : (⋃ b ∈ C, (trivializationAt F E b).source) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.proj ∈ ⋃ b ∈ C, (trivializationAt F E b).baseSet := by
      rw [hcover]
      exact Set.mem_univ _
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨b, hb, (trivializationAt F E b).mem_source.mpr hxb⟩
  apply isLindelof_univ_iff.mp
  rw [← hsourcecover]
  exact hC.isLindelof_biUnion hsource

/-- A fiber bundle with hereditarily Lindelöf base and σ-compact model has Lindelöf
original total space. -/
theorem lindelofSpace_of_hereditarilyLindelof [HereditarilyLindelofSpace B]
    [SigmaCompactSpace F] : LindelofSpace (Bundle.TotalSpace F E) := by
  obtain ⟨C, hC, hcover⟩ :=
    (isLindelof_univ : IsLindelof (Set.univ : Set B)).elim_countable_subcover
      (fun b : B ↦ (trivializationAt F E b).baseSet)
      (fun b ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ Set.mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F E b⟩)
  refine lindelofSpace_of_countable_trivializationAt_cover (F := F) (E := E) C hC ?_ ?_
  · exact Set.eq_univ_of_forall fun b ↦ hcover (Set.mem_univ b)
  · exact fun b _ ↦ HereditarilyLindelofSpace.isLindelof _

end FiberBundle
