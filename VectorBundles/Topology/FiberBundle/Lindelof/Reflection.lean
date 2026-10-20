/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Separation.Basic

/-!
# Lindelöf reflection to bundle models

A chart over a closed nonempty subset of the ambient base reflects the Lindelöf
property of its original domain to its model. For a fiber bundle, a specified point
of an R₀ base suffices to reflect Lindelöfness of the original total space to the model.
Both statements allow an empty model and retain the given topologies and chart data.

Closedness in the chart statement is ambient closedness in the base, not just relative
closedness in the chart's base set. The bundle statement does not require closed fibers
or a separation assumption on the model.

The statements use Mathlib's bundle trivializations and Lindelöf-space API.
-/

@[expose] public section

universe uB uZ uF uE

namespace Bundle.Trivialization

/-- A trivialization of a continuous map with Lindelöf domain has Lindelöf model if
its base set contains a nonempty subset closed in the original ambient base.
No separation assumption on the base or model is required. Nonemptiness is required
only of the base subset, not of its preimage or of the model. -/
theorem lindelofSpace_model_of_isClosed
    {B : Type uB} {Z : Type uZ} {F : Type uF}
    [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace F]
    {p : Z → B} (e : Bundle.Trivialization F p) (hp : Continuous p)
    [LindelofSpace Z] {s : Set B} (hs : IsClosed s) (hne : s.Nonempty)
    (hsub : s ⊆ e.baseSet) : LindelofSpace F := by
  let : LindelofSpace (p ⁻¹' s) :=
    isLindelof_iff_lindelofSpace.mp (hs.preimage hp).isLindelof
  let : LindelofSpace (s × F) :=
    LindelofSpace.of_continuous_surjective
      (e.preimageHomeomorph hsub).continuous (e.preimageHomeomorph hsub).surjective
  obtain ⟨b, hb⟩ := hne
  let : Nonempty s := ⟨⟨b, hb⟩⟩
  exact LindelofSpace.of_continuous_surjective
    (continuous_snd : Continuous (Prod.snd : s × F → F)) Prod.snd_surjective

end Bundle.Trivialization

namespace FiberBundle

/-- A fiber bundle with Lindelöf total space over an R₀ base has Lindelöf model
at any specified base point. All four topologies and the fiber-bundle structure are
the given ones. The model may be empty; it need not satisfy a separation axiom,
and neither singletons in the base nor fibers are assumed closed. -/
theorem lindelofSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [R0Space B] [LindelofSpace (Bundle.TotalSpace F E)]
    (b : B) : LindelofSpace F := by
  refine (trivializationAt F E b).lindelofSpace_model_of_isClosed
    (continuous_proj F E) (s := closure ({b} : Set B))
    isClosed_closure ⟨b, subset_closure (by rfl)⟩ ?_
  intro x hx
  exact (specializes_iff_mem_closure.mpr hx).symm.mem_open
    (trivializationAt F E b).open_baseSet (mem_baseSet_trivializationAt F E b)

end FiberBundle
