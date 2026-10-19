/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import VectorBundles.Topology.Connected.Basic

/-!
# Preconnected and connected fiber-bundle total spaces

For a fiber bundle with preconnected model, the preimage of a preconnected subset of
the base is preconnected. In particular, preconnected base and model give a
preconnected total space, and connected base and model give a connected total space.
The given base, model, fiber and total-space topologies and their `FiberBundle` data
are retained.

## Limitations

The preconnectedness statements allow an empty model. The connectedness statement
also requires nonemptiness, as included in `ConnectedSpace`. The model hypothesis
cannot simply be dropped: over a one-point base, the total space is homeomorphic to
the model. Conversely, connectedness of the total space does not imply connectedness
of the model, as connected nontrivial covering spaces show.

## References

* Mathlib's `FiberBundle.isOpenMap_proj`, `FiberBundle.homeomorphAt` and
  `FiberBundle.continuous_totalSpaceMk` APIs.
* Mathlib's preconnected-preimage criterion for injective open maps, generalized in
  `IsPreconnected.preimage_of_isOpenMap_of_isPreconnected_fibers`.
-/

@[expose] public section

universe uB uF uE

open Bundle

namespace FiberBundle

variable {B : Type uB} (F : Type uF) (E : B → Type uE)
  [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [fb : FiberBundle F E]

include fb

/-- With preconnected model, the preimage under the bundle projection of a
preconnected subset of the base is preconnected, including for an empty model. -/
theorem isPreconnected_preimage_proj [PreconnectedSpace F] {s : Set B}
    (hs : IsPreconnected s) :
    IsPreconnected ((TotalSpace.proj (F := F) (E := E)) ⁻¹' s) := by
  classical
  by_cases hF : Nonempty F
  · letI : Nonempty F := hF
    refine hs.preimage_of_isOpenMap_of_isPreconnected_fibers
      (isOpenMap_proj F E) ?_ ?_
    · intro b _
      exact surjective_proj F E b
    · intro b _
      letI : PreconnectedSpace (E b) :=
        (homeomorphAt F E b).symm.surjective.denseRange.preconnectedSpace
          (homeomorphAt F E b).symm.continuous
      simpa only [TotalSpace.range_mk] using
        (isPreconnected_range (continuous_totalSpaceMk F E b))
  · haveI : IsEmpty (TotalSpace F E) :=
      ⟨fun x => hF ⟨(homeomorphAt F E x.proj) x.snd⟩⟩
    have hempty : ((TotalSpace.proj (F := F) (E := E)) ⁻¹' s) = ∅ := by
      ext x
      exact isEmptyElim x
    rw [hempty]
    exact isPreconnected_empty

/-- A fiber bundle with preconnected base and model has preconnected total space.
Neither the base nor the model is required to be nonempty. -/
theorem preconnectedSpace_totalSpace [PreconnectedSpace B] [PreconnectedSpace F] :
    PreconnectedSpace (TotalSpace F E) := by
  refine ⟨?_⟩
  simpa only [Set.preimage_univ] using
    (isPreconnected_preimage_proj F E (s := Set.univ) isPreconnected_univ)

/-- A fiber bundle with connected base and model has connected total space. -/
theorem connectedSpace_totalSpace [ConnectedSpace B] [ConnectedSpace F] :
    ConnectedSpace (TotalSpace F E) := by
  refine
    { toPreconnectedSpace := preconnectedSpace_totalSpace F E
      toNonempty := ?_ }
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  obtain ⟨x, _⟩ := surjective_proj F E b
  exact ⟨x⟩

end FiberBundle
