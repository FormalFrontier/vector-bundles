/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import VectorBundles.Topology.Separable.Basic

/-!
# Separability of fiber bundles

A fiber bundle with separable base and model has separable total space.
Separability of the total space implies separability of the model at any specified
base point. If both base and model are nonempty, separability of the total space
is equivalent to separability of both. The given base, model, fiber and total-space
topologies and their `FiberBundle` data are retained.

## Scope

The construction from separable base and model needs no second-countability,
Lindelöf, separation, metric, or nonemptiness assumption. In particular, an empty
model is allowed: every original fiber and the total space are then empty, even
when the base is nonempty. This direction does not require the bundle projection
to be surjective.

Model reflection uses a specified base point, not a global nonempty-base
hypothesis, and allows an empty model. Its geometric route is through an open
chart in the original total space and the continuous surjective model-coordinate
projection from that chart. It does not use separability of arbitrary subspaces.
Base reflection for a nonempty model is the stock expression
`(FiberBundle.isQuotientMap_proj F E).separableSpace`.

The global equivalence requires both base and model to be nonempty. An empty
base makes the total space empty independently of the model; an empty model makes
it empty independently of the base. These are explicit theorems, not backward
typeclass instances.

The open-map criterion uses ambient `TopologicalSpace.IsSeparable` for subsets of
the total space, not separability inherited by arbitrary subtypes. The
homeomorphism from each original fiber to the model and the continuous fiber
inclusion supply this ambient fiber condition with the given topologies. Together
with a nonempty separable model and the generic open-quotient preimage equivalence,
they also characterize ambient separability of the projection preimage of any
base subset. No openness or nonemptiness of that subset is needed.

## References

* `IsOpenMap.separableSpace_of_isSeparable_fibers` for the open-map criterion.
* `IsOpenQuotientMap.isSeparable_preimage_iff` for ambient subset reflection.
* Mathlib's `FiberBundle.trivializationAt`,
  `Bundle.Trivialization.sourceHomeomorphBaseSetProd` and
  `DenseRange.separableSpace` for the open-chart model-coordinate route.
* Mathlib's `FiberBundle.isQuotientMap_proj` and
  `Topology.IsQuotientMap.separableSpace` for base reflection.
* Mathlib's `FiberBundle.isOpenMap_proj`, `FiberBundle.homeomorphAt` and
  `FiberBundle.continuous_totalSpaceMk` for the original bundle projection and fibers.
* Mathlib's `Bundle.TotalSpace.range_mk` and `TopologicalSpace.isSeparable_range`
  for ambient separability of the projection fibers.
-/

@[expose] public section

universe uB uF uE

open Bundle TopologicalSpace

namespace FiberBundle

variable {B : Type uB} (F : Type uF) (E : B → Type uE)
  [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [fb : FiberBundle F E]

include fb

/-- A fiber bundle with separable base and model has separable total space, with
its given topologies and bundle structure. The model may be empty. -/
theorem separableSpace_totalSpace [SeparableSpace B] [SeparableSpace F] :
    SeparableSpace (TotalSpace F E) := by
  apply (isOpenMap_proj F E).separableSpace_of_isSeparable_fibers
  intro b
  let : SeparableSpace (E b) :=
    (homeomorphAt F E b).isOpenMap.separableSpace_of_injective
      (homeomorphAt F E b).injective
  rw [← TotalSpace.range_mk]
  exact isSeparable_range (continuous_totalSpaceMk F E b)

end FiberBundle

namespace FiberBundle

variable {B : Type uB} (F : Type uF) (E : B → Type uE)
  [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [fb : FiberBundle F E]

include fb

/-- A separable total space has separable model at any specified base point, with
all original topologies and bundle data. The model may be empty. -/
theorem separableSpace_model (b : B) [SeparableSpace (TotalSpace F E)] :
    SeparableSpace F := by
  let e := trivializationAt F E b
  let : SeparableSpace e.source :=
    e.open_source.isOpenMap_subtype_val.separableSpace_of_injective
      Subtype.val_injective
  let : SeparableSpace (e.baseSet × F) :=
    e.sourceHomeomorphBaseSetProd.surjective.denseRange.separableSpace
      e.sourceHomeomorphBaseSetProd.continuous
  let : Nonempty e.baseSet := ⟨⟨b, mem_baseSet_trivializationAt F E b⟩⟩
  exact (Prod.snd_surjective (α := e.baseSet) (β := F)).denseRange.separableSpace
    continuous_snd

/-- For nonempty base and model, the original total space is separable if and
only if both base and model are separable. -/
theorem separableSpace_totalSpace_iff [Nonempty B] [Nonempty F] :
    SeparableSpace (TotalSpace F E) ↔ (SeparableSpace B ∧ SeparableSpace F) := by
  constructor
  · intro h
    let : SeparableSpace (TotalSpace F E) := h
    exact ⟨(FiberBundle.isQuotientMap_proj F E).separableSpace,
      FiberBundle.separableSpace_model F E (Classical.choice ‹Nonempty B›)⟩
  · rintro ⟨hB, hF⟩
    let : SeparableSpace B := hB
    let : SeparableSpace F := hF
    exact FiberBundle.separableSpace_totalSpace F E

end FiberBundle
