/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import VectorBundles.Topology.Separable.Basic

/-!
# Separability of fiber-bundle total spaces

A fiber bundle with separable base and model has separable total space. The given
base, model, fiber and total-space topologies and their `FiberBundle` data are
retained.

## Scope

No second-countability, Lindelöf, separation, metric, or nonemptiness assumption is
needed. In particular, an empty model is allowed: every original fiber and the
total space are then empty, even when the base is nonempty. The statement does not
require the bundle projection to be surjective.

The open-map criterion uses ambient `TopologicalSpace.IsSeparable` for subsets of
the total space, not separability inherited by arbitrary subtypes. The
homeomorphism from each original fiber to the model and the continuous fiber
inclusion supply this ambient fiber condition with the given topologies.

## References

* `IsOpenMap.separableSpace_of_isSeparable_fibers` for the open-map criterion.
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
  letI : SeparableSpace (E b) :=
    (homeomorphAt F E b).isOpenMap.separableSpace_of_injective
      (homeomorphAt F E b).injective
  rw [← TotalSpace.range_mk]
  exact isSeparable_range (continuous_totalSpaceMk F E b)

end FiberBundle
