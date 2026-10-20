/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Maps.Basic

/-!
# Separability of preimages under open maps and open quotient maps

For an open map, the preimage of an ambiently separable set is ambiently separable
if every fiber is separable as a subset of the original domain. In particular, an
open map to a separable space has separable domain when all its fibers are
ambiently separable. For an open quotient map with the same all-fibers hypothesis,
a set has ambiently separable preimage if and only if the set itself is ambiently
separable.

## Scope

Here `TopologicalSpace.IsSeparable s` means that `s` is contained in the closure of
some countable subset of the ambient space. That countable subset need not lie in
`s`, so this hypothesis does not assert `SeparableSpace s` for the subtype topology
or provide a dense subset chosen inside each fiber.

The set-preimage criterion uses the original topologies on both spaces and does
not assume separability of the whole codomain. The ambient countable witness for
`s` may contain points outside `s`, so the fiber hypothesis is quantified over the
whole codomain, not just over `s`. Neither continuity nor surjectivity is required,
and there is no range, nonemptiness, or separation condition. Fibers over points
outside the range are empty and cause no exception.

The whole-codomain theorem gives a `SeparableSpace` conclusion from
`SeparableSpace` of the codomain and the same ambient separability of all fibers.
It likewise requires no continuity or additional range hypothesis.

For `IsOpenQuotientMap.isSeparable_preimage_iff`, the forward implication uses
continuous surjective image, while the reverse implication uses the open-map
preimage criterion. The set is arbitrary: it need not be open, nonempty, or
separable as a subtype, and neither ambient space is assumed separable.

## References

* Mathlib's `TopologicalSpace.IsSeparable` and `TopologicalSpace.IsSeparable.iUnion`
  for ambient countable witnesses and countable unions of fibers.
* Mathlib's `IsOpenMap.preimage_closure_subset_closure_preimage` for the open-map
  closure inclusion underlying the set-preimage criterion, without continuity.
* Mathlib's `isSeparable_closure`, `TopologicalSpace.IsSeparable.mono`, and
  `isSeparable_univ_iff` for the closure and whole-codomain consequences.
* Mathlib's `IsOpenMap.separableSpace_of_injective` for the injective case.
* Mathlib's `IsOpenQuotientMap` and `TopologicalSpace.IsSeparable.image` for
  continuous surjective images in the preimage equivalence.
-/

@[expose] public section

universe u v

open TopologicalSpace

namespace TopologicalSpace.IsSeparable

/-- The preimage of an ambiently separable set under an open map is ambiently
separable if every fiber is ambiently separable in the original domain. The fiber
hypothesis ranges over the whole codomain, since an ambient countable witness for
`s` need not lie in `s`. No global separability of the codomain, continuity,
surjectivity, or range assumption is required. -/
theorem preimage_of_isOpenMap_of_isSeparable_fibers
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hs : TopologicalSpace.IsSeparable s) (hf : IsOpenMap f)
    (hFib : ∀ y : Y, TopologicalSpace.IsSeparable (f ⁻¹' {y})) :
    TopologicalSpace.IsSeparable (f ⁻¹' s) := by
  obtain ⟨C, hCcount, hsC⟩ := hs
  letI : Countable C := hCcount.to_subtype
  have hpreimage : TopologicalSpace.IsSeparable (f ⁻¹' C) := by
    have hdecomp : f ⁻¹' C = ⋃ y : C, f ⁻¹' {y.val} := by
      ext x
      simp
    rw [hdecomp]
    exact TopologicalSpace.IsSeparable.iUnion (fun y : C => hFib y)
  exact (isSeparable_closure.mpr hpreimage).mono
    ((Set.preimage_mono hsC).trans hf.preimage_closure_subset_closure_preimage)

end TopologicalSpace.IsSeparable

namespace IsOpenMap

/-- An open map to a separable space has separable domain when all its fibers are
ambiently separable. No continuity, surjectivity, or range assumption is needed. -/
theorem separableSpace_of_isSeparable_fibers
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [SeparableSpace Y] (hf : IsOpenMap f)
    (hFib : ∀ y : Y, TopologicalSpace.IsSeparable (f ⁻¹' {y})) :
    SeparableSpace X := by
  apply isSeparable_univ_iff.mp
  simpa only [Set.preimage_univ] using
    (TopologicalSpace.IsSeparable.preimage_of_isOpenMap_of_isSeparable_fibers
      (TopologicalSpace.IsSeparable.of_separableSpace (Set.univ : Set Y)) hf hFib)

end IsOpenMap

namespace IsOpenQuotientMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- For an open quotient map with ambiently separable fibers over every codomain
point, an arbitrary set has ambiently separable preimage if and only if it is
ambiently separable. Neither ambient space need be separable. -/
theorem isSeparable_preimage_iff (hf : IsOpenQuotientMap f)
    (hFib : ∀ y : Y, TopologicalSpace.IsSeparable (f ⁻¹' {y})) (s : Set Y) :
    TopologicalSpace.IsSeparable (f ⁻¹' s) ↔ TopologicalSpace.IsSeparable s := by
  constructor
  · intro hs
    simpa only [hf.surjective.image_preimage s] using hs.image hf.continuous
  · intro hs
    exact hs.preimage_of_isOpenMap_of_isSeparable_fibers hf.isOpenMap hFib

end IsOpenQuotientMap
