/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Preconnected preimages under open maps

An open map pulls back a preconnected set to a preconnected set when that set lies in
its range and the fibers over that set are preconnected. Continuity and global
surjectivity are not required.

The range condition is essential: the open inclusion of `ℝ \ {0}` into `ℝ` has a
disconnected preimage of the connected set `Set.univ`.

## References

* Mathlib's `IsPreconnected.preimage_of_isOpenMap` and its observation that
  preconnected fibers allow a generalization beyond injective maps.
-/

@[expose] public section

universe u v

namespace IsPreconnected

/-- An open map with preconnected fibers over a preconnected subset of its range has
preconnected preimage of that subset. No continuity assumption is needed. -/
theorem preimage_of_isOpenMap_of_isPreconnected_fibers
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hs : IsPreconnected s) (hf : IsOpenMap f)
    (hsf : s ⊆ Set.range f) (hFib : ∀ y ∈ s, IsPreconnected (f ⁻¹' {y})) :
    IsPreconnected (f ⁻¹' s) := by
  intro U V hU hV hcover hSU hSV
  have himageCover : s ⊆ (f '' U) ∪ (f '' V) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsf hy
    rcases hcover hy with hxU | hxV
    · exact Or.inl ⟨x, hxU, rfl⟩
    · exact Or.inr ⟨x, hxV, rfl⟩
  have himageU : (s ∩ (f '' U)).Nonempty := by
    obtain ⟨x, hxs, hxU⟩ := hSU
    exact ⟨f x, hxs, x, hxU, rfl⟩
  have himageV : (s ∩ (f '' V)).Nonempty := by
    obtain ⟨x, hxs, hxV⟩ := hSV
    exact ⟨f x, hxs, x, hxV, rfl⟩
  obtain ⟨y, hy, ⟨xU, hxU, hfxU⟩, ⟨xV, hxV, hfxV⟩⟩ :=
    hs (f '' U) (f '' V) (hf U hU) (hf V hV) himageCover himageU himageV
  have hfiberCover : f ⁻¹' {y} ⊆ U ∪ V := by
    intro x hx
    have hxy : f x = y := hx
    apply hcover
    change f x ∈ s
    rw [hxy]
    exact hy
  obtain ⟨x, hx, hxU, hxV⟩ :=
    hFib y hy U V hU hV hfiberCover ⟨xU, hfxU, hxU⟩ ⟨xV, hfxV, hxV⟩
  have hxs : f x ∈ s := (show f x = y from hx).symm ▸ hy
  exact ⟨x, hxs, hxU, hxV⟩

end IsPreconnected
