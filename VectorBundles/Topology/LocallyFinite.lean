/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Maps.Basic

/-!
# Locally finite images under closed maps with compact fibers

A closed map whose point fibers are compact sends any locally finite family of
sets to a locally finite family. The sets need not be open or closed, and the map
need not be continuous, open or surjective. The spaces and the indexing type may
belong to independent universes; no separation or nonemptiness is required.

Compactness gives an open neighborhood of each fiber meeting only finitely many
members of the family. Closedness of the map gives a neighborhood of the target
point whose entire preimage lies in that neighborhood of the fiber. This also
handles empty fibers.

## References

* Yury Kudryashov and Mathlib contributors,
  [`Mathlib.Topology.LocallyFinite`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/LocallyFinite.lean):
  locally finite families and continuous preimages.
* Mathlib contributors,
  [`Mathlib.Topology.Maps.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Basic.lean):
  closed maps and the open kernel-image criterion.
-/

@[expose] public section

universe uX uY uI

/-- A closed map with compact point fibers sends locally finite families to locally
finite families. Neither continuity nor openness of the map or the family is needed. -/
theorem IsClosedMap.locallyFinite_image
    {X : Type uX} {Y : Type uY} {I : Type uI}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedMap f)
    (hcompact : ∀ y : Y, IsCompact (f ⁻¹' ({y} : Set Y)))
    (U : I → Set X) (hU : LocallyFinite U) :
    LocallyFinite (fun i => f '' U i) := by
  classical
  intro y
  let S : Set I := {i | (closure (U i) ∩ f ⁻¹' ({y} : Set Y)).Nonempty}
  have hS : S.Finite := hU.closure.finite_nonempty_inter_compact (hcompact y)
  let C : Set X := ⋃ i : {i // i ∉ S}, closure (U i)
  have hC : IsClosed C :=
    (hU.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun _ => isClosed_closure)
  have hy : y ∉ f '' C := by
    rintro ⟨x, hx, hxy⟩
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact i.property ⟨x, hi, Set.mem_singleton_iff.mpr hxy⟩
  refine ⟨(f '' C)ᶜ, (hf C hC).isOpen_compl.mem_nhds hy, hS.subset ?_⟩
  rintro i ⟨z, ⟨x, hxi, rfl⟩, hz⟩
  by_contra hi
  exact hz ⟨x, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, subset_closure hxi⟩, rfl⟩
