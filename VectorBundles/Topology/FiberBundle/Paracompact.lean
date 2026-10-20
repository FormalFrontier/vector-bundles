/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import VectorBundles.Topology.Compactness.Paracompact
public import VectorBundles.Topology.FiberBundle.Proper

/-!
# Paracompact models and total spaces of fiber bundles

A chart of a paracompact total space has paracompact model if its base set contains
a nonempty subset closed in the ambient base and the projection is continuous.
The base patch need not be compact, and the model need not be nonempty or satisfy
any separation axiom.

The closed preimage of the base patch is paracompact by Mathlib's closed-embedding
API. The chart's `Bundle.Trivialization.preimageHomeomorph` identifies this
preimage with the product of the patch and the model. A point of the patch gives
a continuous section of the second projection, so paracompactness passes to the
model by `ParacompactSpace.of_continuous_leftInverse`.

For a fiber bundle over an R₀ base, the closure of a specified base point lies in
its selected chart base set. This is a nonempty ambient-closed patch, and the
bundle's canonical continuous projection supplies the continuity hypothesis.
The given topologies on the base, model, total space, and individual fibers, and
their coupled `FiberBundle` data, are retained throughout.

A fiber bundle with compact model over a paracompact base has paracompact total
space. Its canonical projection is proper, and paracompactness passes to the
domain of a proper map.

## References

* Reid Barton, Yury Kudryashov, and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Paracompact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Paracompact.lean):
  paracompactness of closed subspaces and invariance under homeomorphisms.
* Mathlib contributors,
  [`Mathlib.Topology.FiberBundle.Trivialization`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/FiberBundle/Trivialization.lean):
  the homeomorphism over a subset of a chart base set.
* Mathlib contributors,
  [`Mathlib.Topology.FiberBundle.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/FiberBundle/Basic.lean):
  selected trivializations and continuity of the bundle projection.
-/

@[expose] public section

universe uB uZ uF uE

namespace Bundle.Trivialization

/-- A chart of a paracompact space with continuous projection has paracompact model
if its base set contains a nonempty subset closed in the ambient base. The patch
need not be compact, and no separation or nonemptiness of the model is required. -/
theorem paracompactSpace_model_of_isClosed
    {B : Type uB} {Z : Type uZ} {F : Type uF}
    [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace F]
    {p : Z → B} (e : Bundle.Trivialization F p) (hp : Continuous p)
    [ParacompactSpace Z] {s : Set B} (hs : IsClosed s) (hne : s.Nonempty)
    (hsub : s ⊆ e.baseSet) : ParacompactSpace F := by
  let : ParacompactSpace (p ⁻¹' s) :=
    (hs.preimage hp).isClosedEmbedding_subtypeVal.paracompactSpace
  let : ParacompactSpace (s × F) :=
    (e.preimageHomeomorph hsub).paracompactSpace_iff.mp inferInstance
  obtain ⟨b, hb⟩ := hne
  exact ParacompactSpace.of_continuous_leftInverse
    (r := fun x : s × F => x.2) (j := fun f : F => (⟨b, hb⟩, f))
    continuous_snd (continuous_const.prodMk continuous_id) (fun _ => rfl)

end Bundle.Trivialization

namespace FiberBundle

/-- The model of a bundle with paracompact total space over an R₀ base is
paracompact, provided a base point is specified. All four given topologies and the
coupled bundle structure are retained; no nonemptiness of the model is needed. -/
theorem paracompactSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [R0Space B] [ParacompactSpace (Bundle.TotalSpace F E)]
    (b : B) : ParacompactSpace F := by
  let e := trivializationAt F E b
  refine e.paracompactSpace_model_of_isClosed (continuous_proj F E)
    (s := closure ({b} : Set B)) isClosed_closure ?_ ?_
  · exact ⟨b, subset_closure (Set.mem_singleton b)⟩
  · intro x hx
    have hbx : b ⤳ x := specializes_iff_mem_closure.mpr hx
    exact hbx.symm.mem_open e.open_baseSet (mem_baseSet_trivializationAt F E b)

/-- A fiber bundle with compact model over a paracompact base has paracompact total space. -/
theorem paracompactSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [ParacompactSpace B] [CompactSpace F] :
    ParacompactSpace (Bundle.TotalSpace F E) := by
  exact IsProperMap.paracompactSpace (FiberBundle.isProperMap_proj F E)

end FiberBundle
