/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Joint continuity of bundle coordinate changes

The coordinate-change homeomorphisms of two trivializations form a jointly continuous
family on the intersection of their base sets. The inverse family is jointly continuous
on the same overlap. All spaces and subspaces carry their given topologies.

The proofs use Mathlib's `Bundle.Trivialization.preimageHomeomorph` to pass between
the preimage of the overlap and its product with the fiber. The families themselves
are Mathlib's `Bundle.Trivialization.coordChangeHomeomorph`.
-/

@[expose] public section

universe uB uF uZ

namespace Bundle.Trivialization

variable {B : Type uB} {F : Type uF} {Z : Type uZ}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z] {p : Z → B}

private theorem continuous_coordChange_uncurry_of_subset
    (e e' : Trivialization F p) {s : Set B}
    (he : s ⊆ e.baseSet) (he' : s ⊆ e'.baseSet) :
    Continuous (fun q : s × F ↦ e.coordChange e' q.1.val q.2) := by
  simpa only [Function.comp_def, preimageHomeomorph_apply,
    preimageHomeomorph_symm_apply, coordChange] using
    ((e'.preimageHomeomorph he').continuous.comp
      (e.preimageHomeomorph he).continuous_symm).snd

/-- The coordinate-change homeomorphisms of two trivializations are jointly continuous
in the base point and the fiber coordinate on the overlap of their base sets. -/
theorem continuous_coordChange_uncurry (e e' : Trivialization F p) :
    Continuous (fun q : {b : B // b ∈ e.baseSet ∩ e'.baseSet} × F ↦
      (e.coordChangeHomeomorph e' (b := q.1.val) q.1.prop.1 q.1.prop.2) q.2) := by
  simpa only [coordChangeHomeomorph_coe] using
    continuous_coordChange_uncurry_of_subset e e'
      (s := e.baseSet ∩ e'.baseSet) (fun _ hb ↦ hb.1) (fun _ hb ↦ hb.2)

/-- The inverses of the coordinate-change homeomorphisms are jointly continuous
in the base point and the fiber coordinate on the same overlap. -/
theorem continuous_coordChangeHomeomorph_symm_uncurry (e e' : Trivialization F p) :
    Continuous (fun q : {b : B // b ∈ e.baseSet ∩ e'.baseSet} × F ↦
      (e.coordChangeHomeomorph e' (b := q.1.val) q.1.prop.1 q.1.prop.2).symm q.2) := by
  change Continuous (fun q : {b : B // b ∈ e.baseSet ∩ e'.baseSet} × F ↦
    e'.coordChange e q.1.val q.2)
  exact continuous_coordChange_uncurry_of_subset e' e
    (fun _ hb ↦ hb.2) (fun _ hb ↦ hb.1)

end Bundle.Trivialization
