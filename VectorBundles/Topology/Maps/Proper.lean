/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Proper projections of compact-valued correspondences

A subset of a product has proper first projection when its fibers are compact and vary
upper hemicontinuously. All spaces carry their given topologies; neither separation nor
local compactness is required, and the subset need not be closed in the ambient product.

The proof uses Mathlib's upper-hemicontinuity and proper-map APIs. An open subset of the
subtype is the restriction of an ambient open set. Over a fixed compact fiber,
`generalized_tube_lemma` supplies a product neighborhood inside that ambient set. Upper
hemicontinuity keeps nearby fibers inside the second factor of this neighborhood, proving
that the projection is closed. Compactness of its fibers follows by taking continuous
images of the given compact fibers. This tube argument is an independent assembly of the
Mathlib APIs.

## References

* Mathlib's proper-map development, by Anatole Dedecker, Etienne Marion, and contributors,
  including `isProperMap_iff_isClosedMap_and_compact_fibers`.
* Mathlib's hemicontinuity development, by Jireh Loreaux and contributors, including
  `isClosedMap_iff_upperHemicontinuous` and `UpperHemicontinuous.forall_isOpen`.
* Mathlib's compactness development, by Johannes Hölzl, Mario Carneiro, Yury Kudryashov,
  and contributors, including `generalized_tube_lemma`.
-/

@[expose] public section

open Filter Topology

universe uB uF

namespace Set

/-- A compact-valued upper hemicontinuous correspondence has proper graph projection,
with the subspace topology on its graph. No separation assumption or ambient closedness
of the graph is needed. -/
theorem isProperMap_fst_of_upperHemicontinuous
    {B : Type uB} {F : Type uF} [TopologicalSpace B] [TopologicalSpace F]
    {S : Set (B × F)} (hcompact : ∀ b, IsCompact {y : F | (b, y) ∈ S})
    (hupper : UpperHemicontinuous (fun b : B ↦ {y : F | (b, y) ∈ S})) :
    IsProperMap (fun z : S ↦ z.val.1) := by
  have hclosed : IsClosedMap (fun z : S ↦ z.val.1) := by
    apply isClosedMap_iff_upperHemicontinuous.mpr
    apply upperHemicontinuous_iff_forall_isOpen.mpr
    intro b U hU hfiberU
    obtain ⟨W, hW, hWU⟩ := (Topology.IsInducing.subtypeVal (t := S)).isOpen_iff.mp hU
    have hslice : ({b} : Set B) ×ˢ {y : F | (b, y) ∈ S} ⊆ W := by
      rintro ⟨b', y⟩ ⟨hb', hy⟩
      have hb'b : b' = b := mem_singleton_iff.mp hb'
      subst b'
      have hyU : (⟨(b, y), hy⟩ : S) ∈ U := hfiberU rfl
      rw [← hWU] at hyU
      exact hyU
    obtain ⟨V, P, hV, hP, hbV, hKP, hVP⟩ :=
      generalized_tube_lemma isCompact_singleton (hcompact b) hW hslice
    filter_upwards [hV.mem_nhds (hbV (by simp)),
      hupper.forall_isOpen b P hP hKP] with b' hb' hSP
    intro z hz
    have hzbase : z.val.1 = b' := hz
    rw [← hWU]
    change z.val ∈ W
    apply hVP
    constructor
    · rw [hzbase]
      exact hb'
    · apply hSP
      change (b', z.val.2) ∈ S
      rw [← hzbase]
      exact z.property
  have hfiber (b : B) : IsCompact ((fun z : S ↦ z.val.1) ⁻¹' {b}) := by
    let K : Set F := {y : F | (b, y) ∈ S}
    let f : K → S := fun y ↦ ⟨(b, y.val), y.property⟩
    have hf : Continuous f :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have heq : ((fun z : S ↦ z.val.1) ⁻¹' {b}) = f '' univ := by
      ext z
      constructor
      · intro hz
        have hb : z.val.1 = b := hz
        refine ⟨⟨z.val.2, ?_⟩, mem_univ _, ?_⟩
        · change (b, z.val.2) ∈ S
          rw [← hb]
          exact z.property
        · apply Subtype.ext
          change (b, z.val.2) = z.val
          exact Prod.ext hb.symm rfl
      · rintro ⟨y, _, rfl⟩
        rfl
    rw [heq]
    exact (isCompact_iff_isCompact_univ.mp (hcompact b)).image hf
  exact isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_fst.comp continuous_subtype_val, hclosed, hfiber⟩

end Set
