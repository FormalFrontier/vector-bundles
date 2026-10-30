/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Trivializations from homeomorphisms of preimages

If `p` is continuous, a projection-preserving homeomorphism `p ⁻¹' U ≃ₜ U × F` over an
open set gives a `Bundle.Trivialization F p` on the original total space. The construction uses
a chosen function `s : X → T` only to define the inverse outside its target. Neither continuity
of `s` nor an identity `p ∘ s = id` is needed.

The resulting trivialization agrees with the given homeomorphism on the preimage of `U`.
In particular, zeroes in the original fibres `p ⁻¹' {x}` supply the required fallback
without any nonemptiness assumption on the base or on the chart domain.
-/

@[expose] public section

open Set

universe uX uT uF

namespace Bundle.Trivialization

variable {X : Type uX} {T : Type uT} {F : Type uF}
variable [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace F] [Zero F]
variable {p : T → X} {U : Set X}

/-- Construct a trivialization on the original total space from a projection-preserving
homeomorphism of the preimage of an open set. The fallback `s` is used only for the inverse
outside `U ×ˢ univ`; it need not be continuous or be a section of `p`.

The forward map is `(p t, (h ⟨t, ht⟩).2)` when `ht : p t ∈ U`, and `(p t, 0)` otherwise.
-/
noncomputable def ofPreimageHomeomorph (hU : IsOpen U) (hp : Continuous p)
    (h : p ⁻¹' U ≃ₜ U × F) (hproj : ∀ t, ((h t).1 : X) = p t) (s : X → T) :
    Trivialization F p := by
  classical
  let e : PartialEquiv T (X × F) :=
    { toFun := fun t ↦ (p t, if ht : p t ∈ U then (h ⟨t, ht⟩).2 else 0)
      invFun := fun y ↦ if hy : y.1 ∈ U then (h.symm (⟨y.1, hy⟩, y.2)).1 else s y.1
      source := p ⁻¹' U
      target := U ×ˢ univ
      map_source' := fun _ ht ↦ ⟨ht, mem_univ _⟩
      map_target' := by
        intro y hy
        change p (if hy : y.1 ∈ U then (h.symm (⟨y.1, hy⟩, y.2)).1 else s y.1) ∈ U
        rw [dite_eq_left hy.1]
        exact (h.symm (⟨y.1, hy.1⟩, y.2)).2
      left_inv' := by
        intro t ht
        change p t ∈ U at ht
        change (if hu : p t ∈ U then
          (h.symm (⟨p t, hu⟩, if ht : p t ∈ U then (h ⟨t, ht⟩).2 else 0)).1
          else s (p t)) = t
        rw [dite_eq_left ht, dite_eq_left ht]
        have heq : (⟨p t, ht⟩, (h ⟨t, ht⟩).2) = h ⟨t, ht⟩ :=
          Prod.ext (Subtype.ext (hproj ⟨t, ht⟩).symm) rfl
        rw [heq]
        exact congrArg Subtype.val (h.symm_apply_apply ⟨t, ht⟩)
      right_inv' := by
        intro y hy
        have hyU : y.1 ∈ U := hy.1
        let z := h.symm (⟨y.1, hyU⟩, y.2)
        have hinv :
            (if hy : y.1 ∈ U then (h.symm (⟨y.1, hy⟩, y.2)).1 else s y.1) = (z : T) := by
          rw [dite_eq_left hyU]
        have hz : h z = (⟨y.1, hyU⟩, y.2) := h.apply_symm_apply _
        have hpz : p (z : T) = y.1 :=
          (hproj z).symm.trans (congrArg (fun w : U × F ↦ (w.1 : X)) hz)
        refine (congrArg
          (fun t : T ↦ (p t, if ht : p t ∈ U then (h ⟨t, ht⟩).2 else 0)) hinv).trans ?_
        have hzU : p (z : T) ∈ U := z.2
        rw [dite_eq_left hzU]
        apply Prod.ext
        · exact hpz
        · exact congrArg (fun w : U × F ↦ w.2) hz }
  have hrestrict : (p ⁻¹' U).domRestrict e =
      (Prod.map (Subtype.val : U → X) id) ∘ h := by
    funext t
    change (p (t : T), if ht : p (t : T) ∈ U then (h ⟨t, ht⟩).2 else 0) =
      (((h t).1 : X), (h t).2)
    have htU : p (t : T) ∈ U := t.2
    rw [dite_eq_left htU]
    exact Prod.ext (hproj t).symm rfl
  refine Trivialization.mk
    (OpenPartialHomeomorph.ofContinuousOpenRestrict e ?_ ?_ (hU.preimage hp))
    U hU rfl rfl ?_
  · apply continuousOn_iff_continuous_domRestrict.mpr
    rw [hrestrict]
    exact (continuous_subtype_val.prodMap continuous_id).comp h.continuous
  · change IsOpenMap ((p ⁻¹' U).domRestrict e)
    rw [hrestrict]
    exact (hU.isOpenMap_subtype_val.prodMap IsOpenMap.id).comp h.isOpenMap
  · intro t _
    rfl

variable (hU : IsOpen U) (hp : Continuous p)
variable (h : p ⁻¹' U ≃ₜ U × F) (hproj : ∀ t, ((h t).1 : X) = p t) (s : X → T)

@[simp]
theorem ofPreimageHomeomorph_baseSet :
    (ofPreimageHomeomorph hU hp h hproj s).baseSet = U :=
  rfl

@[simp]
theorem ofPreimageHomeomorph_source :
    (ofPreimageHomeomorph hU hp h hproj s).source = p ⁻¹' U :=
  rfl

@[simp]
theorem ofPreimageHomeomorph_target :
    (ofPreimageHomeomorph hU hp h hproj s).target = U ×ˢ univ :=
  rfl

/-- On the chart domain the trivialization has exactly the prescribed coordinates. -/
theorem ofPreimageHomeomorph_apply {t : T} (ht : p t ∈ U) :
    ofPreimageHomeomorph hU hp h hproj s t = (p t, (h ⟨t, ht⟩).2) := by
  classical
  change (p t, if ht : p t ∈ U then (h ⟨t, ht⟩).2 else 0) = _
  rw [dite_eq_left ht]

/-- Outside the chart domain the fibre coordinate is zero. -/
theorem ofPreimageHomeomorph_apply_of_not_mem {t : T} (ht : p t ∉ U) :
    ofPreimageHomeomorph hU hp h hproj s t = (p t, 0) := by
  classical
  change (p t, if ht : p t ∈ U then (h ⟨t, ht⟩).2 else 0) = _
  rw [dite_eq_right ht]

/-- The totalized forward map preserves the projection even outside its source. -/
@[simp]
theorem ofPreimageHomeomorph_apply_fst (t : T) :
    (ofPreimageHomeomorph hU hp h hproj s t).1 = p t :=
  rfl

/-- On the target the inverse is the inverse of the given homeomorphism. -/
theorem ofPreimageHomeomorph_symm_apply {x : X} (hx : x ∈ U) (v : F) :
    (ofPreimageHomeomorph hU hp h hproj s).toOpenPartialHomeomorph.symm (x, v) =
      (h.symm (⟨x, hx⟩, v)).1 := by
  classical
  change (if hx : x ∈ U then (h.symm (⟨x, hx⟩, v)).1 else s x) = _
  rw [dite_eq_left hx]

/-- Outside the target the inverse takes the chosen fallback value. -/
theorem ofPreimageHomeomorph_symm_apply_of_not_mem {x : X} (hx : x ∉ U) (v : F) :
    (ofPreimageHomeomorph hU hp h hproj s).toOpenPartialHomeomorph.symm (x, v) = s x := by
  classical
  change (if hx : x ∈ U then (h.symm (⟨x, hx⟩, v)).1 else s x) = _
  rw [dite_eq_right hx]

/-- The inverse over a point in the chart domain lies in that point's original fibre. -/
theorem ofPreimageHomeomorph_proj_symm_apply {x : X} (hx : x ∈ U) (v : F) :
    p ((ofPreimageHomeomorph hU hp h hproj s).toOpenPartialHomeomorph.symm (x, v)) = x := by
  apply (ofPreimageHomeomorph hU hp h hproj s).proj_symm_apply'
  rw [ofPreimageHomeomorph_baseSet]
  exact hx

/-- Restricting the constructed trivialization recovers the given homeomorphism, not just
an isomorphic chart. -/
@[simp]
theorem ofPreimageHomeomorph_preimageHomeomorph :
    (ofPreimageHomeomorph hU hp h hproj s).preimageHomeomorph (s := U) (by
      intro x hx
      rw [ofPreimageHomeomorph_baseSet]
      exact hx) = h := by
  apply Homeomorph.ext
  intro t
  rw [preimageHomeomorph_apply]
  apply Prod.ext
  · exact Subtype.ext (hproj t).symm
  · have htU : p (t : T) ∈ U := t.2
    exact congrArg (fun w : X × F ↦ w.2)
      (ofPreimageHomeomorph_apply hU hp h hproj s htU)

/-- Zeroes in the original fibres provide enough data to extend a preimage chart to a
trivialization. No global section, continuity of fibrewise zero, or nonempty chart domain
has to be supplied separately. -/
theorem exists_trivialization_preimageHomeomorph (hU : IsOpen U) (hp : Continuous p)
    (h : p ⁻¹' U ≃ₜ U × F) (hproj : ∀ t, ((h t).1 : X) = p t)
    [∀ x, Zero (p ⁻¹' {x})] :
    ∃ e : Trivialization F p, ∃ hb : U ⊆ e.baseSet,
      e.baseSet = U ∧ e.preimageHomeomorph hb = h := by
  let s₀ : X → T := fun x ↦ (0 : p ⁻¹' {x}).1
  refine ⟨ofPreimageHomeomorph hU hp h hproj s₀, ?_,
    ofPreimageHomeomorph_baseSet hU hp h hproj s₀, ?_⟩
  · intro x hx
    rw [ofPreimageHomeomorph_baseSet]
    exact hx
  · exact ofPreimageHomeomorph_preimageHomeomorph hU hp h hproj s₀

end Bundle.Trivialization
