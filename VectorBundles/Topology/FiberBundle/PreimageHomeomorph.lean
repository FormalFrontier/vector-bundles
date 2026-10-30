/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restricting product charts over subsets of the base

`Homeomorph.restrictPreimage` restricts a base-preserving product chart over `W`
to any subset `S ⊆ W`. Both preimages carry their subspace topologies from the
given total space, and both base sets carry their subspace topologies from the
given base. Neither openness nor continuity of the total projection is needed.

The forward map retains the original fiber coordinate. The inverse is the
original chart inverse after inclusion of the smaller base set. The construction
also applies when the base sets or the model fiber are empty.

`Homeomorph.restrictPreimageProd` further expresses a rectangular restricted
base as a product of subspaces. Taking the second set to be a closed interval
gives a chart on the entire corresponding cylinder in the original total space.
-/

@[expose] public section

open Set

namespace Homeomorph

universe uB uZ uF

/-- Flatten nested subspaces when the smaller set is contained in the larger one. -/
def subtypeSubtypeEquivSubtype {Y : Type*} [TopologicalSpace Y] {s t : Set Y}
    (h : t ⊆ s) : {x : s // x.val ∈ t} ≃ₜ t where
  toEquiv := Equiv.subtypeSubtypeEquivSubtype (fun hx ↦ h hx)
  continuous_toFun := by
    change Continuous (fun x : {x : s // x.val ∈ t} => (⟨x.val.val, x.property⟩ : t))
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun x : t =>
      (⟨⟨x.val, h x.property⟩, x.property⟩ : {x : s // x.val ∈ t}))
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Flattening a nested subspace preserves its underlying ambient point. -/
@[simp] theorem subtypeSubtypeEquivSubtype_apply_val {Y : Type*} [TopologicalSpace Y]
    {s t : Set Y} (h : t ⊆ s) (x : {x : s // x.val ∈ t}) :
    (subtypeSubtypeEquivSubtype h x).val = x.val.val := rfl

/-- The inverse inserts the larger-set membership proof without changing the point. -/
@[simp] theorem subtypeSubtypeEquivSubtype_symm_apply_val_val {Y : Type*} [TopologicalSpace Y]
    {s t : Set Y} (h : t ⊆ s) (x : t) :
    ((subtypeSubtypeEquivSubtype h).symm x).val.val = x.val := rfl

private def subtypeFstProd {Y : Type*} {V : Type*}
    [TopologicalSpace Y] [TopologicalSpace V]
    (s : Set Y) : {w : Y × V // w.1 ∈ s} ≃ₜ s × V where
  toEquiv := Equiv.prodSubtypeFstEquivSubtypeProd
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

variable {B : Type uB} {Z : Type uZ} {F : Type uF}
  [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace F]
  {p : Z → B} {W S : Set B}

/-- Restrict a base-preserving product chart over `W` to a subset `S ⊆ W`.

The domain is the preimage of `S` in the given total space, with its subspace
topology. No openness, projection-continuity, or nonempty-model hypothesis is
required. -/
def restrictPreimage (e : (p ⁻¹' W) ≃ₜ W × F) (hSW : S ⊆ W)
    (he : ∀ z : p ⁻¹' W, (e z).1.val = p z.val) : (p ⁻¹' S) ≃ₜ S × F :=
  private_decl% (show (p ⁻¹' S) ≃ₜ S × F from
    (subtypeSubtypeEquivSubtype (s := p ⁻¹' W) (t := p ⁻¹' S)
      (fun _ hz => hSW hz)).symm.trans
      ((e.subtype (p := fun z => p z.val ∈ S) (q := fun w => w.1.val ∈ S)
        (fun z => by rw [he z])).trans
        ((subtypeFstProd {w : W | w.val ∈ S}).trans
          (Homeomorph.prodCongr (subtypeSubtypeEquivSubtype hSW) (Homeomorph.refl F)))))

variable (e : (p ⁻¹' W) ≃ₜ W × F) (hSW : S ⊆ W)
  (he : ∀ z : p ⁻¹' W, (e z).1.val = p z.val)

/-- The restricted chart keeps the full base point and the original fiber coordinate. -/
theorem restrictPreimage_apply (z : p ⁻¹' S) :
    e.restrictPreimage hSW he z =
      (⟨p z.val, z.property⟩, (e ⟨z.val, hSW z.property⟩).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change (e ⟨z.val, hSW z.property⟩).1.val = p z.val
    exact he _
  · rfl

/-- The restricted chart preserves the base point as an element of `S`. -/
@[simp] theorem restrictPreimage_apply_fst (z : p ⁻¹' S) :
    (e.restrictPreimage hSW he z).1 = ⟨p z.val, z.property⟩ :=
  congrArg Prod.fst (e.restrictPreimage_apply hSW he z)

/-- Restriction does not change the fiber coordinate. -/
@[simp] theorem restrictPreimage_apply_snd (z : p ⁻¹' S) :
    (e.restrictPreimage hSW he z).2 = (e ⟨z.val, hSW z.property⟩).2 :=
  congrArg Prod.snd (e.restrictPreimage_apply hSW he z)

/-- Restriction preserves the full base point in the original base space. -/
theorem restrictPreimage_apply_base (z : p ⁻¹' S) :
    (e.restrictPreimage hSW he z).1.val = p z.val := by
  exact congrArg Subtype.val (e.restrictPreimage_apply_fst hSW he z)

/-- The restricted inverse is the original inverse on the same point and fiber coordinate. -/
@[simp] theorem restrictPreimage_symm_apply_val (w : S × F) :
    ((e.restrictPreimage hSW he).symm w).val =
      (e.symm (⟨w.1.val, hSW w.1.property⟩, w.2)).val :=
  private_decl% rfl

/-- Including the restricted inverse into the original chart domain gives the
original chart inverse. -/
theorem restrictPreimage_symm_apply_inclusion (w : S × F) :
    (⟨((e.restrictPreimage hSW he).symm w).val,
      hSW ((e.restrictPreimage hSW he).symm w).property⟩ : p ⁻¹' W) =
      e.symm (⟨w.1.val, hSW w.1.property⟩, w.2) := by
  apply Subtype.ext
  exact e.restrictPreimage_symm_apply_val hSW he w

/-- Applying the original chart to the restricted inverse recovers the included
base point and the unchanged fiber coordinate. -/
theorem restrictPreimage_apply_symm_inclusion (w : S × F) :
    e ⟨((e.restrictPreimage hSW he).symm w).val,
      hSW ((e.restrictPreimage hSW he).symm w).property⟩ =
      (⟨w.1.val, hSW w.1.property⟩, w.2) := by
  rw [e.restrictPreimage_symm_apply_inclusion hSW he w]
  exact e.apply_symm_apply _

/-- The restricted inverse preserves the full base point in the original base space. -/
theorem restrictPreimage_symm_apply_base (w : S × F) :
    p ((e.restrictPreimage hSW he).symm w).val = w.1.val := by
  calc
    p ((e.restrictPreimage hSW he).symm w).val =
        (e ⟨((e.restrictPreimage hSW he).symm w).val,
          hSW ((e.restrictPreimage hSW he).symm w).property⟩).1.val :=
      (he ⟨((e.restrictPreimage hSW he).symm w).val,
        hSW ((e.restrictPreimage hSW he).symm w).property⟩).symm
    _ = w.1.val := congrArg (fun v : W × F => v.1.val)
      (e.restrictPreimage_apply_symm_inclusion hSW he w)

/-- The restricted inverse preserves the base point as an element of `S`. -/
theorem restrictPreimage_symm_apply_fst (w : S × F) :
    (⟨p ((e.restrictPreimage hSW he).symm w).val,
      ((e.restrictPreimage hSW he).symm w).property⟩ : S) = w.1 := by
  apply Subtype.ext
  exact e.restrictPreimage_symm_apply_base hSW he w

section ProductBase

variable {X : Type*} {T : Type*} [TopologicalSpace X] [TopologicalSpace T]
  {q : Z → X × T} {V : Set (X × T)} {U : Set X} {I : Set T}

/-- Restrict a product chart over a set in `X × T` to a rectangular subset,
expressing the restricted base as the product of the two subspaces.

In particular, `I` may be a closed interval with either endpoint equal to the
other. No order or separation hypothesis is needed for this identification. -/
def restrictPreimageProd (e : (q ⁻¹' V) ≃ₜ V × F) (hUI : U ×ˢ I ⊆ V)
    (he : ∀ z : q ⁻¹' V, (e z).1.val = q z.val) :
    (q ⁻¹' (U ×ˢ I)) ≃ₜ (U × I) × F :=
  (e.restrictPreimage hUI he).trans
    ((Homeomorph.Set.prod U I).prodCongr (Homeomorph.refl F))

/-- Rectangular restriction keeps both original base coordinates and the original
fiber coordinate. -/
theorem restrictPreimageProd_apply (e : (q ⁻¹' V) ≃ₜ V × F)
    (hUI : U ×ˢ I ⊆ V) (he : ∀ z : q ⁻¹' V, (e z).1.val = q z.val)
    (z : q ⁻¹' (U ×ˢ I)) :
    e.restrictPreimageProd hUI he z =
      ((⟨(q z.val).1, z.property.1⟩, ⟨(q z.val).2, z.property.2⟩),
        (e ⟨z.val, hUI z.property⟩).2) := by
  change ((Homeomorph.Set.prod U I).prodCongr (Homeomorph.refl F))
    (e.restrictPreimage hUI he z) = _
  rw [e.restrictPreimage_apply hUI he z]
  rfl

/-- The inverse of a rectangular restriction is the original chart inverse at
the same pair of base coordinates and the same fiber coordinate. -/
theorem restrictPreimageProd_symm_apply_val (e : (q ⁻¹' V) ≃ₜ V × F)
    (hUI : U ×ˢ I ⊆ V) (he : ∀ z : q ⁻¹' V, (e z).1.val = q z.val)
    (w : (U × I) × F) :
    ((e.restrictPreimageProd hUI he).symm w).val =
      (e.symm (⟨(w.1.1.val, w.1.2.val),
        hUI ⟨w.1.1.property, w.1.2.property⟩⟩, w.2)).val := by
  change ((e.restrictPreimage hUI he).symm
    ((Homeomorph.Set.prod U I).symm w.1, w.2)).val = _
  exact e.restrictPreimage_symm_apply_val hUI he _

end ProductBase

universe uJ uM

/-- A map with base-preserving product charts is continuous when the chart
sources are open and cover its domain. The base sets need not be open, and the
model spaces may vary with the chart. -/
theorem continuous_of_open_preimage_cover
    {B : Type uB} {Z : Type uZ} {J : Type uJ} {M : J → Type uM}
    [TopologicalSpace B] [TopologicalSpace Z] [∀ j, TopologicalSpace (M j)]
    {p : Z → B} {W : J → Set B}
    (H : ∀ j, (p ⁻¹' W j) ≃ₜ W j × M j)
    (he : ∀ j (z : p ⁻¹' W j), (H j z).1.val = p z.val)
    (hsource : ∀ j, IsOpen (p ⁻¹' W j))
    (hcover : ∀ z, ∃ j, p z ∈ W j) : Continuous p := by
  refine continuous_of_cover_nhds (s := fun j => p ⁻¹' W j) ?_ ?_
  · intro z
    obtain ⟨j, hz⟩ := hcover z
    exact ⟨j, (hsource j).mem_nhds hz⟩
  · intro j
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hlocal : Continuous (fun z : p ⁻¹' W j => (H j z).1.val) :=
      continuous_subtype_val.comp (H j).continuous.fst
    exact hlocal.congr (he j)

end Homeomorph
