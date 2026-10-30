/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinder
public import VectorBundles.Topology.FiberBundle.PreimageHomeomorph

/-!
# Gluing product charts on a closed slab

For a map `p : Z → X × T`, charts on the original preimages of
`U ×ˢ Icc a c` and `U ×ˢ Icc c b` glue to a product chart on the original
preimage of `U ×ˢ Icc a b`. The two models may have independent universes and
topologies. The result uses the left model and retains the entire left chart,
including the bottom and the seam.

The construction identifies the closed halves of the restricted projection
`p ⁻¹' (U ×ˢ Icc a b) → U × Icc a b` with the original smaller preimages, then
applies `Bundle.Trivialization.glueClosedCylinderHomeomorph`. All spaces carry
their subspace topologies. Only closed order rays are required in `T`, and the
cut may equal either endpoint. Neither the base set nor either model is
assumed nonempty. Continuity of the original projection is supplied separately.

`glueClosedSlabOfPreimageCharts` first restricts two charts over arbitrary base
sets containing the respective closed rectangles. The base sets need not be
open for this restriction; continuity of the original projection is still an
independent input.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
* `Bundle.Trivialization.glueClosedCylinderHomeomorph`, for the closed-cover
  pasting construction and the seam normalization.
-/

@[expose] public section

open Set

universe uX uT uZ uF uG

namespace Bundle.Trivialization

private instance closedIicTopologySubtype {Y : Type*} [TopologicalSpace Y] [Preorder Y]
    [ClosedIicTopology Y] (s : Set Y) : ClosedIicTopology s where
  isClosed_Iic y := (isClosed_Iic (a := y.val)).preimage continuous_subtype_val

private instance closedIciTopologySubtype {Y : Type*} [TopologicalSpace Y] [Preorder Y]
    [ClosedIciTopology Y] (s : Set Y) : ClosedIciTopology s where
  isClosed_Ici y := (isClosed_Ici (a := y.val)).preimage continuous_subtype_val

section Slab

variable {X : Type uX} {T : Type uT} {Z : Type uZ} {F : Type uF} {G : Type uG}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace Z] [TopologicalSpace F] [TopologicalSpace G]

private def closedSlabProjection (p : Z → X × T) (U : Set X) (a b : T) :
    (p ⁻¹' (U ×ˢ Icc a b)) → U × Icc a b :=
  fun z => (⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩)

private theorem continuous_closedSlabProjection (p : Z → X × T) (U : Set X) (a b : T)
    (hp : Continuous p) : Continuous (closedSlabProjection p U a b) :=
  ((hp.comp continuous_subtype_val).fst.subtype_mk _).prodMk
    ((hp.comp continuous_subtype_val).snd.subtype_mk _)

private def closedSlabLeftSource (p : Z → X × T) (U : Set X) (a c b : T)
    (hcb : c ≤ b) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // (p z.val).2 ≤ c} ≃ₜ p ⁻¹' (U ×ˢ Icc a c) :=
  ((Homeomorph.refl (p ⁻¹' (U ×ˢ Icc a b))).subtype
    (p := fun z => (p z.val).2 ≤ c)
    (q := fun z => p z.val ∈ U ×ˢ Icc a c)
    (fun z => ⟨fun hz => ⟨z.property.1, z.property.2.1, hz⟩,
      fun hz => hz.2.2⟩)).trans
    (Homeomorph.subtypeSubtypeEquivSubtype (s := p ⁻¹' (U ×ˢ Icc a b))
      (t := p ⁻¹' (U ×ˢ Icc a c))
      (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hcb⟩))

private def closedSlabRightSource (p : Z → X × T) (U : Set X) (a c b : T)
    (hac : a ≤ c) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // c ≤ (p z.val).2} ≃ₜ p ⁻¹' (U ×ˢ Icc c b) :=
  ((Homeomorph.refl (p ⁻¹' (U ×ˢ Icc a b))).subtype
    (p := fun z => c ≤ (p z.val).2)
    (q := fun z => p z.val ∈ U ×ˢ Icc c b)
    (fun z => ⟨fun hz => ⟨z.property.1, hz, z.property.2.2⟩,
      fun hz => hz.2.1⟩)).trans
    (Homeomorph.subtypeSubtypeEquivSubtype (s := p ⁻¹' (U ×ˢ Icc a b))
      (t := p ⁻¹' (U ×ˢ Icc c b))
      (fun _ hz => ⟨hz.1, hac.trans hz.2.1, hz.2.2⟩))

private def closedSlabLeftBase (U : Set X) (a c b : T) (hcb : c ≤ b) :
    {v : U × Icc a b // (v.2 : T) ≤ c} ≃ₜ U × Icc a c :=
  ((Homeomorph.Set.prod U (Icc a b)).symm.subtype
    (p := fun v => (v.2 : T) ≤ c)
    (q := fun v => v.val ∈ U ×ˢ Icc a c)
    (fun v => ⟨fun ht => ⟨v.1.property, v.2.property.1, ht⟩,
      fun ht => ht.2.2⟩)).trans
    ((Homeomorph.subtypeSubtypeEquivSubtype (s := U ×ˢ Icc a b) (t := U ×ˢ Icc a c)
      (fun _ hv => ⟨hv.1, hv.2.1, hv.2.2.trans hcb⟩)).trans
      (Homeomorph.Set.prod U (Icc a c)))

private def closedSlabRightBase (U : Set X) (a c b : T) (hac : a ≤ c) :
    {v : U × Icc a b // c ≤ (v.2 : T)} ≃ₜ U × Icc c b :=
  ((Homeomorph.Set.prod U (Icc a b)).symm.subtype
    (p := fun v => c ≤ (v.2 : T))
    (q := fun v => v.val ∈ U ×ˢ Icc c b)
    (fun v => ⟨fun ht => ⟨v.1.property, ht, v.2.property.2⟩,
      fun ht => ht.2.1⟩)).trans
    ((Homeomorph.subtypeSubtypeEquivSubtype (s := U ×ˢ Icc a b) (t := U ×ˢ Icc c b)
      (fun _ hv => ⟨hv.1, hac.trans hv.2.1, hv.2.2⟩)).trans
      (Homeomorph.Set.prod U (Icc c b)))

private def closedSlabLeftChart (p : Z → X × T) (U : Set X) (a c b : T)
    (hcb : c ≤ b) (HL : (p ⁻¹' (U ×ˢ Icc a c)) ≃ₜ (U × Icc a c) × F) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // (p z.val).2 ≤ c} ≃ₜ
      {v : U × Icc a b // (v.2 : T) ≤ c} × F :=
  (closedSlabLeftSource p U a c b hcb).trans
    (HL.trans ((closedSlabLeftBase U a c b hcb).symm.prodCongr (Homeomorph.refl F)))

private def closedSlabRightChart (p : Z → X × T) (U : Set X) (a c b : T)
    (hac : a ≤ c) (HR : (p ⁻¹' (U ×ˢ Icc c b)) ≃ₜ (U × Icc c b) × G) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // c ≤ (p z.val).2} ≃ₜ
      {v : U × Icc a b // c ≤ (v.2 : T)} × G :=
  (closedSlabRightSource p U a c b hac).trans
    (HR.trans ((closedSlabRightBase U a c b hac).symm.prodCongr (Homeomorph.refl G)))

private theorem closedSlabLeftChart_base (p : Z → X × T) (U : Set X) (a c b : T)
    (hcb : c ≤ b) (HL : (p ⁻¹' (U ×ˢ Icc a c)) ≃ₜ (U × Icc a c) × F)
    (hpL : ∀ z, (((HL z).1.1 : X), ((HL z).1.2 : T)) = p z.val)
    (z : {z : p ⁻¹' (U ×ˢ Icc a b) // (p z.val).2 ≤ c}) :
    (closedSlabLeftChart p U a c b hcb HL z).1.val =
      closedSlabProjection p U a b z.val := by
  apply Prod.ext
  · apply Subtype.ext
    change ((HL (closedSlabLeftSource p U a c b hcb z)).1.1 : X) = (p z.val.val).1
    exact congrArg Prod.fst (hpL (closedSlabLeftSource p U a c b hcb z))
  · apply Subtype.ext
    change ((HL (closedSlabLeftSource p U a c b hcb z)).1.2 : T) = (p z.val.val).2
    exact congrArg Prod.snd (hpL (closedSlabLeftSource p U a c b hcb z))

private theorem closedSlabRightChart_base (p : Z → X × T) (U : Set X) (a c b : T)
    (hac : a ≤ c) (HR : (p ⁻¹' (U ×ˢ Icc c b)) ≃ₜ (U × Icc c b) × G)
    (hpR : ∀ z, (((HR z).1.1 : X), ((HR z).1.2 : T)) = p z.val)
    (z : {z : p ⁻¹' (U ×ˢ Icc a b) // c ≤ (p z.val).2}) :
    (closedSlabRightChart p U a c b hac HR z).1.val =
      closedSlabProjection p U a b z.val := by
  apply Prod.ext
  · apply Subtype.ext
    change ((HR (closedSlabRightSource p U a c b hac z)).1.1 : X) = (p z.val.val).1
    exact congrArg Prod.fst (hpR (closedSlabRightSource p U a c b hac z))
  · apply Subtype.ext
    change ((HR (closedSlabRightSource p U a c b hac z)).1.2 : T) = (p z.val.val).2
    exact congrArg Prod.snd (hpR (closedSlabRightSource p U a c b hac z))

variable (p : Z → X × T) (U : Set X) (a c b : T) (hac : a ≤ c) (hcb : c ≤ b)
  (HL : (p ⁻¹' (U ×ˢ Icc a c)) ≃ₜ (U × Icc a c) × F)
  (HR : (p ⁻¹' (U ×ˢ Icc c b)) ≃ₜ (U × Icc c b) × G)
  (hpL : ∀ z, (((HL z).1.1 : X), ((HL z).1.2 : T)) = p z.val)
  (hpR : ∀ z, (((HR z).1.1 : X), ((HR z).1.2 : T)) = p z.val)
  [ClosedIicTopology T] [ClosedIciTopology T]

/-- Glue charts on the two original closed-slab preimages, retaining the entire
left chart and using its model. Both endpoint cuts and a repeated cut are allowed. -/
noncomputable def glueClosedSlabHomeomorph (hp : Continuous p) :
    (p ⁻¹' (U ×ˢ Icc a b)) ≃ₜ (U × Icc a b) × F := private_decl% (show
      (p ⁻¹' (U ×ˢ Icc a b)) ≃ₜ (U × Icc a b) × F from
  glueClosedCylinderHomeomorph (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR)
    (continuous_closedSlabProjection p U a b hp))

variable (hp : Continuous p)

/-- On the whole left prefix, including the bottom and seam, the glued chart
keeps the original left fiber coordinate and both original base coordinates. -/
theorem glueClosedSlabHomeomorph_apply_left (z : p ⁻¹' (U ×ˢ Icc a b))
    (hz : (p z.val).2 ≤ c) :
    glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z =
      ((⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩),
        (HL ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2) := by
  exact glueClosedCylinderHomeomorph_apply_left
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR)
    (continuous_closedSlabProjection p U a b hp) z hz

/-- The forward map preserves the base point in the product of subspaces. -/
@[simp] theorem glueClosedSlabHomeomorph_proj (z : p ⁻¹' (U ×ˢ Icc a b)) :
    (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z).1 =
      (⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩) := by
  exact glueClosedCylinderHomeomorph_proj
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR)
    (continuous_closedSlabProjection p U a b hp) z

/-- The forward map preserves the full original base point. -/
theorem glueClosedSlabHomeomorph_apply_base (z : p ⁻¹' (U ×ˢ Icc a b)) :
    (((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z).1.1 : X),
      ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z).1.2 : T)) =
      p z.val := by
  exact congrArg (fun v : U × Icc a b => ((v.1 : X), (v.2 : T)))
    (glueClosedSlabHomeomorph_proj p U a c b hac hcb HL HR hpL hpR hp z)

/-- The inverse preserves the base point in the product of subspaces. -/
theorem glueClosedSlabHomeomorph_symm_proj (w : (U × Icc a b) × F) :
    ((⟨(p ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).val).1,
        ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).property.1⟩,
      ⟨(p ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).val).2,
        ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).property.2⟩) :
      U × Icc a b) = w.1 := by
  let e := glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
  have hb := glueClosedSlabHomeomorph_proj p U a c b hac hcb HL HR hpL hpR hp (e.symm w)
  change (e (e.symm w)).1 = closedSlabProjection p U a b (e.symm w) at hb
  rw [e.apply_symm_apply] at hb
  exact hb.symm

/-- The inverse preserves the full original base point. -/
theorem glueClosedSlabHomeomorph_symm_apply_base (w : (U × Icc a b) × F) :
    p ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).val =
      ((w.1.1 : X), (w.1.2 : T)) := by
  let e := glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
  have hb := glueClosedSlabHomeomorph_apply_base p U a c b hac hcb HL HR hpL hpR hp
    (e.symm w)
  change (((e (e.symm w)).1.1 : X), ((e (e.symm w)).1.2 : T)) = p (e.symm w).val at hb
  rw [e.apply_symm_apply] at hb
  exact hb.symm

/-- At every left time the inverse gives the same point of the original total
space as the original left inverse, with unchanged fiber coordinate. -/
theorem glueClosedSlabHomeomorph_symm_apply_left (w : (U × Icc a b) × F)
    (hw : (w.1.2 : T) ≤ c) :
    ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).val =
      (HL.symm ((w.1.1, ⟨(w.1.2 : T), w.1.2.property.1, hw⟩), w.2)).val := by
  let e := glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
  let v : (U × Icc a c) × F :=
    ((w.1.1, ⟨(w.1.2 : T), w.1.2.property.1, hw⟩), w.2)
  have hz : p (HL.symm v).val = ((w.1.1 : X), (w.1.2 : T)) := by
    have hb := hpL (HL.symm v)
    rw [HL.apply_symm_apply] at hb
    exact hb.symm
  let z : p ⁻¹' (U ×ˢ Icc a b) := ⟨(HL.symm v).val,
    ⟨(HL.symm v).property.1, (HL.symm v).property.2.1,
      (HL.symm v).property.2.2.trans hcb⟩⟩
  have hzl : (p z.val).2 ≤ c := (HL.symm v).property.2.2
  have hf : e z = w := by
    change glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z = w
    rw [glueClosedSlabHomeomorph_apply_left p U a c b hac hcb HL HR hpL hpR hp z hzl]
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hz
      · apply Subtype.ext
        exact congrArg Prod.snd hz
    · change (HL (HL.symm v)).2 = w.2
      exact congrArg Prod.snd (HL.apply_symm_apply v)
  have hi := e.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi

end Slab

section PreimageCharts

variable {X : Type uX} {T : Type uT} {Z : Type uZ} {F : Type uF} {G : Type uG}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace Z] [TopologicalSpace F] [TopologicalSpace G]
  [ClosedIicTopology T] [ClosedIciTopology T]
  (p : Z → X × T) (U : Set X) (a c b : T) (hac : a ≤ c) (hcb : c ≤ b)
  {WL WR : Set (X × T)}
  (eL : (p ⁻¹' WL) ≃ₜ WL × F) (eR : (p ⁻¹' WR) ≃ₜ WR × G)
  (hL : U ×ˢ Icc a c ⊆ WL) (hR : U ×ˢ Icc c b ⊆ WR)
  (heL : ∀ z, (eL z).1.val = p z.val) (heR : ∀ z, (eR z).1.val = p z.val)

/-- Restrict two base-preserving charts to adjoining closed rectangles and glue
on their union in the original total space. The ambient chart bases may differ. -/
noncomputable def glueClosedSlabOfPreimageCharts (hp : Continuous p) :
    (p ⁻¹' (U ×ˢ Icc a b)) ≃ₜ (U × Icc a b) × F :=
  glueClosedSlabHomeomorph p U a c b hac hcb
    (eL.restrictPreimageProd hL heL) (eR.restrictPreimageProd hR heR)
    (fun z => by rw [Homeomorph.restrictPreimageProd_apply])
    (fun z => by rw [Homeomorph.restrictPreimageProd_apply]) hp

/-- The two-chart construction keeps the coordinates of the original left chart
on its whole closed prefix, not just in the interior. -/
theorem glueClosedSlabOfPreimageCharts_apply_left (hp : Continuous p)
    (z : p ⁻¹' (U ×ˢ Icc a b)) (hz : (p z.val).2 ≤ c) :
    glueClosedSlabOfPreimageCharts p U a c b hac hcb eL eR hL hR heL heR hp z =
      ((⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩),
        (eL ⟨z.val, hL ⟨z.property.1, z.property.2.1, hz⟩⟩).2) := by
  simpa only [glueClosedSlabOfPreimageCharts, Homeomorph.restrictPreimageProd_apply] using
    (glueClosedSlabHomeomorph_apply_left p U a c b hac hcb
      (eL.restrictPreimageProd hL heL) (eR.restrictPreimageProd hR heR)
      (fun z => by rw [Homeomorph.restrictPreimageProd_apply])
      (fun z => by rw [Homeomorph.restrictPreimageProd_apply]) hp z hz)

end PreimageCharts

end Bundle.Trivialization
