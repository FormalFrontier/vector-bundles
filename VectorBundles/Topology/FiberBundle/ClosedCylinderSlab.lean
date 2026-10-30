/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinder
public import VectorBundles.Topology.FiberBundle.ClosedCylinderLinear
public import VectorBundles.Topology.FiberBundle.PreimageFiber
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

`glueClosedSlabFiberLinearEquiv` refines this same homeomorphism when linear
coordinates on the given original projection fibers agree with the two chart
coordinates. Its algebraic construction and whole-left comparison need no
charts or continuity hypothesis. The forward and inverse fiber formulas,
together with the zero, addition, and scalar-multiplication formulas, use the
coordinate agreement hypotheses.

## Implementation notes

The given additive monoids and modules on the original fibers are unchanged.
Only auxiliary restricted fibers receive the canonical structures from
`PreimageFiber`. The scalar semiring need not be commutative and needs no
topology. No rank, nonemptiness, separation, or continuity of the algebraic
operations is assumed. The linear refinement uses the existing cylinder
linear equivalence and the canonical restricted-fiber equivalence; it does
not make a second topological gluing construction.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1),
  for motivation for closed-slab gluing.
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

/-- The right-to-left seam change for the original slab charts. This is the
coordinate change of the canonical restricted-cylinder construction. -/
noncomputable def closedSlabCoordChange (x : U) : G ≃ₜ F := private_decl% (show G ≃ₜ F from
  closedCylinderCoordChange (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR) x)

omit [ClosedIicTopology T] [ClosedIciTopology T] in
/-- At an original seam point, the seam change takes the original right
coordinate to the original left coordinate. -/
theorem closedSlabCoordChange_apply (x : U) (z : Z) (hz : p z = ((x : X), c)) :
    closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR x
      (HR ⟨z, by change p z ∈ U ×ˢ Icc c b; rw [hz]; exact ⟨x.property, le_rfl, hcb⟩⟩).2 =
    (HL ⟨z, by
      change p z ∈ U ×ˢ Icc a c
      rw [hz]
      exact ⟨x.property, hac, le_rfl⟩⟩).2 := private_decl% (by
  let z' : p ⁻¹' (U ×ˢ Icc a b) :=
    ⟨z, by change p z ∈ U ×ˢ Icc a b; rw [hz]; exact ⟨x.property, hac, hcb⟩⟩
  have hz' : closedSlabProjection p U a b z' = (x, (⟨c, hac, hcb⟩ : Icc a b)) := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hz
    · apply Subtype.ext
      exact congrArg Prod.snd hz
  exact closedCylinderCoordChange_apply
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR) x z' hz')

omit [ClosedIicTopology T] [ClosedIciTopology T] in
/-- The inverse seam change takes original left seam coordinates to original
right seam coordinates. -/
theorem closedSlabCoordChange_symm_apply (x : U) (z : Z) (hz : p z = ((x : X), c)) :
    (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR x).symm
      (HL ⟨z, by change p z ∈ U ×ˢ Icc a c; rw [hz]; exact ⟨x.property, hac, le_rfl⟩⟩).2 =
    (HR ⟨z, by
      change p z ∈ U ×ˢ Icc c b
      rw [hz]
      exact ⟨x.property, le_rfl, hcb⟩⟩).2 := private_decl% (by
  apply (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR x).injective
  rw [Homeomorph.apply_symm_apply]
  exact (closedSlabCoordChange_apply p U a c b hac hcb HL HR hpL hpR x z hz).symm)

omit [ClosedIicTopology T] [ClosedIciTopology T] in
/-- Seam evaluation is jointly continuous in the restricted spatial base and
right coordinate. -/
theorem continuous_closedSlabCoordChange :
    Continuous (fun xv : U × G =>
      closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR xv.1 xv.2) := private_decl% (by
  exact continuous_closedCylinderCoordChange
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR))

omit [ClosedIicTopology T] [ClosedIciTopology T] in
/-- Inverse seam evaluation is jointly continuous. -/
theorem continuous_closedSlabCoordChange_symm :
    Continuous (fun xv : U × F =>
      (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR xv.1).symm xv.2) := private_decl% (by
  exact continuous_closedCylinderCoordChange_symm
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR))

/-- On the whole right slab, use the original right coordinate followed by the
same-spatial-base seam change. The two original base coordinates are unchanged. -/
theorem glueClosedSlabHomeomorph_apply_right (z : p ⁻¹' (U ×ˢ Icc a b))
    (hz : c ≤ (p z.val).2) :
    glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z =
      ((⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩),
        closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR
          ⟨(p z.val).1, z.property.1⟩
          (HR ⟨z.val, ⟨z.property.1, hz, z.property.2.2⟩⟩).2) := private_decl% (by
  exact glueClosedCylinderHomeomorph_apply_right
    (⟨c, hac, hcb⟩ : Icc a b) (closedSlabProjection p U a b)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR)
    (continuous_closedSlabProjection p U a b hp) z hz)

/-- On the whole right slab, undo the same-spatial-base seam change before
applying the original right inverse. This includes the seam and the top. -/
theorem glueClosedSlabHomeomorph_symm_apply_right (w : (U × Icc a b) × F)
    (hw : c ≤ (w.1.2 : T)) :
    ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm w).val =
      (HR.symm ((w.1.1, ⟨(w.1.2 : T), hw, w.1.2.property.2⟩),
        (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR
          w.1.1).symm w.2)).val := private_decl% (by
  let e := glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
  let v : (U × Icc c b) × G :=
    ((w.1.1, ⟨(w.1.2 : T), hw, w.1.2.property.2⟩),
      (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR w.1.1).symm w.2)
  have hz : p (HR.symm v).val = ((w.1.1 : X), (w.1.2 : T)) := by
    have hb := hpR (HR.symm v)
    rw [HR.apply_symm_apply] at hb
    exact hb.symm
  let z : p ⁻¹' (U ×ˢ Icc a b) := ⟨(HR.symm v).val,
    ⟨(HR.symm v).property.1, hac.trans (HR.symm v).property.2.1,
      (HR.symm v).property.2.2⟩⟩
  have hzr : c ≤ (p z.val).2 := (HR.symm v).property.2.1
  have hf : e z = w := by
    change glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp z = w
    rw [glueClosedSlabHomeomorph_apply_right p U a c b hac hcb HL HR hpL hpR hp z hzr]
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hz
      · apply Subtype.ext
        exact congrArg Prod.snd hz
    · have hx : (⟨(p z.val).1, z.property.1⟩ : U) = w.1.1 :=
        Subtype.ext (congrArg Prod.fst hz)
      rw [hx]
      change closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR w.1.1
        (HR (HR.symm v)).2 = w.2
      rw [HR.apply_symm_apply]
      exact (closedSlabCoordChange p U a c b hac hcb HL HR hpL hpR w.1.1).apply_symm_apply w.2
  have hi := e.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi)

section Linear

universe uR

variable {R : Type uR} [Semiring R]
  [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
  [∀ d : X × T, AddCommMonoid {z : Z // p z = d}]
  [∀ d : X × T, Module R {z : Z // p z = d}]
  (Lleft : ∀ (d : X × T), d ∈ U ×ˢ Icc a c → {z : Z // p z = d} ≃ₗ[R] F)
  (Lright : ∀ (d : X × T), d ∈ U ×ˢ Icc c b → {z : Z // p z = d} ≃ₗ[R] G)

private abbrev closedSlabAuxFiberAddCommMonoid :
    ∀ d : U × Icc a b,
      AddCommMonoid {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d} :=
  Set.restrictPreimageFiberAddCommMonoid p (Equiv.Set.prod U (Icc a b))

attribute [local instance] closedSlabAuxFiberAddCommMonoid

private abbrev closedSlabAuxFiberModule :
    ∀ d : U × Icc a b,
      Module R {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d} :=
  Set.restrictPreimageFiberModule R p (Equiv.Set.prod U (Icc a b))

attribute [local instance] closedSlabAuxFiberModule

private def closedSlabAuxFiberBridge (d : U × Icc a b) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d} ≃ₗ[R]
      {z : Z // p z = ((d.1 : X), (d.2 : T))} :=
  LinearEquiv.restrictPreimageFiber R p (Equiv.Set.prod U (Icc a b)) d

private def closedSlabLeftFiberLinearEquiv (d : U × Icc a b)
    (hd : d.2 ≤ (⟨c, hac, hcb⟩ : Icc a b)) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d} ≃ₗ[R] F :=
  (closedSlabAuxFiberBridge (R := R) p U a b d).trans
    (Lleft ((d.1 : X), (d.2 : T)) ⟨d.1.property, d.2.property.1, hd⟩)

private def closedSlabRightFiberLinearEquiv (d : U × Icc a b)
    (hd : (⟨c, hac, hcb⟩ : Icc a b) ≤ d.2) :
    {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d} ≃ₗ[R] G :=
  (closedSlabAuxFiberBridge (R := R) p U a b d).trans
    (Lright ((d.1 : X), (d.2 : T)) ⟨d.1.property, hd, d.2.property.2⟩)

/-- Linear coordinates on each given original projection fiber over the full
slab. Only auxiliary restricted fibers receive transported module structures.
The construction conjugates the cylinder refinement by the canonical
restricted-fiber equivalence and does not glue a second homeomorphism. -/
noncomputable def glueClosedSlabFiberLinearEquiv (d : X × T) (hd : d ∈ U ×ˢ Icc a b) :
    {z : Z // p z = d} ≃ₗ[R] F := private_decl% (show {z : Z // p z = d} ≃ₗ[R] F from
  (closedSlabAuxFiberBridge (R := R) p U a b
    (⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩)).symm.trans
      (glueClosedCylinderFiberLinearEquiv (⟨c, hac, hcb⟩ : Icc a b)
        (closedSlabProjection p U a b)
        (closedSlabLeftFiberLinearEquiv p U a c b hac hcb Lleft)
        (closedSlabRightFiberLinearEquiv p U a c b hac hcb Lright)
        (⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩)))

omit [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
  [TopologicalSpace F] [TopologicalSpace G] [ClosedIicTopology T] [ClosedIciTopology T] in
/-- On every original left fiber, the linear refinement is exactly the supplied
left linear equivalence, including both endpoints of the left slab. -/
theorem glueClosedSlabFiberLinearEquiv_left (d : X × T) (hd : d ∈ U ×ˢ Icc a b)
    (hdl : d ∈ U ×ˢ Icc a c) :
    glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd =
      Lleft d hdl := private_decl% (by
  apply LinearEquiv.ext
  intro v
  let d' : U × Icc a b := (⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩)
  change glueClosedCylinderFiberLinearEquiv (⟨c, hac, hcb⟩ : Icc a b)
    (closedSlabProjection p U a b)
    (closedSlabLeftFiberLinearEquiv p U a c b hac hcb Lleft)
    (closedSlabRightFiberLinearEquiv p U a c b hac hcb Lright) d'
    ((closedSlabAuxFiberBridge (R := R) p U a b d').symm v) = Lleft d hdl v
  rw [glueClosedCylinderFiberLinearEquiv_left (⟨c, hac, hcb⟩ : Icc a b)
    (closedSlabProjection p U a b)
    (closedSlabLeftFiberLinearEquiv p U a c b hac hcb Lleft)
    (closedSlabRightFiberLinearEquiv p U a c b hac hcb Lright) d' hdl.2.2]
  change Lleft d hdl
    ((closedSlabAuxFiberBridge (R := R) p U a b d')
      ((closedSlabAuxFiberBridge (R := R) p U a b d').symm v)) = Lleft d hdl v
  rw [LinearEquiv.apply_symm_apply])

variable
  (hLL : ∀ (d : X × T) (hd : d ∈ U ×ˢ Icc a c) (v : {z : Z // p z = d}),
    Lleft d hd v =
      (HL ⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a c) v.property) hd⟩).2)
  (hLR : ∀ (d : X × T) (hd : d ∈ U ×ˢ Icc c b) (v : {z : Z // p z = d}),
    Lright d hd v =
      (HR ⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc c b) v.property) hd⟩).2)

omit [ClosedIicTopology T] [ClosedIciTopology T] in
include hLL in
private theorem closedSlabLeftFiberLinearEquiv_apply (d : U × Icc a b)
    (hd : d.2 ≤ (⟨c, hac, hcb⟩ : Icc a b))
    (v : {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d}) :
    closedSlabLeftFiberLinearEquiv p U a c b hac hcb Lleft d hd v =
      (closedSlabLeftChart p U a c b hcb HL
        ⟨v.val, Eq.mpr (congrArg
          (fun e : U × Icc a b => e.2 ≤ (⟨c, hac, hcb⟩ : Icc a b)) v.property) hd⟩).2 := by
  refine (hLL ((d.1 : X), (d.2 : T)) ⟨d.1.property, d.2.property.1, hd⟩
    (closedSlabAuxFiberBridge (R := R) p U a b d v)).trans ?_
  apply congrArg (fun z : p ⁻¹' (U ×ˢ Icc a c) => (HL z).2)
  apply Subtype.ext
  change (closedSlabAuxFiberBridge (R := R) p U a b d v).val = v.val.val
  exact LinearEquiv.restrictPreimageFiber_apply_val R p
    (Equiv.Set.prod U (Icc a b)) d v

omit [ClosedIicTopology T] [ClosedIciTopology T] in
include hLR in
private theorem closedSlabRightFiberLinearEquiv_apply (d : U × Icc a b)
    (hd : (⟨c, hac, hcb⟩ : Icc a b) ≤ d.2)
    (v : {z : p ⁻¹' (U ×ˢ Icc a b) // closedSlabProjection p U a b z = d}) :
    closedSlabRightFiberLinearEquiv p U a c b hac hcb Lright d hd v =
      (closedSlabRightChart p U a c b hac HR
        ⟨v.val, Eq.mpr (congrArg
          (fun e : U × Icc a b => (⟨c, hac, hcb⟩ : Icc a b) ≤ e.2) v.property) hd⟩).2 := by
  refine (hLR ((d.1 : X), (d.2 : T)) ⟨d.1.property, hd, d.2.property.2⟩
    (closedSlabAuxFiberBridge (R := R) p U a b d v)).trans ?_
  apply congrArg (fun z : p ⁻¹' (U ×ˢ Icc c b) => (HR z).2)
  apply Subtype.ext
  change (closedSlabAuxFiberBridge (R := R) p U a b d v).val = v.val.val
  exact LinearEquiv.restrictPreimageFiber_apply_val R p
    (Equiv.Set.prod U (Icc a b)) d v

include hLL hLR

/-- The constructed linear coordinates on an original fiber are exactly the
second coordinates of the existing glued slab homeomorphism. -/
theorem glueClosedSlabFiberLinearEquiv_apply (d : X × T) (hd : d ∈ U ×ˢ Icc a b)
    (v : {z : Z // p z = d}) :
    glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd v =
      (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
        ⟨v.val, Eq.mpr
          (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) v.property) hd⟩).2 := private_decl% (by
  let d' : U × Icc a b := (⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩)
  let v' := (closedSlabAuxFiberBridge (R := R) p U a b d').symm v
  have hv : v'.val =
      (⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) v.property) hd⟩ :
        p ⁻¹' (U ×ˢ Icc a b)) := by
    apply Subtype.ext
    exact LinearEquiv.restrictPreimageFiber_symm_apply_val_val R p
      (Equiv.Set.prod U (Icc a b)) d' v
  have h := glueClosedCylinderFiberLinearEquiv_apply (⟨c, hac, hcb⟩ : Icc a b)
    (closedSlabProjection p U a b)
    (closedSlabLeftFiberLinearEquiv p U a c b hac hcb Lleft)
    (closedSlabRightFiberLinearEquiv p U a c b hac hcb Lright)
    (closedSlabLeftChart p U a c b hcb HL) (closedSlabRightChart p U a c b hac HR)
    (closedSlabLeftChart_base p U a c b hcb HL hpL)
    (closedSlabRightChart_base p U a c b hac HR hpR)
    (closedSlabLeftFiberLinearEquiv_apply p U a c b hac hcb HL Lleft hLL)
    (closedSlabRightFiberLinearEquiv_apply p U a c b hac hcb HR Lright hLR)
    (continuous_closedSlabProjection p U a b hp) d' v'
  change glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd v =
    (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp v'.val).2 at h
  rw [hv] at h
  exact h)

/-- The full original slab chart on a given original fiber consists of its
unchanged base and the constructed linear coordinates. -/
theorem glueClosedSlabHomeomorph_apply_fiber (d : X × T) (hd : d ∈ U ×ˢ Icc a b)
    (v : {z : Z // p z = d}) :
    glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
      ⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) v.property) hd⟩ =
      ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩),
        glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd v) := private_decl% (by
  apply Prod.ext
  · rw [glueClosedSlabHomeomorph_proj]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst v.property
    · apply Subtype.ext
      exact congrArg Prod.snd v.property
  · exact (glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd v).symm)

/-- The inverse of the existing slab homeomorphism gives the original total-space
value of the inverse linear coordinate map. No global zero section is used. -/
theorem glueClosedSlabHomeomorph_symm_apply_fiber (d : X × T)
    (hd : d ∈ U ×ˢ Icc a b) (w : F) :
    ((glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp).symm
      ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩), w)).val =
      ((glueClosedSlabFiberLinearEquiv p U a c b hac hcb
        Lleft Lright d hd).symm w).val := private_decl% (by
  let e := glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
  let v := (glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd).symm w
  let z : p ⁻¹' (U ×ˢ Icc a b) :=
    ⟨v.val, Eq.mpr (congrArg (fun f : X × T => f ∈ U ×ˢ Icc a b) v.property) hd⟩
  have hf : e z = ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩), w) := by
    have h := glueClosedSlabHomeomorph_apply_fiber p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd v
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hi := e.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi)

/-- The second coordinate of the slab chart preserves the given zero in each
original projection fiber over the slab. -/
theorem glueClosedSlabHomeomorph_snd_zero (d : X × T) (hd : d ∈ U ×ˢ Icc a b) :
    (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
      ⟨(0 : {z : Z // p z = d}).val,
        Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b)
          (0 : {z : Z // p z = d}).property) hd⟩).2 = 0 := by
  rw [← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
    Lleft Lright hLL hLR d hd (0 : {z : Z // p z = d})]
  exact (glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd).toLinearMap.map_zero

/-- The second coordinate of the slab chart preserves addition in each given
original projection fiber over the slab. -/
theorem glueClosedSlabHomeomorph_snd_add (d : X × T) (hd : d ∈ U ×ˢ Icc a b)
    (v w : {z : Z // p z = d}) :
    (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
      ⟨(v + w).val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b)
        (v + w).property) hd⟩).2 =
      (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
        ⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) v.property) hd⟩).2 +
      (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
        ⟨w.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) w.property) hd⟩).2 := by
  rw [← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd (v + w),
    ← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd v,
    ← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd w]
  exact (glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd).toLinearMap.map_add v w

/-- The second coordinate of the slab chart preserves scalar multiplication in
each given original projection fiber, over an arbitrary semiring. -/
theorem glueClosedSlabHomeomorph_snd_smul (d : X × T) (hd : d ∈ U ×ˢ Icc a b)
    (r : R) (v : {z : Z // p z = d}) :
    (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
      ⟨(r • v).val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b)
        (r • v).property) hd⟩).2 =
      r • (glueClosedSlabHomeomorph p U a c b hac hcb HL HR hpL hpR hp
        ⟨v.val, Eq.mpr (congrArg (fun e : X × T => e ∈ U ×ˢ Icc a b) v.property) hd⟩).2 := by
  rw [← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd (r • v),
    ← glueClosedSlabFiberLinearEquiv_apply p U a c b hac hcb HL HR hpL hpR hp
      Lleft Lright hLL hLR d hd v]
  exact (glueClosedSlabFiberLinearEquiv p U a c b hac hcb Lleft Lright d hd).toLinearMap.map_smul
    r v

end Linear

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
