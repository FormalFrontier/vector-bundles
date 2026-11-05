/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinder
public import VectorBundles.Topology.FiberBundle.Pullback
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.VectorBundle.Constructions
import VectorBundles.Topology.FiberBundle.ClosedCylinderSubdivisionDataLinear

/-!
# Linear trivializations near a compact cylinder

A vector bundle over `X × unitInterval` admits, near each `x : X`, a single
fiberwise-linear trivialization whose base set contains a product of an open
neighborhood of `x` with the whole time interval. The space `X` is arbitrary.

`VectorBundle.cylinderTrivialization` chooses the trivialization together with
its linearity condition. `VectorBundle.cylinderTrivializationNhds` is an open
neighborhood on which that same chart is valid at every time. Forward maps,
inverses, and restrictions to closed subsets use `Bundle.Trivialization`'s API,
in particular `preimageHomeomorph`; they do not require a separate bundle object.

## Implementation notes

The scalar field and normed model space have the hypotheses of Mathlib's
`VectorBundle` class. The fibers need only their given additive, module, and
topological structures. There is no completeness or dimension assumption, and
no separation, paracompactness, or nonemptiness assumption on `X`. This is a
local triviality statement, not an endpoint-isomorphism or classification theorem.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.7, preliminary fact (2), printed pp. 20–21.
* Mathlib's `FiberBundle.exists_trivialization_Icc_subset` gives the topological,
  nonparameterized interval statement. Its conclusion does not assert linearity.
* Mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval` supplies a finite
  closed-interval subdivision subordinate to an open cover. Adjacent restricted
  charts are combined by `Bundle.Trivialization.glueClosedCylinder` and its
  fiberwise-linearity theorem.
-/

@[expose] public section

open Bundle Set TopologicalSpace Topology

universe uX uK uF uE uB

namespace VectorBundle

private def totalSpaceProjectionFiberEquiv {B : Type uB}
    (F : Type uF) (E : B → Type uE) (b : B) :
    {z : TotalSpace F E // z.proj = b} ≃ E b where
  toFun := fun z ↦ z.property ▸ z.val.2
  invFun := fun v ↦ ⟨⟨b, v⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b', v⟩, h⟩
    cases h
    rfl
  right_inv := fun _ ↦ rfl

section OpenChart

variable {B : Type*} {F : Type*} {K : Type*}
    [TopologicalSpace B] [TopologicalSpace F] [Semiring K]
    [AddCommMonoid F] [Module K F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]

-- Domain and codomain extension are used only when the entire base subset is open.
private theorem exists_trivialization_of_open_chart (s : Set B) (hs : IsOpen s) (hne : s.Nonempty)
    (hp : Continuous (π F E))
    (h : ((π F E) ⁻¹' s) ≃ₜ s × F)
    (hh : ∀ z, (h z).1.val = z.val.proj)
    (hl : ∀ q (hq : q ∈ s), IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2)) :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧ e.baseSet = s := by
  classical
  let e : Trivialization F (s.restrictPreimage (π F E)) :=
    { toOpenPartialHomeomorph := h.toOpenPartialHomeomorph
      baseSet := univ
      open_baseSet := isOpen_univ
      source_eq := by ext; simp
      target_eq := by simp
      proj_toFun := fun z _ ↦ Subtype.ext (hh z) }
  let g := (e.codExtend hs hne).domExtend (hs.preimage hp)
  have hg : g.baseSet = s := by
    change Subtype.val '' (univ : Set s) = s
    exact Subtype.coe_image_univ s
  refine ⟨g, ?_, hg⟩
  constructor
  intro q hq
  rw [hg] at hq
  have heq : (fun v : E q ↦ (g ⟨q, v⟩).2) =
      (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
    funext v
    change (if ht : q ∈ s then
      ((e.codExtend hs hne) ⟨⟨q, v⟩, ht⟩) else _).2 = _
    rw [dite_eq_left hq]
    rfl
  rw [heq]
  exact hl q hq

end OpenChart

section Cylinder

variable {X : Type uX} [TopologicalSpace X]
  (K : Type uK) [NontriviallyNormedField K]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
  (E : X × unitInterval → Type uE)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
  [FiberBundle F E] [VectorBundle K F E]

/-- A linear chart for a vector bundle over a cylinder contains a whole time
slice and a uniform open neighborhood of it. This is preliminary fact (2) in
Hatcher's proof of Proposition 1.7. -/
theorem exists_trivialization_cylinder (x : X) :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧
      ∃ U : OpenNhdsOf x, (U : Set X) ×ˢ (univ : Set unitInterval) ⊆ e.baseSet := by
  classical
  let q := fun b : X × unitInterval ↦ totalSpaceProjectionFiberEquiv F E b
  let rawAdd := fun b : X × unitInterval ↦ (q b).addCommMonoid
  let rawModule := fun b : X × unitInterval ↦ (q b).addEquiv.module K
  let rho := fun b : X × unitInterval ↦ (q b).addEquiv.linearEquiv K
  let C := fun j : X × unitInterval ↦ trivializationAt F E j
  let W := fun j : X × unitInterval ↦ (C j).baseSet
  let charts := fun j : X × unitInterval ↦
    (C j).preimageHomeomorph (subset_rfl : W j ⊆ (C j).baseSet)
  let L := fun (j b : X × unitInterval) (hb : b ∈ W j) ↦
    (rho b).trans ((C j).continuousLinearEquivAt K b hb).toLinearEquiv
  have hp := FiberBundle.continuous_proj F E
  have hW (j : X × unitInterval) : IsOpen (W j) := (C j).open_baseSet
  have hcover (b : X × unitInterval) : ∃ j, b ∈ W j :=
    ⟨b, mem_baseSet_trivializationAt F E b⟩
  have he (j : X × unitInterval) (z : (π F E) ⁻¹' W j) :
      (charts j z).1.val = z.val.proj := by
    simp only [charts, Trivialization.preimageHomeomorph_apply]
  have hL (j b : X × unitInterval) (hb : b ∈ W j)
      (z : {z : TotalSpace F E // z.proj = b}) :
      L j b hb z =
        (charts j ⟨z.val,
          Eq.mpr (congrArg (fun b ↦ b ∈ W j) z.property) hb⟩).2 := by
    rcases z with ⟨⟨b', v⟩, hz⟩
    change b' = b at hz
    subst b
    change (C j).continuousLinearEquivAt K b' hb v =
      (charts j ⟨⟨b', v⟩, hb⟩).2
    simp [charts, Trivialization.preimageHomeomorph_apply]
  obtain ⟨U, _, _, H, Lambda, hU, hxU, hH, _, _, _, hLambda, _, _⟩ :=
    @Bundle.Trivialization.exists_local_linear_cylinder_homeomorph_of_preimage_charts
      X (TotalSpace F E) (X × unitInterval) K
      ‹TopologicalSpace X› ‹TopologicalSpace (TotalSpace F E)› inferInstance
      (π F E) (fun _ : X × unitInterval ↦ F)
      (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance)
      rawAdd rawModule W charts L hp hW hcover he hL x
  let sourceProduct :
      ((π F E) ⁻¹' (U ×ˢ (univ : Set unitInterval))) ≃ₜ
        {z : TotalSpace F E // z.proj.1 ∈ U} :=
    (Homeomorph.refl (TotalSpace F E)).subtype
      (fun _ ↦ ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, mem_univ _⟩⟩)
  let baseProduct : (U ×ˢ (univ : Set unitInterval)) ≃ₜ U × unitInterval :=
    (Homeomorph.Set.prod U (univ : Set unitInterval)).trans
      ((Homeomorph.refl U).prodCongr (Homeomorph.Set.univ unitInterval))
  let h := sourceProduct.trans
    (H.trans (baseProduct.symm.prodCongr (Homeomorph.refl F)))
  have hh (z : (π F E) ⁻¹' (U ×ˢ (univ : Set unitInterval))) :
      (h z).1.val = z.val.proj := by
    change (((H (sourceProduct z)).1.1 : X), (H (sourceProduct z)).1.2) = z.val.proj
    exact hH (sourceProduct z)
  let originalLinear := fun (u : U) (t : unitInterval) ↦
    (rho (u.val, t)).symm.trans (Lambda u t)
  have hcoord (u : U) (t : unitInterval) (v : E (u.val, t)) :
      (h ⟨⟨(u.val, t), v⟩, u.property, mem_univ t⟩).2 =
        originalLinear u t v := by
    change (H ⟨⟨(u.val, t), v⟩, u.property⟩).2 =
      Lambda u t ((rho (u.val, t)).symm v)
    exact (hLambda u t ((rho (u.val, t)).symm v)).symm
  have hl (b : X × unitInterval) (hb : b ∈ U ×ˢ (univ : Set unitInterval)) :
      IsLinearMap K (fun v : E b ↦ (h ⟨⟨b, v⟩, hb⟩).2) := by
    rcases b with ⟨y, t⟩
    let u : U := ⟨y, hb.1⟩
    have heq : (fun v : E (y, t) ↦ (h ⟨⟨(y, t), v⟩, hb⟩).2) =
        (fun v : E (y, t) ↦ originalLinear u t v) := by
      funext v
      exact hcoord u t v
    rw [heq]
    exact
      { map_add := fun v w ↦ (originalLinear u t).toLinearMap.map_add v w
        map_smul := fun c v ↦ (originalLinear u t).toLinearMap.map_smul c v }
  obtain ⟨e, he, hbase⟩ := exists_trivialization_of_open_chart
    (U ×ˢ (univ : Set unitInterval)) (hU.prod isOpen_univ)
    ⟨(x, 0), hxU, mem_univ _⟩ hp h hh hl
  refine ⟨e, he, ⟨⟨⟨U, hU⟩, hxU⟩, ?_⟩⟩
  rw [hbase]
  exact subset_rfl

/-- A fiberwise-linear trivialization valid near the entire time slice over `x`.
The choice includes linearity, not just the underlying topological chart. -/
noncomputable def cylinderTrivialization (x : X) : Trivialization F (π F E) :=
  Classical.choose (exists_trivialization_cylinder K F E x)

/-- The chosen cylinder chart is linear on every fiber in its base set. -/
instance cylinderTrivialization_isLinear (x : X) :
    (cylinderTrivialization K F E x).IsLinear K := by
  exact (Classical.choose_spec (exists_trivialization_cylinder K F E x)).1

/-- An open neighborhood of `x` on which the chosen chart works for all times. -/
noncomputable def cylinderTrivializationNhds (x : X) : OpenNhdsOf x :=
  Classical.choose (Classical.choose_spec (exists_trivialization_cylinder K F E x)).2

/-- The entire product neighborhood lies in the base set of the chosen chart. -/
theorem cylinderTrivializationNhds_prod_subset (x : X) :
    (cylinderTrivializationNhds K F E x : Set X) ×ˢ (univ : Set unitInterval) ⊆
      (cylinderTrivialization K F E x).baseSet := by
  exact Classical.choose_spec
    (Classical.choose_spec (exists_trivialization_cylinder K F E x)).2

/-- Every time over a point of the chosen open neighborhood belongs to the chart. -/
theorem mem_cylinderTrivialization_baseSet (x : X) {y : X}
    (hy : y ∈ cylinderTrivializationNhds K F E x) (t : unitInterval) :
    (y, t) ∈ (cylinderTrivialization K F E x).baseSet := by
  exact cylinderTrivializationNhds_prod_subset K F E x ⟨hy, mem_univ t⟩

/-- The chosen chart contains the whole time slice over its center. -/
theorem mem_cylinderTrivialization_baseSet_self (x : X) (t : unitInterval) :
    (x, t) ∈ (cylinderTrivialization K F E x).baseSet := by
  exact mem_cylinderTrivialization_baseSet K F E x
    (cylinderTrivializationNhds K F E x).mem t

end Cylinder

section Interval

variable (K : Type uK) [NontriviallyNormedField K]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
  (E : unitInterval → Type uE)
  [TopologicalSpace (TotalSpace F E)] [∀ t, TopologicalSpace (E t)]
  [∀ t, AddCommMonoid (E t)] [∀ t, Module K (E t)]
  [FiberBundle F E] [VectorBundle K F E]

/-- A vector bundle over the unit interval has a global linear trivialization.
Forgetting linearity gives the conclusion of
`FiberBundle.exists_trivialization_Icc_subset F E 0 1`, since the closed interval
between these endpoints is the whole base. No equality of chosen charts is asserted. -/
theorem exists_linearTrivialization_unitInterval :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧ e.baseSet = univ := by
  let f : C(PUnit.{1} × unitInterval, unitInterval) := ⟨Prod.snd, continuous_snd⟩
  let E' := (f : PUnit.{1} × unitInterval → unitInterval) *ᵖ E
  let h : @Homeomorph (TotalSpace F E) (TotalSpace F E')
      ‹TopologicalSpace (TotalSpace F E)› (Pullback.TotalSpace.topologicalSpace F E f) :=
    { toFun := fun z ↦ ⟨(PUnit.unit, z.proj), z.2⟩
      invFun := Pullback.lift f
      left_inv := fun _ ↦ rfl
      right_inv := by rintro ⟨⟨u, t⟩, v⟩; cases u; rfl
      continuous_toFun := by
        apply (inducing_pullbackTotalSpaceEmbedding F E f).continuous_iff.mpr
        exact (continuous_const.prodMk (FiberBundle.continuous_proj F E)).prodMk continuous_id
      continuous_invFun := Pullback.continuous_lift F E f }
  obtain ⟨e, he, U, hU⟩ := exists_trivialization_cylinder K F E' PUnit.unit
  let e' : Trivialization F (π F E) :=
    (e.compHomeomorph h).homeomorphComp (Homeomorph.punitProd unitInterval)
  have hbase (t : unitInterval) : (PUnit.unit, t) ∈ e.baseSet :=
    hU ⟨U.mem, mem_univ t⟩
  refine ⟨e', ?_, ?_⟩
  · let := he
    constructor
    intro t _
    exact e.linear K (hbase t)
  · exact eq_univ_iff_forall.mpr hbase

end Interval

end VectorBundle
