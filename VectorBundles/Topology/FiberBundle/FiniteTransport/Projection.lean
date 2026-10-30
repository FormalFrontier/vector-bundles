/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.FiniteTransport
public import VectorBundles.Topology.FiberBundle.Pullback
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Topology.UnitInterval

/-!
# Finite cylinder transport for a projection

The fibers of a map `p : T → B` are subtypes of the given space `T`. Their
`Unit`-parametrized total space is equivalent to `T`; the topology induced by
this equivalence is used only on that auxiliary total space. It neither changes
the topology on `T` nor prescribes topologies or algebra on the individual fibers.
The topology definition below is installed as an instance only locally in this
file, never as a default instance for total spaces.

The comparisons retain the standard product and subspace topologies. In
particular, the source of the zero-pullback comparison is the pullback of the
entire zero restriction of `T`, not a chart domain or a stage-dependent carrier.
The slice and identity comparisons use continuity of `p`. Covering original
charts supply that continuity, without an additional continuity assumption on the
cylinder transport.

`Bundle.Trivialization.finiteCylinderTransportOfProjection` applies the finite
ordered family transport to the fibers of an arbitrary given projection. Its
source is the standard product-subspace pullback of the full zero slice and its
target is the original space `T`. The comparison with the nested standard source
uses `Pullback.homeomorphComp`, with continuity of the intermediate spatial
coordinate proved from the standard pullback projection. Both directions preserve
the whole cylinder base point, and every zero-slice point is fixed, including
points in the closed supports. Its application characterization is expressed in
`T` using the original chart lifts: at each increasing index the next point is
the chart lift to the next prefix clock on the closed support, and is unchanged
off that support. `finiteCylinderTransportOfProjection_apply_eq_last` identifies
the result with the last term of any sequence in `T` satisfying these ordered
step equations, at any time, not just at the endpoints. Chart models and their
topologies may vary independently of `T`.

`Bundle.Trivialization.finiteCylinderEndpointTransportOfProjection` compares the
entire original zero and one slices, with their inherited topologies. It uses
the independently ordered endpoint assembly on the projection fibers and the
full-slice comparisons, rather than restricting cylinder transport. The top
application formula identifies the two constructions on every original zero
slice point.

Given modules on the original fibers `{z : T // p z = b}` and the chart models
over a possibly noncommutative semiring `R`, together with matching linear
coordinate equivalences, `finiteCylinderTransportOfProjection_isLinearMap_of_coordinates`
proves linearity of this same transport from the original fiber over `(x, 0)` to
that over `(x, t)`. No replacement fiber algebra is introduced. Real weights
change time only, so `R` needs no topology and the module operations need not be
continuous.

## Limitations

The homeomorphisms use only given finite ordered cylinder charts and continuous
real weights in `[0, 1]`, summing to one, with closures of their cozero sets
subordinate to the auxiliary covering sets `U j`. No normality of `X` or openness
of `U j` is required. No common chart model, rank, finite-dimensionality, field,
separation, nonempty-fiber hypothesis, or additional topology on `T` or its fibers is needed;
the homeomorphisms themselves require no algebra. The `Existence` module supplies
weights from a finite open cylinder-chart cover of a normal space. No independence
from weights or chart order, or homotopy invariance for arbitrary bundles, is
asserted.

## References

- Mathlib supplies `Equiv.sigmaFiberEquiv`, `Equiv.toHomeomorphOfIsInducing`,
  `Bundle.Trivialization.compHomeomorph`, and product/subtype homeomorphisms.
  Its `Mathlib.Data.Bundle`, `Mathlib.Topology.FiberBundle.Trivialization` and
  `Mathlib.Topology.FiberBundle.Constructions` provide the dependent bundle,
  chart and pullback APIs. `Bundle.Pullback.homeomorphProdSubtype` and
  `Bundle.Pullback.homeomorphComp` from
  `VectorBundles.Topology.FiberBundle.Pullback` supply the standard pullback
  comparisons. `Bundle.Trivialization.finiteCylinderTransport` supplies the
  ordered weighted transport and `Bundle.Trivialization.finiteCylinderEndpointTransport`
  its independent endpoint assembly; this module compares their source and target
  with the given projection space and its entire original slices.
- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.7, is a motivating comparison problem only; printed p. 20
  (PDF p. 24) motivates subordinate weights. This finite ordered cylinder-chart
  result allows arbitrary semirings and varying chart models and does not assert
  the full proposition.
-/

open Bundle

universe uA uB uT uF uX uY uι

namespace Bundle.Trivialization

section ProjectionFibers

variable {B : Type uB} {T : Type uT} (p : T → B)

/-- Forget the fiber index using the stock equivalence for the fibers of a map. -/
private def fiberTotalEquiv :
    TotalSpace Unit (fun b ↦ {z : T // p z = b}) ≃ T :=
  (show TotalSpace Unit (fun b ↦ {z : T // p z = b}) ≃
      (Σ b, {z : T // p z = b}) from
    { toFun := fun z ↦ ⟨z.proj, z.snd⟩
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }).trans (Equiv.sigmaFiberEquiv p)

private theorem fiberTotalEquiv_apply
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) :
    fiberTotalEquiv p z = z.snd.val := rfl

private theorem fiberTotalEquiv_symm_apply (z : T) :
    (fiberTotalEquiv p).symm z = ⟨p z, ⟨z, rfl⟩⟩ := rfl

variable [TopologicalSpace T]

/-- Only the auxiliary total space receives the topology induced from `T`. -/
@[instance_reducible]
private def fiberTotalTopology :
    TopologicalSpace (TotalSpace Unit (fun b ↦ {z : T // p z = b})) :=
  TopologicalSpace.induced (fiberTotalEquiv p) inferInstance

attribute [local instance] fiberTotalTopology

/-- The inducing equivalence recovers the given topology of `T`. -/
private def fiberTotalHomeomorph :
    TotalSpace Unit (fun b ↦ {z : T // p z = b}) ≃ₜ T :=
  (fiberTotalEquiv p).toHomeomorphOfIsInducing ⟨rfl⟩

private theorem fiberTotalHomeomorph_apply
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) :
    fiberTotalHomeomorph p z = z.snd.val := rfl

private theorem fiberTotalHomeomorph_symm_apply (z : T) :
    (fiberTotalHomeomorph p).symm z = ⟨p z, ⟨z, rfl⟩⟩ := rfl

/-- Compatibility with the original projection uses the fiber's equality proof. -/
private theorem fiberTotalHomeomorph_proj
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) :
    p (fiberTotalHomeomorph p z) = z.proj :=
  z.snd.property

private theorem fiberTotalHomeomorph_comp :
    p ∘ fiberTotalHomeomorph p = π Unit (fun b ↦ {z : T // p z = b}) :=
  funext (fiberTotalHomeomorph_proj p)

section Charts

variable [TopologicalSpace B] {F : Type uF} [TopologicalSpace F]

/-- Equality transport changes the projection, not the underlying chart. -/
private def congrProjection {Z : Type uA} [TopologicalSpace Z]
    {p₁ p₂ : Z → B} (h : p₁ = p₂) (e : Trivialization F p₁) :
    Trivialization F p₂ :=
  h ▸ e

private theorem congrProjection_baseSet {Z : Type uA} [TopologicalSpace Z]
    {p₁ p₂ : Z → B} (h : p₁ = p₂) (e : Trivialization F p₁) :
    (congrProjection h e).baseSet = e.baseSet := by
  cases h
  rfl

private theorem congrProjection_apply {Z : Type uA} [TopologicalSpace Z]
    {p₁ p₂ : Z → B} (h : p₁ = p₂) (e : Trivialization F p₁) (z : Z) :
    congrProjection h e z = e z := by
  cases h
  rfl

private theorem congrProjection_lift {Z : Type uA} [TopologicalSpace Z]
    {p₁ p₂ : Z → B} (h : p₁ = p₂) (e : Trivialization F p₁) (z : Z) (b : B) :
    (congrProjection h e).lift z b = e.lift z b := by
  cases h
  rfl

/-- Original charts on the canonical total space of projection fibers. -/
private def fiberTrivialization (e : Trivialization F p) :
    Trivialization F (π Unit (fun b ↦ {z : T // p z = b})) :=
  congrProjection (fiberTotalHomeomorph_comp p)
    (e.compHomeomorph (fiberTotalHomeomorph p))

private theorem fiberTrivialization_baseSet (e : Trivialization F p) :
    (fiberTrivialization p e).baseSet = e.baseSet :=
  congrProjection_baseSet (fiberTotalHomeomorph_comp p)
    (e.compHomeomorph (fiberTotalHomeomorph p))

private theorem fiberTrivialization_apply (e : Trivialization F p)
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) :
    fiberTrivialization p e z = e z.snd.val :=
  congrProjection_apply (fiberTotalHomeomorph_comp p)
    (e.compHomeomorph (fiberTotalHomeomorph p)) z

/-- Forgetting the fiber index commutes with the original chart lift, including
its values outside the chart domain. Only the projection is equality-transported. -/
private theorem fiberTrivialization_lift (e : Trivialization F p)
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) (b : B) :
    fiberTotalHomeomorph p ((fiberTrivialization p e).lift z b) =
      e.lift (fiberTotalHomeomorph p z) b := by
  calc
    fiberTotalHomeomorph p ((fiberTrivialization p e).lift z b) =
        fiberTotalHomeomorph p ((e.compHomeomorph (fiberTotalHomeomorph p)).lift z b) :=
      congrArg (fiberTotalHomeomorph p)
        (congrProjection_lift (fiberTotalHomeomorph_comp p)
          (e.compHomeomorph (fiberTotalHomeomorph p)) z b)
    _ = e.lift (fiberTotalHomeomorph p z) b :=
      (fiberTotalHomeomorph p).apply_symm_apply _

/-- Any given coordinate maps retain their agreement with the original chart.
In particular this applies to the given linear equivalences on the same fibers;
no replacement module structure or fiber topology is introduced. -/
private theorem fiberTrivialization_coordinates (e : Trivialization F p)
    (L : ∀ b, b ∈ e.baseSet → {z : T // p z = b} → F)
    (hL : ∀ b hb v, L b hb v = (e v.val).2)
    (b : B) (hb : b ∈ e.baseSet) (v : {z : T // p z = b}) :
    L b hb v = (fiberTrivialization p e ⟨b, v⟩).2 := by
  rw [fiberTrivialization_apply]
  exact hL b hb v

end Charts

section Graphs

variable {A : Type uA} [TopologicalSpace A] (q : A → B)

/-- The standard pullback becomes the graph equality in the original space.
The base map need not be continuous for this comparison. -/
private def pullbackGraphHomeomorph :
    TotalSpace Unit (q *ᵖ (fun b ↦ {z : T // p z = b})) ≃ₜ
      {w : A × T // q w.1 = p w.2} :=
  (Pullback.homeomorphProdSubtype Unit (fun b ↦ {z : T // p z = b}) q).trans
    (((Homeomorph.refl A).prodCongr (fiberTotalHomeomorph p)).subtype
      (fun w ↦ by
        change (q w.1 = w.2.proj) ↔ q w.1 = p (fiberTotalHomeomorph p w.2)
        rw [fiberTotalHomeomorph_proj p w.2]))

private theorem pullbackGraphHomeomorph_apply_val
    (z : TotalSpace Unit (q *ᵖ (fun b ↦ {z : T // p z = b}))) :
    (pullbackGraphHomeomorph p q z).val = (z.proj, z.snd.val) := rfl

private theorem pullbackGraphHomeomorph_symm_proj
    (w : {w : A × T // q w.1 = p w.2}) :
    ((pullbackGraphHomeomorph p q).symm w).proj = w.val.1 := rfl

private theorem pullbackGraphHomeomorph_symm_snd_val
    (w : {w : A × T // q w.1 = p w.2}) :
    ((pullbackGraphHomeomorph p q).symm w).snd.val = w.val.2 := by
  exact congrArg (fun v ↦ v.val.2) ((pullbackGraphHomeomorph p q).apply_symm_apply w)

end Graphs

section Identity

variable [TopologicalSpace B]

/-- The identity graph recovers `T`, using continuity of the original projection. -/
private def graphIdHomeomorph (hp : Continuous p) :
    {w : B × T // w.1 = p w.2} ≃ₜ T where
  toFun w := w.val.2
  invFun z := ⟨(p z, z), rfl⟩
  left_inv := by
    rintro ⟨⟨b, z⟩, h⟩
    apply Subtype.ext
    exact Prod.ext h.symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.snd
  continuous_invFun := (hp.prodMk continuous_id).subtype_mk _

private theorem graphIdHomeomorph_apply (hp : Continuous p)
    (w : {w : B × T // w.1 = p w.2}) :
    graphIdHomeomorph p hp w = w.val.2 := rfl

private theorem graphIdHomeomorph_symm_apply (hp : Continuous p) (z : T) :
    (graphIdHomeomorph p hp).symm z = ⟨(p z, z), rfl⟩ := rfl

/-- The terminal identity pullback is compared with the original total space,
not with a separately topologized reconstruction of it. Its pullback topology is
explicit because the identity-pullback carrier is definitionally the same as the
auxiliary total-space carrier. -/
private def pullbackIdHomeomorph (hp : Continuous p) :
    @Homeomorph (TotalSpace Unit ((id : B → B) *ᵖ (fun b ↦ {z : T // p z = b}))) T
      (@pullbackTopology B Unit (fun b ↦ {z : T // p z = b}) B id
        inferInstance (fiberTotalTopology p)) inferInstance :=
  (pullbackGraphHomeomorph p id).trans (graphIdHomeomorph p hp)

private theorem pullbackIdHomeomorph_apply (hp : Continuous p)
    (z : TotalSpace Unit ((id : B → B) *ᵖ (fun b ↦ {z : T // p z = b}))) :
    pullbackIdHomeomorph p hp z = z.snd.val := rfl

private theorem pullbackIdHomeomorph_symm_proj (hp : Continuous p) (z : T) :
    ((pullbackIdHomeomorph p hp).symm z).proj = p z :=
  pullbackGraphHomeomorph_symm_proj p id ((graphIdHomeomorph p hp).symm z)

private theorem pullbackIdHomeomorph_symm_snd_val (hp : Continuous p) (z : T) :
    ((pullbackIdHomeomorph p hp).symm z).snd.val = z :=
  pullbackGraphHomeomorph_symm_snd_val p id ((graphIdHomeomorph p hp).symm z)

end Identity

end ProjectionFibers

section CoveringCharts

variable {B : Type uB} {T : Type uT} [TopologicalSpace B] [TopologicalSpace T]
    {p : T → B} {ι : Type uι} {F : ι → Type uF} [∀ i, TopologicalSpace (F i)]

/-- A covering family of original charts proves continuity on the given space.
The index is selected only at the point under consideration. -/
private theorem continuous_of_trivialization_cover
    (e : ∀ i, Trivialization (F i) p)
    (hcover : ∀ z, ∃ i, p z ∈ (e i).baseSet) : Continuous p := by
  apply continuous_iff_continuousAt.2
  intro z
  obtain ⟨i, hi⟩ := hcover z
  exact (e i).continuousAt_proj ((e i).mem_source.mpr hi)

end CoveringCharts

section Slices

variable {X : Type uX} {Y : Type uY} {T : Type uT}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    (p : T → X × Y) (a : Y)

/-- Forgetting only the slice proof identifies the standard pullback of the full
slice with the graph of the constant-time base map. No continuity of `p` is used. -/
private def slicePullbackGraphHomeomorph :
    {w : (X × Y) × {z : T // (p z).2 = a} // w.1.1 = (p w.2.val).1} ≃ₜ
      {w : (X × Y) × T // (w.1.1, a) = p w.2} := by
  let S := {w : (X × Y) × {z : T // (p z).2 = a} // w.1.1 = (p w.2.val).1}
  let G := {w : (X × Y) × T // (w.1.1, a) = p w.2}
  let toGraph : S → G := fun w ↦
    ⟨(w.val.1, w.val.2.val),
      show (w.val.1.1, a) = p w.val.2.val from
        Prod.ext w.property w.val.2.property.symm⟩
  let fromGraph : G → S := fun w ↦
    ⟨(w.val.1, ⟨w.val.2, (congrArg (fun b : X × Y ↦ b.2) w.property).symm⟩),
      by
        have hfst := congrArg (fun b : X × Y ↦ b.1) w.property
        exact hfst⟩
  let e : S ≃ G :=
    { toFun := toGraph
      invFun := fromGraph
      left_inv := fun w ↦ by apply Subtype.ext; rfl
      right_inv := fun w ↦ by apply Subtype.ext; rfl }
  refine { toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous toGraph
    exact
      (show Continuous (fun w : S ↦ (w.val.1, w.val.2.val)) from
        continuous_subtype_val.fst.prodMk
          (continuous_subtype_val.comp continuous_subtype_val.snd)).subtype_mk
        (fun w : S ↦
          show (w.val.1.1, a) = p w.val.2.val from (toGraph w).property)
  · change Continuous fromGraph
    exact
      (show Continuous (fun w : G ↦ (w.val.1, (fromGraph w).val.2)) from
        continuous_subtype_val.fst.prodMk
          (continuous_subtype_val.snd.subtype_mk
            (fun w : G ↦
              show (p w.val.2).2 = a from (fromGraph w).val.2.property))).subtype_mk
        (fun w : G ↦
          show w.val.1.1 = (p w.val.2).1 from (fromGraph w).property)

private theorem slicePullbackGraphHomeomorph_apply_val
    (w : {w : (X × Y) × {z : T // (p z).2 = a} // w.1.1 = (p w.2.val).1}) :
    (slicePullbackGraphHomeomorph p a w).val = (w.val.1, w.val.2.val) := rfl

private theorem slicePullbackGraphHomeomorph_symm_apply_val
    (w : {w : (X × Y) × T // (w.1.1, a) = p w.2}) :
    ((slicePullbackGraphHomeomorph p a).symm w).val =
      (w.val.1, ⟨w.val.2, (congrArg Prod.snd w.property).symm⟩) := rfl

/-- The graph of the slice inclusion is the full original slice, with its
subspace topology. The inverse reads the original first base coordinate. -/
private def graphSliceHomeomorph (hp : Continuous p) :
    {w : X × T // (w.1, a) = p w.2} ≃ₜ {z : T // (p z).2 = a} where
  toFun w := ⟨w.val.2, (congrArg Prod.snd w.property).symm⟩
  invFun z := ⟨((p z.val).1, z.val), Prod.ext rfl z.property.symm⟩
  left_inv := by
    rintro ⟨⟨x, z⟩, h⟩
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.fst h).symm rfl
  right_inv z := by apply Subtype.ext; rfl
  continuous_toFun := continuous_subtype_val.snd.subtype_mk _
  continuous_invFun :=
    ((hp.fst.comp continuous_subtype_val).prodMk continuous_subtype_val).subtype_mk _

private theorem graphSliceHomeomorph_apply_val (hp : Continuous p)
    (w : {w : X × T // (w.1, a) = p w.2}) :
    (graphSliceHomeomorph p a hp w).val = w.val.2 := rfl

private theorem graphSliceHomeomorph_symm_apply_val (hp : Continuous p)
    (z : {z : T // (p z).2 = a}) :
    ((graphSliceHomeomorph p a hp).symm z).val = ((p z.val).1, z.val) := rfl

attribute [local instance] fiberTotalTopology

/-- The standard pullback along a slice inclusion is the full original slice. -/
private def pullbackSliceHomeomorph (hp : Continuous p) :
    TotalSpace Unit ((fun x : X ↦ (x, a)) *ᵖ
      (fun b ↦ {z : T // p z = b})) ≃ₜ {z : T // (p z).2 = a} :=
  (pullbackGraphHomeomorph p (fun x : X ↦ (x, a))).trans (graphSliceHomeomorph p a hp)

private theorem pullbackSliceHomeomorph_apply_val (hp : Continuous p)
    (z : TotalSpace Unit ((fun x : X ↦ (x, a)) *ᵖ
      (fun b ↦ {z : T // p z = b}))) :
    (pullbackSliceHomeomorph p a hp z).val = z.snd.val := rfl

private theorem pullbackSliceHomeomorph_symm_proj (hp : Continuous p)
    (z : {z : T // (p z).2 = a}) :
    ((pullbackSliceHomeomorph p a hp).symm z).proj = (p z.val).1 := by
  change ((pullbackGraphHomeomorph p (fun x : X ↦ (x, a))).symm
    ((graphSliceHomeomorph p a hp).symm z)).proj = (p z.val).1
  exact pullbackGraphHomeomorph_symm_proj (A := X) p (fun x : X ↦ (x, a))
    ((graphSliceHomeomorph p a hp).symm z)

private theorem pullbackSliceHomeomorph_symm_snd_val (hp : Continuous p)
    (z : {z : T // (p z).2 = a}) :
    ((pullbackSliceHomeomorph p a hp).symm z).snd.val = z.val := by
  change ((pullbackGraphHomeomorph p (fun x : X ↦ (x, a))).symm
    ((graphSliceHomeomorph p a hp).symm z)).snd.val = z.val
  exact pullbackGraphHomeomorph_symm_snd_val (A := X) p (fun x : X ↦ (x, a))
    ((graphSliceHomeomorph p a hp).symm z)

private theorem pullbackSliceHomeomorph_baseX (hp : Continuous p)
    (z : TotalSpace Unit ((fun x : X ↦ (x, a)) *ᵖ
      (fun b ↦ {z : T // p z = b}))) :
    (p (pullbackSliceHomeomorph p a hp z).val).1 = z.proj := by
  rw [pullbackSliceHomeomorph_apply_val]
  exact congrArg Prod.fst z.snd.property

private theorem pullbackSliceHomeomorph_symm_apply (hp : Continuous p)
    (z : {z : T // (p z).2 = a}) :
    (pullbackSliceHomeomorph p a hp).symm z =
      (⟨(p z.val).1, ⟨z.val, Prod.ext rfl z.property⟩⟩ :
        TotalSpace Unit ((fun x : X ↦ (x, a)) *ᵖ
          (fun b ↦ {z : T // p z = b}))) := by
  apply (pullbackGraphHomeomorph p (fun x : X ↦ (x, a))).injective
  apply Subtype.ext
  change (((pullbackSliceHomeomorph p a hp).symm z).proj,
    ((pullbackSliceHomeomorph p a hp).symm z).snd.val) = ((p z.val).1, z.val)
  exact Prod.ext (pullbackSliceHomeomorph_symm_proj p a hp z)
    (pullbackSliceHomeomorph_symm_snd_val p a hp z)

end Slices

section ZeroPullback

variable {X : Type uX} {T : Type uT} [TopologicalSpace X] [TopologicalSpace T]
    (p : T → X × unitInterval)

attribute [local instance] fiberTotalTopology

/-- The fixed standard pullback of the full zero restriction, compared with the
zero-time pullback of projection fibers. The source topology is built directly
from the given topology on `T`. -/
private def zeroPullbackHomeomorph :
    {w : (X × unitInterval) × {z : T // (p z).2 = 0} //
      w.1.1 = (p w.2.val).1} ≃ₜ
      TotalSpace Unit ((fun b : X × unitInterval ↦ (b.1, 0)) *ᵖ
        (fun b ↦ {z : T // p z = b})) :=
  (slicePullbackGraphHomeomorph p 0).trans
    (pullbackGraphHomeomorph p (fun b : X × unitInterval ↦ (b.1, 0))).symm

private theorem zeroPullbackHomeomorph_proj
    (w : {w : (X × unitInterval) × {z : T // (p z).2 = 0} //
      w.1.1 = (p w.2.val).1}) :
    (zeroPullbackHomeomorph p w).proj = w.val.1 := by
  change ((pullbackGraphHomeomorph p
    (fun b : X × unitInterval ↦ (b.1, 0))).symm
      (slicePullbackGraphHomeomorph p 0 w)).proj = w.val.1
  exact pullbackGraphHomeomorph_symm_proj (A := X × unitInterval) p
    (fun b : X × unitInterval ↦ (b.1, 0)) (slicePullbackGraphHomeomorph p 0 w)

private theorem zeroPullbackHomeomorph_snd_val
    (w : {w : (X × unitInterval) × {z : T // (p z).2 = 0} //
      w.1.1 = (p w.2.val).1}) :
    (zeroPullbackHomeomorph p w).snd.val = w.val.2.val := by
  change ((pullbackGraphHomeomorph p
    (fun b : X × unitInterval ↦ (b.1, 0))).symm
      (slicePullbackGraphHomeomorph p 0 w)).snd.val = w.val.2.val
  exact pullbackGraphHomeomorph_symm_snd_val (A := X × unitInterval) p
    (fun b : X × unitInterval ↦ (b.1, 0)) (slicePullbackGraphHomeomorph p 0 w)

end ZeroPullback

end Bundle.Trivialization

@[expose] public section

open Set
open scoped BigOperators unitInterval

namespace Bundle.Trivialization

section CylinderTransport

variable {X : Type uX} {T : Type uT} [TopologicalSpace X] [TopologicalSpace T]
    (p : T → X × I)

/-- Compare the original zero-slice pullback with the nested standard pullback.
Only the auxiliary total space of projection fibers receives a local topology. -/
private def projectionZeroPullbackHomeomorph :
    letI := fiberTotalTopology p
    {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1} ≃ₜ
      TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
        ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b}))) := by
  letI := fiberTotalTopology p
  exact (zeroPullbackHomeomorph p).trans
    (Pullback.homeomorphComp Unit (fun b ↦ {z : T // p z = b})
      (fun x : X ↦ (x, (0 : I))) (Prod.fst : X × I → X)
      (continuous_fst.comp (Pullback.continuous_proj Unit
        (fun b ↦ {z : T // p z = b})
        ((fun x : X ↦ (x, (0 : I))) ∘ (Prod.fst : X × I → X))))).symm

private theorem projectionZeroPullbackHomeomorph_apply
    (s : {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1}) :
    projectionZeroPullbackHomeomorph p s =
      (⟨s.val.1, ⟨s.val.2.val, Prod.ext s.property.symm s.val.2.property⟩⟩ :
        TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
          ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b})))) := by
  let := fiberTotalTopology p
  change (Pullback.homeomorphComp Unit (fun b ↦ {z : T // p z = b})
    (fun x : X ↦ (x, (0 : I))) (Prod.fst : X × I → X)
    (continuous_fst.comp (Pullback.continuous_proj Unit
      (fun b ↦ {z : T // p z = b})
      ((fun x : X ↦ (x, (0 : I))) ∘ (Prod.fst : X × I → X))))).symm
        (zeroPullbackHomeomorph p s) = _
  rw [Pullback.homeomorphComp_symm_apply]
  have hb := zeroPullbackHomeomorph_proj p s
  have hv := zeroPullbackHomeomorph_snd_val p s
  generalize hy : zeroPullbackHomeomorph p s = y at hb hv ⊢
  rcases y with ⟨b, v⟩
  change b = s.val.1 at hb
  subst b
  exact congrArg (fun v : {z : T // p z = (s.val.1.1, (0 : I))} ↦
    (⟨s.val.1, v⟩ : TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
      ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b})))))
    (Subtype.ext hv)

variable {n : ℕ} {F : Fin n → Type uF} [∀ j, TopologicalSpace (F j)]
    (e : ∀ j, Trivialization (F j) p) (U : Fin n → Set X)
    (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
    (w : Fin n → C(X, ℝ)) (hw : ∀ j x, 0 ≤ w j x ∧ w j x ≤ 1)
    (hsum : ∀ x, ∑ j, w j x = 1)
    (hsupport : ∀ j, closure {x | w j x ≠ 0} ⊆ U j)
    (hcover : (⋃ j, U j) = univ)

/-- Weighted finite cylinder transport for an arbitrary original projection.

The chart steps are those of `finiteCylinderTransport`, in increasing index
order, applied to the projection fibers `{z : T // p z = b}`. The source has the
standard product and subspace topology induced by the given topology of `T`,
and the target is the same original `T`. The models `F j` may vary; no common
model, algebraic structure, separation, nonemptiness, or separate continuity
assumption on `p` is required. -/
noncomputable def finiteCylinderTransportOfProjection :
    {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1} ≃ₜ T :=
  private_decl% (show
    {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1} ≃ₜ T from by
    letI := fiberTotalTopology p
    exact ((projectionZeroPullbackHomeomorph p).trans
      (finiteCylinderTransport (fun j ↦ fiberTrivialization p (e j)) U
        (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
        w hw hsum hsupport hcover)).trans (fiberTotalHomeomorph p))

/-- Transport preserves the entire cylinder base point in the original space. -/
theorem finiteCylinderTransportOfProjection_proj
    (s : {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1}) :
    p (finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover s) =
      s.val.1 := by
  let := fiberTotalTopology p
  change p (fiberTotalHomeomorph p
    (finiteCylinderTransport (fun j ↦ fiberTrivialization p (e j)) U
      (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
      w hw hsum hsupport hcover (projectionZeroPullbackHomeomorph p s))) = _
  simp only [fiberTotalHomeomorph_proj, finiteCylinderTransport_proj,
    projectionZeroPullbackHomeomorph_apply]

/-- The inverse recovers the entire original cylinder base point. -/
@[simp] theorem finiteCylinderTransportOfProjection_symm_proj (z : T) :
    ((finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover).symm z).val.1 =
      p z := by
  have h := finiteCylinderTransportOfProjection_proj p e U hchart w hw hsum hsupport hcover
    ((finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover).symm z)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

/-- Every point of the original zero slice is fixed, including supported points. -/
@[simp] theorem finiteCylinderTransportOfProjection_apply_bottom
    (z : {z : T // (p z).2 = 0}) :
    finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover
      ⟨(((p z.val).1, 0), z), rfl⟩ = z.val := by
  let := fiberTotalTopology p
  change fiberTotalHomeomorph p
    (finiteCylinderTransport (fun j ↦ fiberTrivialization p (e j)) U
      (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
      w hw hsum hsupport hcover
      (projectionZeroPullbackHomeomorph p ⟨(((p z.val).1, 0), z), rfl⟩)) = _
  rw [projectionZeroPullbackHomeomorph_apply, finiteCylinderTransport_apply_bottom]
  rfl

/-- Any source point over zero time is sent to its given zero-slice point. -/
theorem finiteCylinderTransportOfProjection_apply_of_snd_eq_zero
    (s : {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1})
    (hs : s.val.1.2 = 0) :
    finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover s =
      s.val.2.val := by
  have heq : s = ⟨(((p s.val.2.val).1, 0), s.val.2), rfl⟩ := by
    apply Subtype.ext
    exact Prod.ext (Prod.ext s.property hs) rfl
  exact (congrArg
    (finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover) heq).trans
      (finiteCylinderTransportOfProjection_apply_bottom p e U hchart w hw hsum hsupport hcover
        s.val.2)

/-- The inverse fixes every point of the same original zero slice. -/
@[simp] theorem finiteCylinderTransportOfProjection_symm_apply_bottom
    (z : {z : T // (p z).2 = 0}) :
    (finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover).symm z.val =
      ⟨(((p z.val).1, 0), z), rfl⟩ := by
  apply (finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover).injective
  rw [Homeomorph.apply_symm_apply, finiteCylinderTransportOfProjection_apply_bottom]

/-- Original-space characterization of the same finite cylinder transport.

Starting with the supplied zero-slice point, apply the original chart lifts in
increasing index order. On the closed support of weight `j`, lift to prefix
clock `j + 1`; off that support leave the preceding point unchanged. Any
sequence with these equations has last point equal to the constructed transport.
No auxiliary total space or topology occurs in the statement. -/
theorem finiteCylinderTransportOfProjection_apply_eq_last
    (s : {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1})
    (v : Fin (n + 1) → T) (hzero : v 0 = s.val.2.val)
    (hmem : ∀ j : Fin n, s.val.1.1 ∈ closure {x | w j x ≠ 0} →
      v j.succ = (e j).lift (v j.castSucc)
        (cylinderPrefixMap w hw hsum (j.val + 1) s.val.1))
    (hnotMem : ∀ j : Fin n, s.val.1.1 ∉ closure {x | w j x ≠ 0} →
      v j.succ = v j.castSucc) :
    finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover s =
      v (Fin.last n) := by
  let := fiberTotalTopology p
  let e' := fun j ↦ fiberTrivialization p (e j)
  have hchart' : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e' j).baseSet := fun j ↦ by
    simpa only [e', fiberTrivialization_baseSet] using hchart j
  let z := projectionZeroPullbackHomeomorph p s
  have hzproj : z.proj = s.val.1 := by
    simp only [z, projectionZeroPullbackHomeomorph_apply]
  have hprefix : ∀ (k : ℕ) (hk : k ≤ n),
      fiberTotalHomeomorph p
          (Pullback.lift (cylinderPrefixMap w hw hsum k)
            (finiteCylinderPrefixTransport e' U hchart' w hw hsum hsupport k hk z)) =
        v ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        rw [finiteCylinderPrefixTransport_lift_zero]
        change (projectionZeroPullbackHomeomorph p s).snd.val = v 0
        rw [projectionZeroPullbackHomeomorph_apply]
        exact hzero.symm
    | succ k ih =>
        intro hk
        let j : Fin n := ⟨k, hk⟩
        by_cases hj : s.val.1.1 ∈ closure {x | w j x ≠ 0}
        · have hstep := congrArg (fiberTotalHomeomorph p)
            (finiteCylinderPrefixTransport_lift_succ_of_mem e' U hchart' w hw hsum
              hsupport j z (by simpa only [hzproj] using hj))
          calc
            fiberTotalHomeomorph p
                (Pullback.lift (cylinderPrefixMap w hw hsum (k + 1))
                  (finiteCylinderPrefixTransport e' U hchart' w hw hsum hsupport
                    (k + 1) hk z)) =
                (e j).lift
                  (fiberTotalHomeomorph p
                    (Pullback.lift (cylinderPrefixMap w hw hsum k)
                      (finiteCylinderPrefixTransport e' U hchart' w hw hsum hsupport
                        k (Nat.le_of_succ_le hk) z)))
                  (cylinderPrefixMap w hw hsum (j.val + 1) s.val.1) := by
                    simpa only [e', fiberTrivialization_lift, hzproj] using hstep
            _ = (e j).lift (v j.castSucc)
                (cylinderPrefixMap w hw hsum (j.val + 1) s.val.1) := by
                  rw [ih (Nat.le_of_succ_le hk)]
                  rfl
            _ = v j.succ := (hmem j hj).symm
        · have hstep := congrArg (fiberTotalHomeomorph p)
            (finiteCylinderPrefixTransport_lift_succ_of_notMem e' U hchart' w hw hsum
              hsupport j z (by simpa only [hzproj] using hj))
          calc
            fiberTotalHomeomorph p
                (Pullback.lift (cylinderPrefixMap w hw hsum (k + 1))
                  (finiteCylinderPrefixTransport e' U hchart' w hw hsum hsupport
                    (k + 1) hk z)) =
                fiberTotalHomeomorph p
                  (Pullback.lift (cylinderPrefixMap w hw hsum k)
                    (finiteCylinderPrefixTransport e' U hchart' w hw hsum hsupport
                      k (Nat.le_of_succ_le hk) z)) := hstep
            _ = v j.castSucc := ih (Nat.le_of_succ_le hk)
            _ = v j.succ := (hnotMem j hj).symm
  change fiberTotalHomeomorph p
    (finiteCylinderTransport e' U hchart' w hw hsum hsupport hcover z) = v (Fin.last n)
  rw [finiteCylinderTransport_apply_eq_lift_prefix]
  exact hprefix n le_rfl

/-- The given cylinder chart cover supplies continuity of the original projection
for the full-slice comparisons. No chart index is selected globally. -/
private theorem continuous_of_cylinder_chart_cover
    (e : ∀ j, Trivialization (F j) p) (U : Fin n → Set X)
    (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
    (hcover : (⋃ j, U j) = univ) : Continuous p := by
  apply continuous_of_trivialization_cover e
  intro z
  have hz : (p z).1 ∈ ⋃ j, U j := by rw [hcover]; exact mem_univ _
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  exact ⟨j, hchart j ⟨hj, mem_univ _⟩⟩

/-- Independently ordered transport between the entire original endpoint slices.

The source and target have their inherited subspace topologies from the given
`T`. The full-slice comparisons conjugate `finiteCylinderEndpointTransport`,
which composes the same supported chart steps over `X` in increasing order.
This definition does not restrict cylinder transport. The given cover supplies
continuity of `p` for the slice comparisons; no additional continuity,
nonemptiness, algebraic structure, or common chart model is assumed. -/
noncomputable def finiteCylinderEndpointTransportOfProjection :
    {z : T // (p z).2 = 0} ≃ₜ {z : T // (p z).2 = 1} :=
  private_decl% (show {z : T // (p z).2 = 0} ≃ₜ {z : T // (p z).2 = 1} from by
    letI := fiberTotalTopology p
    let hp := continuous_of_cylinder_chart_cover p e U hchart hcover
    exact (((pullbackSliceHomeomorph p (0 : I) hp).symm).trans
      (finiteCylinderEndpointTransport (fun j ↦ fiberTrivialization p (e j)) U
        (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
        w hw hsum hsupport)).trans (pullbackSliceHomeomorph p (1 : I) hp))

/-- Original endpoint transport preserves the spatial base coordinate. -/
@[simp] theorem finiteCylinderEndpointTransportOfProjection_baseX
    (z : {z : T // (p z).2 = 0}) :
    (p (finiteCylinderEndpointTransportOfProjection p e U hchart w hw hsum hsupport
      hcover z).val).1 = (p z.val).1 := by
  let := fiberTotalTopology p
  let hp := continuous_of_cylinder_chart_cover p e U hchart hcover
  change (p (pullbackSliceHomeomorph p (1 : I) hp
    (finiteCylinderEndpointTransport (fun j ↦ fiberTrivialization p (e j)) U
      (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
      w hw hsum hsupport ((pullbackSliceHomeomorph p (0 : I) hp).symm z))).val).1 = _
  rw [pullbackSliceHomeomorph_baseX, finiteCylinderEndpointTransport_proj,
    pullbackSliceHomeomorph_symm_proj]

/-- The inverse original endpoint transport preserves the spatial base coordinate. -/
@[simp] theorem finiteCylinderEndpointTransportOfProjection_symm_baseX
    (z : {z : T // (p z).2 = 1}) :
    (p ((finiteCylinderEndpointTransportOfProjection p e U hchart w hw hsum hsupport
      hcover).symm z).val).1 = (p z.val).1 := by
  have h := finiteCylinderEndpointTransportOfProjection_baseX p e U hchart w hw hsum
    hsupport hcover
    ((finiteCylinderEndpointTransportOfProjection p e U hchart w hw hsum hsupport
      hcover).symm z)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

/-- On the top slice, the original cylinder transport agrees with the independently
assembled ordered endpoint transport, under the full original slice comparisons. -/
theorem finiteCylinderTransportOfProjection_apply_top
    (z : {z : T // (p z).2 = 0}) :
    finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover
        ⟨(((p z.val).1, 1), z), rfl⟩ =
      (finiteCylinderEndpointTransportOfProjection p e U hchart w hw hsum hsupport
        hcover z).val := by
  let := fiberTotalTopology p
  let hp := continuous_of_cylinder_chart_cover p e U hchart hcover
  change fiberTotalHomeomorph p
    (finiteCylinderTransport (fun j ↦ fiberTrivialization p (e j)) U
      (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
      w hw hsum hsupport hcover
      (projectionZeroPullbackHomeomorph p ⟨(((p z.val).1, 1), z), rfl⟩)) =
    (pullbackSliceHomeomorph p (1 : I) hp
      (finiteCylinderEndpointTransport (fun j ↦ fiberTrivialization p (e j)) U
        (fun j ↦ by simpa only [fiberTrivialization_baseSet] using hchart j)
        w hw hsum hsupport ((pullbackSliceHomeomorph p (0 : I) hp).symm z))).val
  simp only [projectionZeroPullbackHomeomorph_apply, finiteCylinderTransport_apply_top,
    pullbackSliceHomeomorph_apply_val, pullbackSliceHomeomorph_symm_apply,
    fiberTotalHomeomorph_apply]
  rfl

end CylinderTransport

section Linear

universe uR

/-- Equality transport of a projection fiber preserves its value in `T`. -/
private theorem fiberTotalHomeomorph_cast_snd_val
    {B : Type uB} {T : Type uT} [TopologicalSpace T] (p : T → B) {b : B}
    (z : TotalSpace Unit (fun b ↦ {z : T // p z = b})) (h : z.proj = b) :
    (cast (congrArg (fun b ↦ {z : T // p z = b}) h) z.snd).val =
      fiberTotalHomeomorph p z := by
  cases h
  rfl

variable {X : Type uX} {T : Type uT} [TopologicalSpace X] [TopologicalSpace T]
    (p : T → X × I)

/-- A point of an original zero-time fiber gives the same nested pullback point
as its original zero-slice representative. Only equality proofs are forgotten. -/
private theorem projectionZeroPullbackHomeomorph_apply_fiber
    (x : X) (t : I) (v : {z : T // p z = (x, (0 : I))}) :
    projectionZeroPullbackHomeomorph p
      ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
        (congrArg Prod.fst v.property).symm⟩ =
      (⟨(x, t), v⟩ : TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
        ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b})))) := by
  rw [projectionZeroPullbackHomeomorph_apply]

variable {n : ℕ} {F : Fin n → Type uF} [∀ j, TopologicalSpace (F j)]
    {R : Type uR} [Semiring R]
    [∀ j, AddCommMonoid (F j)] [∀ j, Module R (F j)]
    [∀ b, AddCommMonoid {z : T // p z = b}] [∀ b, Module R {z : T // p z = b}]
    (e : ∀ j, Trivialization (F j) p) (U : Fin n → Set X)
    (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
    (w : Fin n → C(X, ℝ)) (hw : ∀ j x, 0 ≤ w j x ∧ w j x ≤ 1)
    (hsum : ∀ x, ∑ j, w j x = 1)
    (hsupport : ∀ j, closure {x | w j x ≠ 0} ⊆ U j)
    (L : ∀ j b, b ∈ (e j).baseSet → {z : T // p z = b} ≃ₗ[R] F j)
    (hL : ∀ j b (hb : b ∈ (e j).baseSet) (v : {z : T // p z = b}),
      L j b hb v = (e j v.val).2)

include L hL in
/-- Linear coordinates on the original projection fibers make the same weighted
cylinder transport linear from the fiber over `(x, 0)` to the fiber over `(x, t)`.
The source representative uses the entire original zero slice with its standard
pullback topology, and the target fiber is certified by the whole-base law.
The given fiber modules and varying chart models are unchanged. The scalar
semiring may be noncommutative, and needs no topology or continuity of operations;
the real weights change only time.

The finite ordered cylinder-chart cover is given. Hatcher, *Vector Bundles and
K-Theory*, Proposition 1.7, is a motivating bundle comparison, with subordinate
weights motivated by printed p. 20 (PDF p. 24). The arbitrary-semiring and
varying-model formulation here does not assert the full proposition. -/
theorem finiteCylinderTransportOfProjection_isLinearMap_of_coordinates
    (hcover : (⋃ j, U j) = univ) (x : X) (t : I) :
    IsLinearMap R (fun v : {z : T // p z = (x, (0 : I))} ↦
      (⟨finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover
          ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
            (congrArg Prod.fst v.property).symm⟩,
        finiteCylinderTransportOfProjection_proj p e U hchart w hw hsum hsupport hcover
          ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
            (congrArg Prod.fst v.property).symm⟩⟩ : {z : T // p z = (x, t)})) := by
  let := fiberTotalTopology p
  let e' := fun j ↦ fiberTrivialization p (e j)
  have hchart' : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e' j).baseSet := by
    intro j
    simpa only [e', fiberTrivialization_baseSet] using hchart j
  let L' : ∀ j b, b ∈ (e' j).baseSet → {z : T // p z = b} ≃ₗ[R] F j :=
    fun j b hb ↦ L j b (by simpa only [e', fiberTrivialization_baseSet] using hb)
  have hL' : ∀ j b (hb : b ∈ (e' j).baseSet) (v : {z : T // p z = b}),
      L' j b hb v =
        (e' j (⟨b, v⟩ : TotalSpace Unit (fun b ↦ {z : T // p z = b}))).2 := by
    intro j b hb v
    exact fiberTrivialization_coordinates p (e j) (fun b hb v ↦ L j b hb v) (hL j) b
      (by simpa only [e', fiberTrivialization_baseSet] using hb) v
  let H := finiteCylinderTransport e' U hchart' w hw hsum hsupport hcover
  let g : {z : T // p z = (x, (0 : I))} → {z : T // p z = (x, t)} := fun v ↦
    cast (congrArg (fun b ↦ {z : T // p z = b})
      (finiteCylinderTransport_proj e' U hchart' w hw hsum hsupport hcover
        (⟨(x, t), v⟩ : TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
          ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b}))))))
      (H ⟨(x, t), v⟩).snd
  have hg : IsLinearMap R g :=
    finiteCylinderTransport_isLinearMap_of_coordinates e' U hchart' w hw hsum hsupport
      L' hL' hcover x t
  let s : {z : T // p z = (x, (0 : I))} →
      {s : (X × I) × {z : T // (p z).2 = 0} // s.1.1 = (p s.2.val).1} := fun v ↦
    ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
      (congrArg Prod.fst v.property).symm⟩
  let f : {z : T // p z = (x, (0 : I))} → {z : T // p z = (x, t)} := fun v ↦
    ⟨finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover (s v),
      finiteCylinderTransportOfProjection_proj p e U hchart w hw hsum hsupport hcover
        (s v)⟩
  change IsLinearMap R f
  have hfg : f = g := by
    funext v
    apply Subtype.ext
    change finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover
      (s v) = (g v).val
    calc
      finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover
          (s v) = fiberTotalHomeomorph p (H ⟨(x, t), v⟩) := by
        change fiberTotalHomeomorph p (H (projectionZeroPullbackHomeomorph p (s v))) = _
        rw [show projectionZeroPullbackHomeomorph p (s v) =
          (⟨(x, t), v⟩ : TotalSpace Unit ((Prod.fst : X × I → X) *ᵖ
            ((fun x : X ↦ (x, (0 : I))) *ᵖ (fun b ↦ {z : T // p z = b})))) from
          projectionZeroPullbackHomeomorph_apply_fiber p x t v]
      _ = (g v).val :=
        (fiberTotalHomeomorph_cast_snd_val p (H ⟨(x, t), v⟩)
          (finiteCylinderTransport_proj e' U hchart' w hw hsum hsupport hcover
            ⟨(x, t), v⟩)).symm
  rw [hfg]
  exact hg

end Linear

end Bundle.Trivialization
