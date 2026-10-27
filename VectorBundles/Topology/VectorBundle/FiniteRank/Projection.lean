/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Projections, zero sections and descent for finite-rank atlases

The projection of a finite-rank atlas is continuous, open and a quotient map for the
given total-space and base topologies. A subset of the base is open or closed exactly
when its preimage under the projection has the same property. A map from the base to
any topological space is continuous exactly when its composition with the projection
is continuous. The canonical zero section is also continuous.

On each open chart source the projection is the first chart coordinate, followed by
the inclusion of the open chart base set. Over its open base set, inverse zero
coordinates give the original zero vector. These zero vectors also witness
surjectivity of the projection, so the quotient property follows from Mathlib's
continuous, open, surjective criterion. Chart ranks may vary and may be zero; no
common model or continuity of scalar operations is required.

## References

* The fibre-bundle and topology APIs of Mathlib.
-/

@[expose] public section

universe uK uB uE uP uI

open Bundle Topology

namespace Bundle.FiniteRankAtlas

/-- The projection of a finite-rank atlas is continuous for the given total-space topology. -/
theorem continuous_proj
    {K : Type uK} [Field K] [TopologicalSpace K]
    {B : Type uB} [TopologicalSpace B]
    {P : Type uP} {E : B → Type uE}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
    (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    Continuous (TotalSpace.proj : TotalSpace P E → B) := by
  apply continuous_iff_continuousAt.2
  intro p
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
  have hp : p ∈ (A.chart i).source := (A.mem_source_iff i p).mpr hi
  have hchart : ContinuousOn (fun q : TotalSpace P E => (A.chart i q).1)
      (A.chart i).source :=
    (A.chart i).continuousOn_toFun.fst
  have hproj : ContinuousOn (TotalSpace.proj : TotalSpace P E → B)
      (A.chart i).source := by
    apply hchart.congr
    intro q hq
    simp only [A.chart_proj i q hq]
  exact (hproj p hp).continuousAt ((A.chart i).open_source.mem_nhds hp)

/-- The projection of a finite-rank atlas is open for the given total-space topology. -/
theorem isOpenMap_proj
    {K : Type uK} [Field K] [TopologicalSpace K]
    {B : Type uB} [TopologicalSpace B]
    {P : Type uP} {E : B → Type uE}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
    (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    IsOpenMap (TotalSpace.proj : TotalSpace P E → B) := by
  intro s hs
  have hopen (i : A.Index) :
      IsOpen ((fun p : (A.chart i).source => p.1.proj) ''
        ((Subtype.val : (A.chart i).source → TotalSpace P E) ⁻¹' s)) := by
    have hmap : IsOpenMap (fun p : (A.chart i).source => p.1.proj) := by
      have hbase : IsOpenMap (Subtype.val : (A.chart i).baseSet → B) := by
        intro t ht
        rcases ht with ⟨u, hu, rfl⟩
        have himage :
            (Subtype.val : (A.chart i).baseSet → B) ''
                ((Subtype.val : (A.chart i).baseSet → B) ⁻¹' u) =
              (A.chart i).baseSet ∩ u := by
          ext b
          constructor
          · rintro ⟨q, hq, rfl⟩
            exact ⟨q.2, hq⟩
          · rintro ⟨hb, hbu⟩
            exact ⟨⟨b, hb⟩, hbu, rfl⟩
        rw [himage]
        exact (A.chart i).open_baseSet.inter hu
      have hcomp : IsOpenMap
          ((Subtype.val : (A.chart i).baseSet → B) ∘ Prod.fst ∘ A.sourceHomeomorph i) :=
        hbase.comp (isOpenMap_fst.comp (A.sourceHomeomorph i).isOpenMap)
      simpa only [Function.comp_def, sourceHomeomorph_fst_coe] using hcomp
    exact hmap _ (hs.preimage continuous_subtype_val)
  -- The chart sources cover the original total space, so their images cover the image of `s`.
  have heq : TotalSpace.proj '' s = ⋃ i : A.Index,
      (fun p : (A.chart i).source => p.1.proj) ''
        ((Subtype.val : (A.chart i).source → TotalSpace P E) ⁻¹' s) := by
    ext b
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
      exact Set.mem_iUnion.mpr
        ⟨i, ⟨⟨p, (A.mem_source_iff i p).mpr hi⟩, hp, rfl⟩⟩
    · intro hb
      rcases Set.mem_iUnion.mp hb with ⟨i, p, hp, hpb⟩
      exact ⟨p.1, hp, hpb⟩
  rw [heq]
  exact isOpen_iUnion hopen

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]

/-- The canonical zero section of a finite-rank atlas is continuous for the given
original total-space topology. -/
theorem continuous_zeroSection (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    Continuous (fun b : B => (TotalSpace.mk b (0 : E b) : TotalSpace P E)) := by
  apply continuous_iff_continuousAt.2
  intro b
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet b
  have hzero : ContinuousOn
      (fun b : B => (TotalSpace.mk b (0 : E b) : TotalSpace P E))
      (A.chart i).baseSet := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun b : (A.chart i).baseSet =>
      (TotalSpace.mk b.1 (0 : E b.1) : TotalSpace P E))
    simpa only [invCoord_zero] using A.continuous_invCoord_const i 0
  exact (hzero b hi).continuousAt ((A.chart i).open_baseSet.mem_nhds hi)

/-- The projection of a finite-rank atlas is a quotient map for the given topologies. -/
theorem isQuotientMap_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    Topology.IsQuotientMap (TotalSpace.proj : TotalSpace P E → B) := by
  exact A.isOpenMap_proj.isQuotientMap A.continuous_proj
    (fun b => ⟨(TotalSpace.mk b (0 : E b) : TotalSpace P E), rfl⟩)

/-- A subset of the base is open exactly when its preimage under the original
total-space projection is open. -/
theorem isOpen_iff_preimage_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) (s : Set B) :
    IsOpen s ↔ IsOpen ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' s) :=
  A.isQuotientMap_proj.isOpen_preimage.symm

/-- A subset of the base is closed exactly when its preimage under the original
total-space projection is closed. -/
theorem isClosed_iff_preimage_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) (s : Set B) :
    IsClosed s ↔ IsClosed ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' s) :=
  A.isQuotientMap_proj.isClosed_preimage.symm

universe uY

/-- A map from the base to any topological space is continuous exactly when its
composition with the original total-space projection is continuous. -/
theorem continuous_iff_comp_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    {Y : Type uY} [TopologicalSpace Y] (g : B → Y) :
    Continuous g ↔ Continuous (g ∘ (TotalSpace.proj : TotalSpace P E → B)) :=
  A.isQuotientMap_proj.continuous_iff

end Bundle.FiniteRankAtlas
