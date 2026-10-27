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

/-- The total space of a finite-rank atlas is Hausdorff if the base and every
chart-coordinate space are Hausdorff, for their given topologies. The chart ranks may
vary and may be zero; Hausdorffness of the scalar field is not required. -/
theorem t2Space_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [T2Space B] [∀ i : A.Index, T2Space (Fin (A.rank i) → K)] :
    T2Space (TotalSpace P E) := by
  classical
  constructor
  intro p q hpq
  by_cases hbase : p.proj = q.proj
  · obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
    -- The full-fibre source of this one chart contains both points.
    have hp : p ∈ (A.chart i).source := (A.mem_source_iff i p).mpr hi
    have hq : q ∈ (A.chart i).source := by
      apply (A.mem_source_iff i q).mpr
      rw [← hbase]
      exact hi
    let p' : (A.chart i).source := ⟨p, hp⟩
    let q' : (A.chart i).source := ⟨q, hq⟩
    have hne : A.sourceHomeomorph i p' ≠ A.sourceHomeomorph i q' := by
      intro h
      exact hpq (congrArg Subtype.val ((A.sourceHomeomorph i).injective h))
    obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := t2_separation hne
    let f : (A.chart i).baseSet × (Fin (A.rank i) → K) → TotalSpace P E :=
      (Subtype.val : (A.chart i).source → TotalSpace P E) ∘
        (A.sourceHomeomorph i).symm
    have hf : IsOpenMap f :=
      (A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap.comp
        (A.sourceHomeomorph i).symm.isOpenMap
    refine ⟨f '' u, f '' v, hf u hu, hf v hv, ?_, ?_, ?_⟩
    · exact ⟨A.sourceHomeomorph i p', hpu,
        congrArg Subtype.val ((A.sourceHomeomorph i).symm_apply_apply p')⟩
    · exact ⟨A.sourceHomeomorph i q', hqv,
        congrArg Subtype.val ((A.sourceHomeomorph i).symm_apply_apply q')⟩
    · apply Set.disjoint_left.mpr
      rintro z ⟨x, hxu, hxz⟩ ⟨y, hyv, hyz⟩
      have hxy : x = y := (A.sourceHomeomorph i).symm.injective
        (Subtype.ext (hxz.trans hyz.symm))
      subst y
      exact Set.disjoint_left.mp huv hxu hyv
  · obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := t2_separation hbase
    refine ⟨TotalSpace.proj ⁻¹' u, TotalSpace.proj ⁻¹' v,
      hu.preimage A.continuous_proj, hv.preimage A.continuous_proj, hpu, hqv, ?_⟩
    exact Set.disjoint_left.mpr (fun z hz hz' => Set.disjoint_left.mp huv hz hz')

/-- The total space of a finite-rank atlas is locally compact if the base and every
chart-coordinate space are locally compact, for their given topologies. Chart ranks
may vary and may be zero; neither local compactness of the scalar field nor
Hausdorffness is assumed. -/
theorem locallyCompactSpace_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [LocallyCompactSpace B] [∀ i : A.Index, LocallyCompactSpace (Fin (A.rank i) → K)] :
    LocallyCompactSpace (TotalSpace P E) := by
  constructor
  intro p s hs
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
  have : LocallyCompactSpace (A.chart i).baseSet :=
    (A.chart i).open_baseSet.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (A.chart i).source :=
    (A.sourceHomeomorph i).isOpenEmbedding.locallyCompactSpace
  let p' : (A.chart i).source := ⟨p, (A.mem_source_iff i p).mpr hi⟩
  have hpre : (Subtype.val : (A.chart i).source → TotalSpace P E) ⁻¹' s ∈ 𝓝 p' := by
    obtain ⟨u, hus, hu, hpu⟩ := mem_nhds_iff.mp hs
    exact mem_nhds_iff.mpr ⟨Subtype.val ⁻¹' u, Set.preimage_mono hus,
      hu.preimage continuous_subtype_val, hpu⟩
  obtain ⟨v, hvs, hv, hpv⟩ := mem_nhds_iff.mp hpre
  obtain ⟨c, hcompact, hpc, hcv⟩ := exists_compact_subset hv hpv
  have hc : c ∈ 𝓝 p' :=
    mem_nhds_iff.mpr ⟨interior c, interior_subset, isOpen_interior, hpc⟩
  have hcs : c ⊆ (Subtype.val : (A.chart i).source → TotalSpace P E) ⁻¹' s :=
    hcv.trans hvs
  refine ⟨Subtype.val '' c, ?_, ?_, hcompact.image continuous_subtype_val⟩
  · -- Openness of the original source makes its neighbourhoods ambient neighbourhoods.
    obtain ⟨v, hvc, hv, hpv⟩ := mem_nhds_iff.mp hc
    refine mem_nhds_iff.mpr ⟨Subtype.val '' v, Set.image_mono hvc, ?_, ?_⟩
    · exact (A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap v hv
    · exact ⟨p', hpv, rfl⟩
  · rintro q ⟨q', hq', rfl⟩
    exact hcs hq'

/-- The total space of a finite-rank atlas is first countable if the base and every
chart-coordinate space are first countable, for their given topologies. Chart ranks
may vary and may be zero; first countability of the scalar field is not required. -/
theorem firstCountableTopology_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [FirstCountableTopology B]
    [∀ i : A.Index, FirstCountableTopology (Fin (A.rank i) → K)] :
    FirstCountableTopology (TotalSpace P E) := by
  constructor
  intro p
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
  have hp : p ∈ (A.chart i).source := (A.mem_source_iff i p).mpr hi
  let p' : (A.chart i).source := ⟨p, hp⟩
  let H := A.sourceHomeomorph i
  let q := H p'
  let j : (A.chart i).baseSet × (Fin (A.rank i) → K) → TotalSpace P E :=
    (Subtype.val : (A.chart i).source → TotalSpace P E) ∘ H.symm
  have hj : IsOpenMap j :=
    (A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap.comp H.symm.isOpenMap
  have hjcont : Continuous j := continuous_subtype_val.comp H.symm.continuous
  have hjq : j q = p := congrArg Subtype.val (H.symm_apply_apply p')
  -- The original open source upgrades chart neighbourhoods to ambient neighbourhoods.
  have hmap : Filter.map j (𝓝 q) = 𝓝 p := by
    ext s
    change j ⁻¹' s ∈ 𝓝 q ↔ s ∈ 𝓝 p
    constructor
    · intro hs
      obtain ⟨v, hvs, hv, hqv⟩ := mem_nhds_iff.mp hs
      refine mem_nhds_iff.mpr ⟨j '' v, ?_, hj v hv, ⟨q, hqv, hjq⟩⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hvs hx
    · intro hs
      obtain ⟨u, hus, hu, hpu⟩ := mem_nhds_iff.mp hs
      refine mem_nhds_iff.mpr ⟨j ⁻¹' u, Set.preimage_mono hus,
        hu.preimage hjcont, ?_⟩
      change j q ∈ u
      rw [hjq]
      exact hpu
  rw [← hmap]
  infer_instance

universe uY

/-- A map from the base to any topological space is continuous exactly when its
composition with the original total-space projection is continuous. -/
theorem continuous_iff_comp_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    {Y : Type uY} [TopologicalSpace Y] (g : B → Y) :
    Continuous g ↔ Continuous (g ∘ (TotalSpace.proj : TotalSpace P E → B)) :=
  A.isQuotientMap_proj.continuous_iff

end Bundle.FiniteRankAtlas
