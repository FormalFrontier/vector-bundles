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
is continuous. The canonical zero section is continuous and detects continuity of
maps from any topological domain into the base: composing with the continuous
projection recovers the original map. The zero section is a topological embedding.

On each open chart source the projection is the first chart coordinate, followed by
the inclusion of the open chart base set. Over its open base set, inverse zero
coordinates give the original zero vector. These zero vectors also witness
surjectivity of the projection, so the quotient property follows from Mathlib's
continuous, open, surjective criterion. Chart ranks may vary and may be zero; no
common model or continuity of scalar operations is required.

The total space is T0 when the base and each full chart-coordinate space are T0 for
their given topologies. The coordinate ranks may vary without a global bound and may
be zero; the scalar field need not be T0.

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

/-- The total space of a finite-rank atlas is T0 if the base and every exact
chart-coordinate space are T0, for their given topologies. Chart ranks may vary
without a global bound and may be zero; the scalar field need not be T0. -/
theorem t0Space_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [T0Space B] [∀ i : A.Index, T0Space (Fin (A.rank i) → K)] :
    T0Space (TotalSpace P E) := by
  constructor
  intro p q hpq
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
  have hp : p ∈ (A.chart i).source := (A.mem_source_iff i p).mpr hi
  have hS := (A.chart i).open_source
  have hq : q ∈ (A.chart i).source :=
    (Inseparable.mem_open_iff hpq hS).mp hp
  have hchartCONTon := (A.chart i).continuousOn_toFun
  have himage : Inseparable (A.chart i p) (A.chart i q) :=
    Inseparable.map_of_continuousOn hpq hchartCONTon hp hq
  have himageEq : A.chart i p = A.chart i q := by
    rcases (inferInstance : T0Space (B × (Fin (A.rank i) → K))) with ⟨hT0⟩
    exact hT0 himage
  -- Recover the original points using this chart only on its source.
  have hbase : p.proj = q.proj := by
    simpa only [A.chart_proj i p hp, A.chart_proj i q hq] using
      congrArg Prod.fst himageEq
  let p' : (A.chart i).source := ⟨p, hp⟩
  let q' : (A.chart i).source := ⟨q, hq⟩
  have hsource : A.sourceHomeomorph i p' = A.sourceHomeomorph i q' := by
    apply Prod.ext
    · apply Subtype.ext
      exact (A.sourceHomeomorph_fst_coe i p').trans
        (hbase.trans (A.sourceHomeomorph_fst_coe i q').symm)
    · exact (A.sourceHomeomorph_snd i p').trans
        ((congrArg Prod.snd himageEq).trans (A.sourceHomeomorph_snd i q').symm)
  exact congrArg Subtype.val ((A.sourceHomeomorph i).injective hsource)

/-- The total space of a finite-rank atlas is T1 if the base and every exact
chart-coordinate space are T1, for their given topologies. Chart ranks may vary
without a global bound and may be zero; the scalar field need not be T1. -/
theorem t1Space_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [T1Space B] [∀ i : A.Index, T1Space (Fin (A.rank i) → K)] :
    T1Space (TotalSpace P E) := by
  classical
  constructor
  intro p
  let j (i : A.Index) : (A.chart i).baseSet × (Fin (A.rank i) → K) → TotalSpace P E :=
    (Subtype.val : (A.chart i).source → TotalSpace P E) ∘ (A.sourceHomeomorph i).symm
  have hj (i : A.Index) : IsOpenMap (j i) :=
    (A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap.comp
      (A.sourceHomeomorph i).symm.isOpenMap
  have hinj (i : A.Index) : Function.Injective (j i) := by
    intro x y h
    exact (A.sourceHomeomorph i).symm.injective (Subtype.ext h)
  let v (i : A.Index) : Set ((A.chart i).baseSet × (Fin (A.rank i) → K)) :=
    {x | j i x ≠ p}
  have hv (i : A.Index) : IsOpen (v i) := by
    have : T1Space ((A.chart i).baseSet × (Fin (A.rank i) → K)) := by infer_instance
    -- Remove the unique representative of `p` when it lies in this original source.
    by_cases hp : p ∈ (A.chart i).source
    · let p' : (A.chart i).source := ⟨p, hp⟩
      have hrep : j i (A.sourceHomeomorph i p') = p :=
        congrArg Subtype.val ((A.sourceHomeomorph i).symm_apply_apply p')
      have heq : v i = {A.sourceHomeomorph i p'}ᶜ := by
        ext x
        change j i x ≠ p ↔ x ≠ A.sourceHomeomorph i p'
        constructor
        · intro hx h
          exact hx ((congrArg (j i) h).trans hrep)
        · intro hx h
          exact hx (hinj i (h.trans hrep.symm))
      rw [heq]
      exact isClosed_singleton.isOpen_compl
    · have heq : v i = Set.univ := by
        ext x
        constructor
        · intro _
          exact Set.mem_univ x
        · intro _
          change j i x ≠ p
          intro h
          have hx : j i x ∈ (A.chart i).source := ((A.sourceHomeomorph i).symm x).2
          exact hp (h ▸ hx)
      rw [heq]
      exact isOpen_univ
  -- The original open chart cover supplies every point other than `p`.
  have heq : ({p} : Set (TotalSpace P E))ᶜ = ⋃ i : A.Index, j i '' v i := by
    ext q
    constructor
    · intro hq
      change q ≠ p at hq
      obtain ⟨i, hi⟩ := A.exists_mem_baseSet q.proj
      let q' : (A.chart i).source := ⟨q, (A.mem_source_iff i q).mpr hi⟩
      have hjq : j i (A.sourceHomeomorph i q') = q :=
        congrArg Subtype.val ((A.sourceHomeomorph i).symm_apply_apply q')
      refine Set.mem_iUnion.mpr ⟨i, ⟨A.sourceHomeomorph i q', ?_, hjq⟩⟩
      change j i (A.sourceHomeomorph i q') ≠ p
      rwa [hjq]
    · intro hq
      rcases Set.mem_iUnion.mp hq with ⟨i, x, hx, rfl⟩
      change j i x ≠ p
      exact hx
  apply isOpen_compl_iff.mp
  rw [heq]
  exact isOpen_iUnion (fun i => hj i _ (hv i))

/-- The total space of a finite-rank atlas is regular if the given base and every exact
chart-coordinate space are regular, for their given topologies. Ranks may vary without
a global bound and may be zero; regularity of the scalar field is not required.

A closed neighbourhood in the base supplies an ambient-closed buffer inside a chart
source. Within this buffer, a source-closed neighbourhood is also ambient closed. -/
theorem regularSpace_totalSpace (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    [RegularSpace B] [∀ i : A.Index, RegularSpace (Fin (A.rank i) → K)] :
    RegularSpace (TotalSpace P E) := by
  classical
  have hproj : Continuous (TotalSpace.proj : TotalSpace P E → B) := A.continuous_proj
  have hbuffer (p : TotalSpace P E) :
      ∃ (i : A.Index) (F : Set B),
        IsClosed F ∧ p.proj ∈ interior F ∧ F ⊆ (A.chart i).baseSet ∧
          IsClosed ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) ∧
          ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) ∈ 𝓝 p ∧
          ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) ⊆ (A.chart i).source := by
    obtain ⟨i, hi⟩ := A.exists_mem_baseSet p.proj
    have hU : IsOpen ((A.chart i).baseSet) := (A.chart i).open_baseSet
    rcases exists_mem_nhds_isClosed_subset (hU.mem_nhds hi) with
      ⟨F, hFp, hFclosed, hFsub⟩
    have hFinterior : p.proj ∈ interior F := mem_interior_iff_mem_nhds.mpr hFp
    have hDclosed : IsClosed ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) :=
      hFclosed.preimage hproj
    have hDnhds : ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) ∈ 𝓝 p := by
      refine mem_nhds_iff.mpr
        ⟨(TotalSpace.proj : TotalSpace P E → B) ⁻¹' interior F, ?_,
          isOpen_interior.preimage hproj, hFinterior⟩
      intro q hq
      exact (interior_subset : interior F ⊆ F) hq
    have hDsource : ((TotalSpace.proj : TotalSpace P E → B) ⁻¹' F) ⊆
        (A.chart i).source := by
      intro q hq
      exact (A.mem_source_iff i q).mpr (hFsub hq)
    exact ⟨i, F, hFclosed, hFinterior, hFsub, hDclosed, hDnhds, hDsource⟩
  -- Each original chart source is regular via its product homeomorphism.
  have hsource : ∀ i : A.Index, RegularSpace (A.chart i).source := ?_
  swap
  · intro i
    have hproduct : RegularSpace ((A.chart i).baseSet × (Fin (A.rank i) → K)) := by
      infer_instance
    have e : (A.chart i).source ≃ₜ
        (A.chart i).baseSet × (Fin (A.rank i) → K) := A.sourceHomeomorph i
    -- Both factors carry their original subtype and Pi topologies.
    refine IsInducing.regularSpace (show IsInducing e from ?_)
    exact Homeomorph.isInducing e
  -- Construct closed neighbourhoods in the original total space.
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset ?_
  intro a W hW
  obtain ⟨i, F, hFclosed, haFinterior, hFsub, hDclosed, hDnhds, hDsource⟩ := hbuffer a
  -- Fix the regular original source containing the point.
  have hsource_a : RegularSpace (A.chart i).source := hsource i
  have ha_source : a ∈ (A.chart i).source :=
    (A.mem_source_iff i a).mpr
      (hFsub ((interior_subset : interior F ⊆ F) haFinterior))
  let a' : (A.chart i).source := ⟨a, ha_source⟩
  let j : (A.chart i).source → TotalSpace P E := Subtype.val
  let D : Set (TotalSpace P E) :=
    (TotalSpace.proj : TotalSpace P E → B) ⁻¹' F
  have hDS : D ⊆ (A.chart i).source := hDsource
  -- W and the interior of the closed buffer give an ambient neighbourhood.
  have haDinterior : a ∈ interior D := mem_interior_iff_mem_nhds.mpr hDnhds
  have hWD : W ∩ interior D ∈ 𝓝 a := by
    obtain ⟨u, huW, hu, hau⟩ := mem_nhds_iff.mp hW
    refine mem_nhds_iff.mpr
      ⟨u ∩ interior D, ?_, hu.inter isOpen_interior, ⟨hau, haDinterior⟩⟩
    intro q hq
    exact ⟨huW hq.1, hq.2⟩
  -- Pull back that neighbourhood to the original source subtype.
  have hpre : j ⁻¹' (W ∩ interior D) ∈ 𝓝 a' := by
    obtain ⟨u, huWD, hu, hau⟩ := mem_nhds_iff.mp hWD
    exact mem_nhds_iff.mpr
      ⟨j ⁻¹' u, Set.preimage_mono huWD, hu.preimage continuous_subtype_val, hau⟩
  -- Choose a closed neighbourhood in the original source.
  rcases exists_mem_nhds_isClosed_subset hpre with
    ⟨C', hC'nhds, hC'closed, hC'sub⟩
  let C : Set (TotalSpace P E) := j '' C'
  have hpreimage_image : j ⁻¹' C = C' := by
    ext q
    change j q ∈ j '' C' ↔ q ∈ C'
    constructor
    · rintro ⟨r, hr, hrq⟩
      have hrq' : r = q := Subtype.ext hrq
      exact hrq' ▸ hr
    · intro hq
      exact ⟨q, hq, rfl⟩
  have hCrel : IsClosed (j ⁻¹' C) := by
    rw [hpreimage_image]
    exact hC'closed
  have hCD : C ⊆ D := by
    rintro q ⟨q', hq', rfl⟩
    exact (interior_subset : interior D ⊆ D) ((hC'sub hq').2)
  have hCW : C ⊆ W := by
    rintro q ⟨q', hq', rfl⟩
    exact (hC'sub hq').1
  -- The source-closed C lies in the ambient-closed buffer D, itself inside the source.
  -- Its ambient complement is therefore an open source image together with Dᶜ.
  have hcompeq : Cᶜ = j '' (j ⁻¹' C)ᶜ ∪ Dᶜ := by
    ext q
    constructor
    · intro hq
      by_cases hqD : q ∈ D
      · left
        refine ⟨⟨q, hDS hqD⟩, ?_, rfl⟩
        change q ∉ C
        exact hq
      · right
        exact hqD
    · intro hq
      rcases hq with ⟨q', hq', rfl⟩ | hqD
      · change j q' ∉ C
        exact hq'
      · intro hqC
        exact hqD (hCD hqC)
  have hCclosed : IsClosed C := by
    apply isOpen_compl_iff.mp
    rw [hcompeq]
    exact
      ((A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap
        ((j ⁻¹' C)ᶜ) hCrel.isOpen_compl).union hDclosed.isOpen_compl
  -- Openness of the source transports its neighbourhood to the ambient space.
  have hCnhds : C ∈ 𝓝 a := by
    obtain ⟨v, hvc, hv, hav⟩ := mem_nhds_iff.mp hC'nhds
    refine mem_nhds_iff.mpr ⟨j '' v, ?_, ?_, ?_⟩
    · exact Set.image_mono hvc
    · exact (A.chart i).open_source.isOpenEmbedding_subtypeVal.isOpenMap v hv
    · exact ⟨a', hav, rfl⟩
  exact ⟨C, hCnhds, hCclosed, hCW⟩

/-- The canonical zero section of a finite-rank atlas is a topological embedding
for the given original total-space and base topologies. -/
theorem isEmbedding_zeroSection (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    Topology.IsEmbedding
      (fun b : B => (TotalSpace.mk b (0 : E b) : TotalSpace P E)) := by
  have hz := A.continuous_zeroSection
  have hp := A.continuous_proj
  have hret : ∀ b : B,
      (TotalSpace.mk b (0 : E b) : TotalSpace P E).proj = b := fun _ => rfl
  exact IsEmbedding.of_leftInverse hret hp hz

universe uY

/-- A map from any topological space into the base is continuous exactly when its
composition with the canonical zero section is continuous, for the given topologies. -/
theorem continuous_iff_zeroSection_comp (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    {Y : Type uY} [TopologicalSpace Y] (h : Y → B) :
    Continuous h ↔ Continuous
      ((fun b : B => (TotalSpace.mk b (0 : E b) : TotalSpace P E)) ∘ h) := by
  constructor
  · intro hh
    exact A.continuous_zeroSection.comp hh
  · intro hz
    exact A.continuous_proj.comp hz

/-- A map from the base to any topological space is continuous exactly when its
composition with the original total-space projection is continuous. -/
theorem continuous_iff_comp_proj (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    {Y : Type uY} [TopologicalSpace Y] (g : B → Y) :
    Continuous g ↔ Continuous (g ∘ (TotalSpace.proj : TotalSpace P E → B)) :=
  A.isQuotientMap_proj.continuous_iff

end Bundle.FiniteRankAtlas
