/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.Homeomorph.Lemmas
public import VectorBundles.Topology.FiberBundle.ModelTopology
public import VectorBundles.Topology.VectorBundle.FiniteRank.LinearEquiv
public import VectorBundles.Topology.VectorBundle.FiniteRank.Patch
public import VectorBundles.Topology.VectorBundle.CoordinateMap

/-!
# Fixed-model bundles from constant-rank atlases

A finite-rank atlas whose original fibres have constant finrank gives named whole-base
`FiberBundle` data with model `Fin n → K`. The fibres, their module structures and topologies
are unchanged. The total-space topology is transported from the original total space by the
base- and vector-preserving `Bundle.TotalSpace.changeModelHomeomorph`.

Only charts of rank `n` are retained. They cover the base; charts of any other rank have empty
base set. Neither the base nor the retained index type is required to be nonempty. The chart
coordinates are the original coordinates, reindexed solely by equality of the chart rank with
`n`. The patch comparison uses the existing patch topology and patch homeomorphisms, including
on empty chart domains.

Over a nontrivially normed field, `vectorBundleOfFinrank` applies the linear-atlas criterion to
exactly these fibre-bundle data and this topology. The field need not be complete, and the
original fibres need no norms. The fibre-bundle construction itself needs only a field with a
given topology; it assumes no continuity of scalar or fibre operations.

## References

The chart transports and fibre-bundle assembly use Mathlib's `Trivialization.compHomeomorph`,
`Homeomorph.subtype` and `FiberBundle.mk`. The vector-bundle conclusion uses the project's
`VectorBundle.of_isLinear`, with Mathlib's scalar-self and finite-product module-topology
instances. The original coordinates and local comparisons use `FiniteRankAtlas`'s coordinate
linear equivalences and patch homeomorphisms.
-/

@[expose] public section

open Bundle Topology

universe uK uB uE uP uI

namespace Bundle.FiniteRankAtlas

section Topological

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [tP : TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) (n : ℕ)

local notation "C" => TotalSpace.changeModelTopology P (Fin n → K) E tP
local notation "H" => TotalSpace.changeModelHomeomorph P (Fin n → K) E tP

/-- The equality reindexing of a chart's finite coordinate space. No choice of basis is made. -/
def rankReindex (i : A.Index) (hi : A.rank i = n) :
    (Fin (A.rank i) → K) ≃ₗ[K] (Fin n → K) := by
  subst n
  exact LinearEquiv.refl K (Fin (A.rank i) → K)

/-- Equality reindexing at the chart's own rank is the identity. -/
@[simp] theorem rankReindex_rfl (i : A.Index) :
    A.rankReindex (A.rank i) i rfl = LinearEquiv.refl K (Fin (A.rank i) → K) := rfl

/-- Equality reindexing evaluates by the inverse equality cast of the coordinate index. -/
@[simp] theorem rankReindex_apply (i : A.Index) (hi : A.rank i = n)
    (w : Fin (A.rank i) → K) (j : Fin n) :
    A.rankReindex n i hi w j = w (Fin.cast hi.symm j) := by
  subst n
  rfl

/-- Inverse equality reindexing evaluates by the forward equality cast of the index. -/
@[simp] theorem rankReindex_symm_apply (i : A.Index) (hi : A.rank i = n)
    (w : Fin n → K) (j : Fin (A.rank i)) :
    (A.rankReindex n i hi).symm w j = w (Fin.cast hi j) := by
  subst n
  rfl

/-- A chart of rank `n`, expressed on the unchanged fibres with the named transported
total-space topology. Only equality reindexing and the constructed tag homeomorphism are used. -/
def fixedRankTrivialization (i : A.Index) (hi : A.rank i = n) :
    @Trivialization B (Fin n → K) (TotalSpace (Fin n → K) E)
      inferInstance inferInstance C TotalSpace.proj := by
  subst n
  letI : TopologicalSpace (TotalSpace (Fin (A.rank i) → K) E) :=
    TotalSpace.changeModelTopology P (Fin (A.rank i) → K) E tP
  exact (A.chart i).compHomeomorph
    (TotalSpace.changeModelHomeomorph P (Fin (A.rank i) → K) E tP)

/-- The transported chart has exactly the original chart's base set. -/
@[simp] theorem fixedRankTrivialization_baseSet (i : A.Index) (hi : A.rank i = n) :
    @Trivialization.baseSet B (Fin n → K) (TotalSpace (Fin n → K) E)
      inferInstance inferInstance C TotalSpace.proj
      (A.fixedRankTrivialization n i hi) = (A.chart i).baseSet := by
  subst n
  rfl

/-- The source of the transported chart is the preimage of the original chart base set. -/
@[simp] theorem fixedRankTrivialization_source (i : A.Index) (hi : A.rank i = n) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))).source =
      TotalSpace.proj ⁻¹' (A.chart i).baseSet := by
  let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  rw [(A.fixedRankTrivialization n i hi).source_eq,
    A.fixedRankTrivialization_baseSet n i hi]

/-- The target of the transported chart is the original base set times the fixed model. -/
@[simp] theorem fixedRankTrivialization_target (i : A.Index) (hi : A.rank i = n) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))).target =
      (A.chart i).baseSet ×ˢ (Set.univ : Set (Fin n → K)) := by
  let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  rw [(A.fixedRankTrivialization n i hi).target_eq,
    A.fixedRankTrivialization_baseSet n i hi]

/-- Everywhere, the new chart is the original chart after tag transport and equality reindexing.
Its values outside its source are not required to preserve the projection. -/
theorem fixedRankTrivialization_apply (i : A.Index) (hi : A.rank i = n)
    (p : TotalSpace (Fin n → K) E) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))) p =
      ((A.chart i (TotalSpace.changeModelEquiv P (Fin n → K) E p)).1,
        A.rankReindex n i hi
          (A.chart i (TotalSpace.changeModelEquiv P (Fin n → K) E p)).2) := by
  subst n
  rfl

/-- On an original fibre in its chart domain, the new chart retains the base point and
reads exactly the original coordinate vector, reindexed only by the rank equality. -/
@[simp] theorem fixedRankTrivialization_mk (i : A.Index) (hi : A.rank i = n)
    {b : B} (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))) (TotalSpace.mk b v) =
      (b, A.rankReindex n i hi (A.coord i b v)) := by
  subst n
  apply Prod.ext
  · exact A.chart_proj i (TotalSpace.mk b v) ((A.mk_mem_source_iff i b v).mpr hb)
  · rfl

/-- The on-source formula for the transported chart. -/
theorem fixedRankTrivialization_apply_of_mem (i : A.Index) (hi : A.rank i = n)
    (p : TotalSpace (Fin n → K) E) (hp : p.proj ∈ (A.chart i).baseSet) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))) p =
      (p.proj, A.rankReindex n i hi (A.coord i p.proj p.snd)) := by
  cases p with
  | mk b v => exact A.fixedRankTrivialization_mk n i hi hp v

/-- Inverse coordinates of the new chart are precisely the original inverse coordinates,
with the vector unchanged and the total-space tag transported back. -/
theorem fixedRankTrivialization_symm (i : A.Index) (hi : A.rank i = n)
    (b : (A.chart i).baseSet) (w : Fin n → K) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))).symm (b.1, w) =
      (@Homeomorph.toEquiv (TotalSpace (Fin n → K) E) (TotalSpace P E) C tP H).symm
        (A.invCoord i b ((A.rankReindex n i hi).symm w)) := by
  subst n
  rfl

/-- The inverse transported chart recovers the same original fibre vector as the original
coordinate linear equivalence. -/
theorem fixedRankTrivialization_symm_eq_mk (i : A.Index) (hi : A.rank i = n)
    {b : B} (hb : b ∈ (A.chart i).baseSet) (w : Fin n → K) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi)))).symm (b, w) =
      TotalSpace.mk b ((A.coordLinearEquiv i hb).symm
        ((A.rankReindex n i hi).symm w)) := by
  rw [A.fixedRankTrivialization_symm n i hi ⟨b, hb⟩,
    A.invCoord_eq_mk_coordLinearEquiv_symm i hb]
  rfl

/-- Transported charts are linear for the original fibre module structures. -/
theorem fixedRankTrivialization_isLinear (i : A.Index) (hi : A.rank i = n) :
    @Trivialization.IsLinear K B (Fin n → K) E
      inferInstance inferInstance inferInstance C
      inferInstance inferInstance inferInstance inferInstance
      (A.fixedRankTrivialization n i hi) := by
  subst n
  let : TopologicalSpace (TotalSpace (Fin (A.rank i) → K) E) :=
    TotalSpace.changeModelTopology P (Fin (A.rank i) → K) E tP
  apply (Trivialization.isFiberwiseLinear_iff_isLinear _).mp
  constructor
  · intro b hb v w
    exact (A.linear i).map_add b hb v w
  · intro b hb c v
    exact (A.linear i).map_smul b hb c v

include A in
/-- The unchanged original fibre topology is induced by inclusion in the transported total space. -/
theorem fixedRankTotalSpaceMk_isInducing (b : B) :
    @IsInducing (E b) (TotalSpace (Fin n → K) E) inferInstance C
      (TotalSpace.mk b) := by
  let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  exact (H).symm.isInducing.comp (A.inducing b)

/-- Charts retained by equality of rank still cover the whole base. An empty base does not
require the retained index type to be inhabited. -/
theorem exists_mem_fixedRankTrivialization_baseSet
    (hn : ∀ b, Module.finrank K (E b) = n) (b : B) :
    ∃ i : {i : A.Index // A.rank i = n},
      b ∈ @Trivialization.baseSet B (Fin n → K) (TotalSpace (Fin n → K) E)
        inferInstance inferInstance C TotalSpace.proj
        (A.fixedRankTrivialization n i.1 i.2) := by
  obtain ⟨i, hb⟩ := A.cover b
  refine ⟨⟨i, A.rank_eq_of_mem n hn i b hb⟩, ?_⟩
  simpa only [fixedRankTrivialization_baseSet] using hb

/-- Named whole-base fibre-bundle data for a constant-finrank atlas. Its atlas is exactly
the range of the transported rank-`n` charts, and its fibre and total-space topologies are
the original fibre topologies and the named transported topology. This is not an instance. -/
@[instance_reducible] noncomputable def fiberBundleOfFinrank
    (hn : ∀ b, Module.finrank K (E b) = n) :
    @FiberBundle B (Fin n → K) inferInstance inferInstance E C inferInstance := by
  letI : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  let indexAt (b : B) : {i : A.Index // A.rank i = n} :=
    Classical.choose (A.exists_mem_fixedRankTrivialization_baseSet n hn b)
  have indexAt_mem (b : B) :
      b ∈ (A.fixedRankTrivialization n (indexAt b).1 (indexAt b).2).baseSet :=
    Classical.choose_spec (A.exists_mem_fixedRankTrivialization_baseSet n hn b)
  exact
    { totalSpaceMk_isInducing' := A.fixedRankTotalSpaceMk_isInducing n
      trivializationAtlas' := Set.range
        (fun i : {i : A.Index // A.rank i = n} =>
          A.fixedRankTrivialization n i.1 i.2)
      trivializationAt' := fun b => A.fixedRankTrivialization n
        (indexAt b).1 (indexAt b).2
      mem_baseSet_trivializationAt' := indexAt_mem
      trivialization_mem_atlas' := fun b => ⟨indexAt b, rfl⟩ }

/-- The named whole-base atlas consists exactly of the transported retained charts. -/
@[simp] theorem fiberBundleOfFinrank_trivializationAtlas
    (hn : ∀ b, Module.finrank K (E b) = n) :
    @FiberBundle.trivializationAtlas' B (Fin n → K) inferInstance inferInstance E C
      inferInstance (A.fiberBundleOfFinrank n hn) =
        Set.range (fun i : {i : A.Index // A.rank i = n} =>
          A.fixedRankTrivialization n i.1 i.2) := rfl

/-- Membership in the constructed atlas is precisely being one of the retained charts. -/
theorem mem_fiberBundleOfFinrank_atlas_iff
    (hn : ∀ b, Module.finrank K (E b) = n)
    (e : @Trivialization B (Fin n → K) (TotalSpace (Fin n → K) E)
      inferInstance inferInstance C TotalSpace.proj) :
    e ∈ @FiberBundle.trivializationAtlas' B (Fin n → K) inferInstance inferInstance E C
      inferInstance (A.fiberBundleOfFinrank n hn) ↔
      ∃ (i : A.Index) (hi : A.rank i = n), A.fixedRankTrivialization n i hi = e := by
  rw [A.fiberBundleOfFinrank_trivializationAtlas n hn]
  constructor
  · rintro ⟨⟨i, hi⟩, he⟩
    exact ⟨i, hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, he⟩

/-- The chart chosen by the named bundle data covers its specified base point. -/
theorem fiberBundleOfFinrank_mem_baseSet_trivializationAt
    (hn : ∀ b, Module.finrank K (E b) = n) (b : B) :
    b ∈ @Trivialization.baseSet B (Fin n → K) (TotalSpace (Fin n → K) E)
      inferInstance inferInstance C TotalSpace.proj
      (@FiberBundle.trivializationAt' B (Fin n → K) inferInstance inferInstance E C
        inferInstance (A.fiberBundleOfFinrank n hn) b) :=
  @FiberBundle.mem_baseSet_trivializationAt' B (Fin n → K) inferInstance inferInstance E C
    inferInstance (A.fiberBundleOfFinrank n hn) b

/-- The chart chosen at a point belongs to exactly the constructed retained atlas. -/
theorem fiberBundleOfFinrank_trivializationAt_mem_atlas
    (hn : ∀ b, Module.finrank K (E b) = n) (b : B) :
    @FiberBundle.trivializationAt' B (Fin n → K) inferInstance inferInstance E C
      inferInstance (A.fiberBundleOfFinrank n hn) b ∈
        @FiberBundle.trivializationAtlas' B (Fin n → K) inferInstance inferInstance E C
          inferInstance (A.fiberBundleOfFinrank n hn) :=
  @FiberBundle.trivialization_mem_atlas' B (Fin n → K) inferInstance inferInstance E C
    inferInstance (A.fiberBundleOfFinrank n hn) b

/-- A chosen chart comes from an original covering chart of rank `n`. -/
theorem fiberBundleOfFinrank_trivializationAt_eq
    (hn : ∀ b, Module.finrank K (E b) = n) (b : B) :
    ∃ (i : A.Index) (hi : A.rank i = n),
      @FiberBundle.trivializationAt' B (Fin n → K) inferInstance inferInstance E C
        inferInstance (A.fiberBundleOfFinrank n hn) b = A.fixedRankTrivialization n i hi ∧
      b ∈ (A.chart i).baseSet := by
  obtain ⟨i, hi, he⟩ := (A.mem_fiberBundleOfFinrank_atlas_iff n hn _).mp
    (A.fiberBundleOfFinrank_trivializationAt_mem_atlas n hn b)
  refine ⟨i, hi, he.symm, ?_⟩
  simpa only [← he, fixedRankTrivialization_baseSet] using
    A.fiberBundleOfFinrank_mem_baseSet_trivializationAt n hn b

/-- Every chart in the specific constructed atlas is linear for the unchanged fibre modules. -/
theorem fiberBundleOfFinrank_isLinear
    (hn : ∀ b, Module.finrank K (E b) = n)
    (e : @Trivialization B (Fin n → K) (TotalSpace (Fin n → K) E)
      inferInstance inferInstance C TotalSpace.proj)
    (he : e ∈ @FiberBundle.trivializationAtlas' B (Fin n → K) inferInstance inferInstance E C
      inferInstance (A.fiberBundleOfFinrank n hn)) :
    @Trivialization.IsLinear K B (Fin n → K) E
      inferInstance inferInstance inferInstance C
      inferInstance inferInstance inferInstance inferInstance e := by
  obtain ⟨i, hi, rfl⟩ := (A.mem_fiberBundleOfFinrank_atlas_iff n hn e).mp he
  exact A.fixedRankTrivialization_isLinear n i hi

/-- The existing original-coordinate patch, with its existing topology, is homeomorphic to
the corresponding subspace of the transported whole total space. Both maps preserve the
original base point and vector. No rank equality or nonempty-domain hypothesis is needed. -/
def fixedRankPatchHomeomorph (i : A.Index) :
    @Homeomorph
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
      (A.patchTopology i) (TopologicalSpace.induced Subtype.val C) := by
  letI : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  let h : {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet} ≃ₜ
      {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet} :=
    (H).subtype (fun _ => Iff.rfl)
  exact @Homeomorph.trans
    (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
    {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet}
    {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
    (A.patchTopology i) inferInstance (TopologicalSpace.induced Subtype.val C)
    (A.patchTotalSpaceHomeomorph i) h.symm

/-- The patch comparison preserves each original vector and base point. -/
@[simp] theorem fixedRankPatchHomeomorph_mk (i : A.Index)
    (b : (A.chart i).baseSet) (v : E b.1) :
    (@Homeomorph.toEquiv
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
      (A.patchTopology i) (TopologicalSpace.induced Subtype.val C)
      (A.fixedRankPatchHomeomorph n i)) (TotalSpace.mk b v) =
        ⟨TotalSpace.mk b.1 v, b.2⟩ := rfl

/-- The inverse patch comparison retains the same original fibre vector. -/
@[simp] theorem fixedRankPatchHomeomorph_symm_apply (i : A.Index)
    (p : {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}) :
    (@Homeomorph.toEquiv
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
      (A.patchTopology i) (TopologicalSpace.induced Subtype.val C)
      (A.fixedRankPatchHomeomorph n i)).symm p =
        TotalSpace.mk ⟨p.1.proj, p.2⟩ p.1.snd := rfl

/-- Pulling back the whole-base transported topology along patch inclusion gives exactly
the existing patch topology, including on empty chart domains. -/
theorem fixedRankPatch_induced_topology (i : A.Index) :
    TopologicalSpace.induced
      (fun p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1) =>
        (TotalSpace.mk p.proj.1 p.snd : TotalSpace (Fin n → K) E)) C =
      A.patchTopology i := by
  let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
  let : TopologicalSpace
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :=
    A.patchTopology i
  have hfun :
      Subtype.val ∘ (A.fixedRankPatchHomeomorph n i) =
        (fun p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1) =>
          (TotalSpace.mk p.proj.1 p.snd : TotalSpace (Fin n → K) E)) := by
    funext p
    cases p with
    | mk b v =>
      simpa only [Function.comp_def, Homeomorph.coe_toEquiv] using
        congrArg Subtype.val (A.fixedRankPatchHomeomorph_mk n i b v)
  simpa only [induced_compose, hfun] using
    (A.fixedRankPatchHomeomorph n i).induced_eq

/-- Whole-base fixed-rank coordinates on a patch agree with the existing patch product
homeomorphism, with only equality reindexing of the finite model. -/
theorem fixedRankTrivialization_patchProductHomeomorph (i : A.Index) (hi : A.rank i = n)
    (p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi))))
      ((@Homeomorph.toEquiv
        (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
        {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
        (A.patchTopology i) (TopologicalSpace.induced Subtype.val C)
        (A.fixedRankPatchHomeomorph n i)) p).1 =
      ((((@Homeomorph.toEquiv
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K))
          (A.patchTopology i) inferInstance (A.patchProductHomeomorph i)) p).1 : B),
        A.rankReindex n i hi ((@Homeomorph.toEquiv
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K))
          (A.patchTopology i) inferInstance (A.patchProductHomeomorph i)) p).2) := by
  cases p with
  | mk b v =>
    rw [A.fixedRankPatchHomeomorph_mk n i b v,
      A.fixedRankTrivialization_mk n i hi b.2 v]
    simp only [Homeomorph.coe_toEquiv, A.patchProductHomeomorph_mk i b v]

/-- The existing patch trivialization and the whole-base fixed-rank trivialization have
exactly the same local product coordinates after equality reindexing. -/
theorem fixedRankTrivialization_patchTrivialization (i : A.Index) (hi : A.rank i = n)
    (p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :
    (@PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i hi))))
      ((@Homeomorph.toEquiv
        (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
        {p : TotalSpace (Fin n → K) E // p.proj ∈ (A.chart i).baseSet}
        (A.patchTopology i) (TopologicalSpace.induced Subtype.val C)
        (A.fixedRankPatchHomeomorph n i)) p).1 =
      ((((@PartialHomeomorph.toPartialEquiv
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K)) (A.patchTopology i) inferInstance
          (@OpenPartialHomeomorph.toPartialHomeomorph
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            ((A.chart i).baseSet × (Fin (A.rank i) → K)) (A.patchTopology i) inferInstance
            (@Trivialization.toOpenPartialHomeomorph
              (A.chart i).baseSet (Fin (A.rank i) → K)
              (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
              inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
              (A.patchTrivialization i)))) p).1 : B),
        A.rankReindex n i hi ((@PartialHomeomorph.toPartialEquiv
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K)) (A.patchTopology i) inferInstance
          (@OpenPartialHomeomorph.toPartialHomeomorph
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            ((A.chart i).baseSet × (Fin (A.rank i) → K)) (A.patchTopology i) inferInstance
            (@Trivialization.toOpenPartialHomeomorph
              (A.chart i).baseSet (Fin (A.rank i) → K)
              (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
              inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
              (A.patchTrivialization i)))) p).2) :=
  A.fixedRankTrivialization_patchProductHomeomorph n i hi p

/-- An independent total-space topology agrees with the named transported topology if the
retained original partial equivalences are trivializations for it. Equality is proved from
the chart cover, not assumed through a homeomorphism. -/
theorem eq_changeModelTopology_of_fixedRankTrivializations
    (hn : ∀ b, Module.finrank K (E b) = n)
    (σ : TopologicalSpace (TotalSpace (Fin n → K) E))
    (eσ : (i : {i : A.Index // A.rank i = n}) →
      @Trivialization B (Fin n → K) (TotalSpace (Fin n → K) E)
        inferInstance inferInstance σ TotalSpace.proj)
    (he : ∀ i,
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) σ inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin n → K) E) (B × (Fin n → K)) σ inferInstance
          (@Trivialization.toOpenPartialHomeomorph
            B (Fin n → K) (TotalSpace (Fin n → K) E)
            inferInstance inferInstance σ TotalSpace.proj (eσ i)))) =
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
          (@Trivialization.toOpenPartialHomeomorph
            B (Fin n → K) (TotalSpace (Fin n → K) E)
            inferInstance inferInstance C TotalSpace.proj
            (A.fixedRankTrivialization n i.1 i.2))))) : σ = C := by
  apply TopologicalSpace.ext_nhds
  intro p
  obtain ⟨i, hi⟩ := A.exists_mem_fixedRankTrivialization_baseSet n hn p.proj
  let peσ : PartialEquiv (TotalSpace (Fin n → K) E) (B × (Fin n → K)) :=
    @PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) σ inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) σ inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance σ TotalSpace.proj (eσ i)))
  let peC : PartialEquiv (TotalSpace (Fin n → K) E) (B × (Fin n → K)) :=
    @PartialHomeomorph.toPartialEquiv
      (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
      (@OpenPartialHomeomorph.toPartialHomeomorph
        (TotalSpace (Fin n → K) E) (B × (Fin n → K)) C inferInstance
        (@Trivialization.toOpenPartialHomeomorph
          B (Fin n → K) (TotalSpace (Fin n → K) E)
          inferInstance inferInstance C TotalSpace.proj
          (A.fixedRankTrivialization n i.1 i.2)))
  have he' : peσ = peC := he i
  have hC : p ∈ peC.source := by
    let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
    exact (A.fixedRankTrivialization n i.1 i.2).mem_source.mpr hi
  have hs : peσ.source = peC.source := congrArg PartialEquiv.source he'
  have hσ : p ∈ peσ.source := hs.symm ▸ hC
  have hf : (peσ : TotalSpace (Fin n → K) E → B × (Fin n → K)) = peC :=
    congrArg (fun e : PartialEquiv (TotalSpace (Fin n → K) E) (B × (Fin n → K)) =>
      (e : TotalSpace (Fin n → K) E → B × (Fin n → K))) he'
  have hσnhds : @nhds (TotalSpace (Fin n → K) E) σ p =
      Filter.comap (peσ : TotalSpace (Fin n → K) E → B × (Fin n → K)) (𝓝 (peσ p)) ⊓
        Filter.principal peσ.source := by
    let : TopologicalSpace (TotalSpace (Fin n → K) E) := σ
    exact (eσ i).nhds_eq_comap_inf_principal hσ
  have hCnhds : @nhds (TotalSpace (Fin n → K) E) C p =
      Filter.comap (peC : TotalSpace (Fin n → K) E → B × (Fin n → K)) (𝓝 (peC p)) ⊓
        Filter.principal peC.source := by
    let : TopologicalSpace (TotalSpace (Fin n → K) E) := C
    exact (A.fixedRankTrivialization n i.1 i.2).nhds_eq_comap_inf_principal hC
  rw [hσnhds, hCnhds, hf, hs]

end Topological

section Normed

variable {K : Type uK} [NontriviallyNormedField K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [tP : TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) (n : ℕ)

/-- A constant-finrank atlas over a nontrivially normed field gives a vector-bundle mixin
for exactly `fiberBundleOfFinrank`, its retained atlas, and the named transported topology.
The scalar topology is the canonical norm topology already used by the input atlas. No
completeness, fibre norms or additional fibre finite-dimensionality assumptions are needed. -/
theorem vectorBundleOfFinrank (hn : ∀ b, Module.finrank K (E b) = n) :
    letI : TopologicalSpace (TotalSpace (Fin n → K) E) :=
      TotalSpace.changeModelTopology P (Fin n → K) E tP
    letI : FiberBundle (Fin n → K) E := A.fiberBundleOfFinrank n hn
    letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
    letI : IsModuleTopology K (Fin n → K) := IsModuleTopology.instPi
    VectorBundle K (Fin n → K) E :=
  letI : TopologicalSpace (TotalSpace (Fin n → K) E) :=
    TotalSpace.changeModelTopology P (Fin n → K) E tP
  letI : FiberBundle (Fin n → K) E := A.fiberBundleOfFinrank n hn
  letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
  letI : IsModuleTopology K (Fin n → K) := IsModuleTopology.instPi
  (show VectorBundle K (Fin n → K) E from
    VectorBundle.of_isLinear (A.fiberBundleOfFinrank_isLinear n hn))

end Normed

end Bundle.FiniteRankAtlas
