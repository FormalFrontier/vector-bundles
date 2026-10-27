/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Finite-rank atlases

A `Bundle.FiniteRankAtlas` describes a vector bundle by local trivializations whose finite
ranks may depend on the chart. The topology and vector space operations on each fibre,
and the topology on the total space, are parameters rather than constructions.

The type parameter of `Bundle.TotalSpace` is independent of every chart model. In
particular, an atlas does not assume a global fixed-model `FiberBundle` instance.

The atlas data only require a topology on the scalar field. This does not by itself
assert that field operations or fibre operations are continuous. Results concerning
continuous vector space operations require the corresponding scalar continuity hypotheses.

## Implementation notes

`Trivialization.IsFiberwiseLinear` expresses linearity for trivializations with an
arbitrary total-space parameter. It only requires linearity over the chart's base set.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), §1.1.
* The fibre-bundle and vector-bundle APIs of Mathlib.
-/

@[expose] public section

open Bundle Topology

universe uK uB uE uP uF uI

namespace Bundle.Trivialization

variable {K : Type uK} [Semiring K]
variable {B : Type uB} [TopologicalSpace B]
variable {E : B → Type uE} {P : Type uP}
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
variable [TopologicalSpace (TotalSpace P E)]
variable {F : Type uF} [AddCommMonoid F] [Module K F] [TopologicalSpace F]

/-- A trivialization is fibrewise linear on its base set. The total-space parameter
need not coincide with the chart model. No linearity is required outside the base set. -/
structure IsFiberwiseLinear
    (e : Trivialization F (TotalSpace.proj : TotalSpace P E → B)) : Prop where
  /-- Additivity on a fibre lying in the base set. -/
  map_add : ∀ (b : B), b ∈ e.baseSet → ∀ v w : E b,
    (e (TotalSpace.mk b (v + w))).2 =
      (e (TotalSpace.mk b v)).2 + (e (TotalSpace.mk b w)).2
  /-- Compatibility with scalar multiplication on a fibre lying in the base set. -/
  map_smul : ∀ (b : B), b ∈ e.baseSet → ∀ (c : K) (v : E b),
    (e (TotalSpace.mk b (c • v))).2 = c • (e (TotalSpace.mk b v)).2

/-- The linear map on a fibre supplied by a fibrewise-linear trivialization. -/
def IsFiberwiseLinear.linearMap
    {e : Trivialization F (TotalSpace.proj : TotalSpace P E → B)}
    (h : e.IsFiberwiseLinear (K := K)) {b : B} (hb : b ∈ e.baseSet) : E b →ₗ[K] F where
  toFun v := (e (TotalSpace.mk b v)).2
  map_add' := h.map_add b hb
  map_smul' := h.map_smul b hb

/-- The fibrewise linear map evaluates to the second coordinate of the chart. -/
@[simp] theorem IsFiberwiseLinear.linearMap_apply
    {e : Trivialization F (TotalSpace.proj : TotalSpace P E → B)}
    (h : e.IsFiberwiseLinear (K := K)) {b : B} (hb : b ∈ e.baseSet) (v : E b) :
    h.linearMap hb v = (e (TotalSpace.mk b v)).2 := rfl

/-- On a fixed-model total space, fibrewise linearity agrees exactly with the
linearity condition for a fixed-model trivialization. -/
theorem isFiberwiseLinear_iff_isLinear [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) :
    e.IsFiberwiseLinear (K := K) ↔ Trivialization.IsLinear K e := by
  constructor
  · intro h
    constructor
    intro b hb
    exact ⟨h.map_add b hb, h.map_smul b hb⟩
  · intro h
    constructor
    · intro b hb v w
      exact (h.linear b hb).map_add v w
    · intro b hb c v
      exact (h.linear b hb).map_smul c v

end Bundle.Trivialization

namespace Bundle

variable (K : Type uK) [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable (P : Type uP) (E : B → Type uE)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]

/-- A covering atlas of finite-dimensional, fibrewise-linear trivializations of a given
bundle. The finite rank can vary between charts and need not have a global bound.

The total-space topology, fibre topologies, and fibre module structures are all given.
`inducing` asserts that these given fibre topologies are the topologies induced from the
given total space. The atlas retains its chart data, with a chart-index universe
independent of the base and fibre universes. -/
@[ext] structure FiniteRankAtlas where
  /-- The type indexing the charts. -/
  Index : Type uI
  /-- The finite dimension of each chart model. -/
  rank : Index → ℕ
  /-- The charts, each with its own finite-dimensional standard model. -/
  chart : (i : Index) →
    Trivialization (Fin (rank i) → K) (TotalSpace.proj : TotalSpace P E → B)
  /-- Each chart is linear on fibres over its base set. -/
  linear : ∀ i, (chart i).IsFiberwiseLinear (K := K)
  /-- The chart domains cover the base. -/
  cover : ∀ b : B, ∃ i, b ∈ (chart i).baseSet
  /-- The given fibre topology agrees with its topology inside the given total space. -/
  inducing : ∀ b : B, IsInducing (TotalSpace.mk b : E b → TotalSpace P E)

namespace FiniteRankAtlas

variable {K P E}
variable (A : FiniteRankAtlas K P E)

/-- A total-space point belongs to a chart source precisely when its base point
belongs to the chart base set. -/
@[simp] theorem mem_source_iff (i : A.Index) (p : TotalSpace P E) :
    p ∈ (A.chart i).source ↔ p.proj ∈ (A.chart i).baseSet := by
  rw [(A.chart i).source_eq]
  rfl

/-- Chart membership for a vector in a specified fibre. -/
@[simp] theorem mk_mem_source_iff (i : A.Index) (b : B) (v : E b) :
    TotalSpace.mk b v ∈ (A.chart i).source ↔ b ∈ (A.chart i).baseSet :=
  A.mem_source_iff i (TotalSpace.mk b v)

/-- Every chart preserves the original bundle projection on its source. -/
theorem chart_proj (i : A.Index) (p : TotalSpace P E) (hp : p ∈ (A.chart i).source) :
    (A.chart i p).1 = p.proj :=
  (A.chart i).proj_toFun p hp

/-- A chart identifies its original total-space source, with the inherited subspace
topology, with the product of its base set and its standard finite-dimensional model. -/
def sourceHomeomorph (i : A.Index) :
    (A.chart i).source ≃ₜ (A.chart i).baseSet × (Fin (A.rank i) → K) :=
  (A.chart i).sourceHomeomorphBaseSetProd

/-- The original-source patch homeomorphism preserves the original projection. -/
@[simp] theorem sourceHomeomorph_fst_coe (i : A.Index) (p : (A.chart i).source) :
    ((A.sourceHomeomorph i p).1 : B) = p.1.proj :=
  (A.chart i).proj_toFun p.1 p.2

/-- The second coordinate of the original-source patch homeomorphism is the chart coordinate. -/
@[simp] theorem sourceHomeomorph_snd (i : A.Index) (p : (A.chart i).source) :
    (A.sourceHomeomorph i p).2 = (A.chart i p.1).2 := rfl

/-- The coordinate of a fibre vector in a chart. This function is defined everywhere;
its linearity assertions require membership in the chart's base set. -/
def coord (i : A.Index) (b : B) (v : E b) : Fin (A.rank i) → K :=
  (A.chart i (TotalSpace.mk b v)).2

/-- Coordinates are the second component of the chart. -/
@[simp] theorem coord_apply (i : A.Index) (b : B) (v : E b) :
    A.coord i b v = (A.chart i (TotalSpace.mk b v)).2 := rfl

/-- The original-source patch homeomorphism has the same fibre coordinates as the chart. -/
@[simp] theorem sourceHomeomorph_mk_snd (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    (A.sourceHomeomorph i
      ⟨TotalSpace.mk b v, (A.mk_mem_source_iff i b v).mpr hb⟩).2 = A.coord i b v := rfl

/-- Coordinates are additive on every fibre in the chart domain. -/
theorem coord_add (i : A.Index) {b : B} (hb : b ∈ (A.chart i).baseSet) (v w : E b) :
    A.coord i b (v + w) = A.coord i b v + A.coord i b w :=
  (A.linear i).map_add b hb v w

/-- Coordinates commute with scalar multiplication on the chart domain. -/
theorem coord_smul (i : A.Index) {b : B} (hb : b ∈ (A.chart i).baseSet)
    (c : K) (v : E b) :
    A.coord i b (c • v) = c • A.coord i b v :=
  (A.linear i).map_smul b hb c v

/-- Coordinates on a fibre in the chart domain, as a linear map. -/
def coordLinearMap (i : A.Index) {b : B} (hb : b ∈ (A.chart i).baseSet) :
    E b →ₗ[K] (Fin (A.rank i) → K) :=
  (A.linear i).linearMap hb

/-- The coordinate linear map agrees with coordinate evaluation. -/
@[simp] theorem coordLinearMap_apply (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    A.coordLinearMap i hb v = A.coord i b v := rfl

/-- Every point belongs to the base set of a chart in the atlas. -/
theorem exists_mem_baseSet (b : B) : ∃ i, b ∈ (A.chart i).baseSet := A.cover b

/-- A property holding on each chart domain holds at every base point. -/
theorem induction_on {Q : B → Prop} (b : B)
    (h : ∀ i b, b ∈ (A.chart i).baseSet → Q b) : Q b := by
  obtain ⟨i, hi⟩ := A.exists_mem_baseSet b
  exact h i b hi

/-- The original total-space point with specified chart coordinates over a point in
the chart base set. -/
def invCoord (i : A.Index) (b : (A.chart i).baseSet) (w : Fin (A.rank i) → K) :
    TotalSpace P E :=
  ((A.sourceHomeomorph i).symm (b, w)).1

/-- Inverse coordinates always lie in the original chart source. -/
@[simp] theorem invCoord_mem_source (i : A.Index) (b : (A.chart i).baseSet)
    (w : Fin (A.rank i) → K) : A.invCoord i b w ∈ (A.chart i).source :=
  ((A.sourceHomeomorph i).symm (b, w)).2

/-- Inverse coordinates preserve the specified base point. -/
@[simp] theorem invCoord_proj (i : A.Index) (b : (A.chart i).baseSet)
    (w : Fin (A.rank i) → K) : (A.invCoord i b w).proj = b.1 := by
  have h := congrArg (fun q : (A.chart i).baseSet × (Fin (A.rank i) → K) => (q.1 : B))
    ((A.sourceHomeomorph i).apply_symm_apply (b, w))
  simpa only [sourceHomeomorph_fst_coe, invCoord] using h

/-- Applying a chart to inverse coordinates recovers the specified fibre coordinate. -/
@[simp] theorem chart_invCoord_snd (i : A.Index) (b : (A.chart i).baseSet)
    (w : Fin (A.rank i) → K) : (A.chart i (A.invCoord i b w)).2 = w := by
  have h := congrArg Prod.snd ((A.sourceHomeomorph i).apply_symm_apply (b, w))
  simpa only [sourceHomeomorph_snd, invCoord] using h

/-- Inverting the coordinates of a fibre vector recovers that original vector. -/
@[simp] theorem invCoord_coord (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    A.invCoord i ⟨b, hb⟩ (A.coord i b v) = TotalSpace.mk b v := by
  let p : (A.chart i).source :=
    ⟨TotalSpace.mk b v, (A.mk_mem_source_iff i b v).mpr hb⟩
  have he : A.sourceHomeomorph i p = (⟨b, hb⟩, A.coord i b v) := by
    apply Prod.ext
    · apply Subtype.ext
      exact A.sourceHomeomorph_fst_coe i p
    · exact A.sourceHomeomorph_snd i p
  have h := congrArg (fun q : (A.chart i).source => q.1)
    ((A.sourceHomeomorph i).symm_apply_apply p)
  rw [he] at h
  exact h

/-- Zero inverse coordinates give the zero vector in the original fibre. -/
@[simp] theorem invCoord_zero (i : A.Index) (b : (A.chart i).baseSet) :
    A.invCoord i b 0 = TotalSpace.mk b.1 (0 : E b.1) := by
  have hzero : A.coord i b.1 (0 : E b.1) = 0 :=
    (A.coordLinearMap i b.2).map_zero
  simpa only [hzero] using A.invCoord_coord i b.2 (0 : E b.1)

/-- Inverse coordinates are continuous into the original total space, with the product
of the original base-subspace topology and the standard coordinate topology. -/
theorem continuous_invCoord (i : A.Index) :
    Continuous (fun q : (A.chart i).baseSet × (Fin (A.rank i) → K) =>
      A.invCoord i q.1 q.2) :=
  continuous_subtype_val.comp (A.sourceHomeomorph i).symm.continuous

/-- Constant chart coordinates give a continuous local section of the original total space. -/
theorem continuous_invCoord_const (i : A.Index) (w : Fin (A.rank i) → K) :
    Continuous (fun b : (A.chart i).baseSet => A.invCoord i b w) :=
  (A.continuous_invCoord i).comp (continuous_id.prodMk continuous_const)

/-- The fixed-model total space on a chart domain, identified with the corresponding
subspace of the original total space. This equivalence does not change either fibre. -/
def patchTotalSpaceEquiv (i : A.Index) :
    TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1) ≃
      {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet} where
  toFun p := ⟨TotalSpace.mk p.proj.1 p.2, p.proj.2⟩
  invFun p := TotalSpace.mk ⟨p.1.proj, p.2⟩ p.1.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology on the fixed-model patch total space is induced by its identification
with the original total-space subspace. This is a topology on the patch only. -/
@[instance_reducible] def patchTopology (i : A.Index) :
    TopologicalSpace
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :=
  TopologicalSpace.induced (A.patchTotalSpaceEquiv i) inferInstance

/-- The fixed-model patch with its induced topology is homeomorphic to the original
patch subspace. In particular, no topology on the original total space is replaced. -/
def patchTotalSpaceHomeomorph (i : A.Index) :
    @Homeomorph
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet}
      (A.patchTopology i) inferInstance :=
  @Homeomorph.mk
    (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
    {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet}
    (A.patchTopology i)
    (inferInstance : TopologicalSpace {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet})
    (A.patchTotalSpaceEquiv i)
    (by
      rw [continuous_def]
      intro s hs
      exact ⟨s, hs, rfl⟩)
    (by
      rw [continuous_def]
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      change IsOpen ((A.patchTotalSpaceEquiv i).symm ⁻¹'
        ((A.patchTotalSpaceEquiv i) ⁻¹' t))
      have hpre : (A.patchTotalSpaceEquiv i).symm ⁻¹'
          ((A.patchTotalSpaceEquiv i) ⁻¹' t) = t := by
        ext p
        change (A.patchTotalSpaceEquiv i ((A.patchTotalSpaceEquiv i).symm p) ∈ t) ↔ p ∈ t
        rw [(A.patchTotalSpaceEquiv i).apply_symm_apply]
      rw [hpre]
      exact ht)

/-- The patch homeomorphism sends a fibre vector to the same original fibre vector. -/
@[simp] theorem patchTotalSpaceHomeomorph_mk (i : A.Index)
    (b : (A.chart i).baseSet) (v : E b.1) :
    A.patchTotalSpaceHomeomorph i (TotalSpace.mk b v) =
      ⟨TotalSpace.mk b.1 v, b.2⟩ := rfl

end FiniteRankAtlas
end Bundle
