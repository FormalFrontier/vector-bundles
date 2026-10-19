/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Embedding a bundle into a finite power of its model

A vector bundle on a compact normal base has a base-preserving, fiberwise linear
embedding into a trivial bundle whose fiber is a finite power of the model. Real
weights act only on the model, through a continuous real module structure. The model
need not be finite-dimensional or complete, and the base need not be Hausdorff.

`VectorBundle.finiteTrivialEmbedding` retains the number of model copies, the fiber
linear maps, and the continuous total-space embedding together. Its projections and
application lemmas refer to this same choice. The domain has its given total-space
topology; the target has the product topology on the base and the finite model power.

The coordinate construction uses a finite chart cover and a subordinate
`BumpCovering` without converting it to a partition of unity. Some cutoff is one on
a neighborhood of each base point. On that neighborhood, applying the inverse chart
to the corresponding coordinate is a continuous local left inverse. The continuity
of weighted coordinates at chart boundaries uses containment of their topological
supports in the chart domains. Continuous additive maps commute with real scalar
multiplication, so no scalar-commutation hypothesis is needed.

## Limitations

The induced range bundle and a finite-rank complement are not constructed here.
A finite power of an infinite-dimensional model is not asserted to be finite-dimensional.
Hatcher's compact Hausdorff setting implies the compact normal hypotheses used here;
the finite-rank real and complex complement conclusion additionally requires the
image-bundle and orthogonal-sum steps.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, November 2017,
  Proposition 1.4, printed page 13 (PDF page 17): weighted local coordinates followed
  by the complement construction of Proposition 1.3.
* Mathlib's bundle and trivialization formalizations by Nicolò Cavalleri,
  Sébastien Gouëzel, Heather Macbeth, Patrick Massot, and Floris van Doorn.
* Mathlib's `BumpCovering` and continuous-additive real-linearity formalizations by
  Yury Kudryashov, and its compactness formalization by Johannes Hölzl,
  Mario Carneiro, and Yury Kudryashov.
-/

@[expose] public section

noncomputable section

open Bundle Topology

namespace VectorBundle

universe u𝕜 uB uF uE

private theorem continuous_weighted_trivialization
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [Module ℝ F] [ContinuousSMul ℝ F]
    {E : B → Type uE} [TopologicalSpace (TotalSpace F E)]
    (hπ : Continuous (π F E)) (e : Trivialization F (π F E)) (ρ : C(B, ℝ))
    (hρ : tsupport (ρ : B → ℝ) ⊆ e.baseSet) :
    Continuous (fun p : TotalSpace F E ↦ ρ p.proj • (e p).2) := by
  refine continuous_of_tsupport fun p hp ↦ ?_
  have hb : p.proj ∈ tsupport (ρ : B → ℝ) :=
    tsupport_comp_subset_preimage (ρ : B → ℝ) hπ
      (tsupport_smul_subset_left (fun q : TotalSpace F E ↦ ρ q.proj)
        (fun q ↦ (e q).2) hp)
  exact (ρ.continuous.comp hπ).continuousAt.smul
    (e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr (hρ hb))).snd

section ScalarCompatibility

variable (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Module ℝ F] [ContinuousSMul ℝ F]

private theorem smul_real_comm (a : 𝕜) (r : ℝ) (v : F) :
    a • (r • v) = r • (a • v) :=
  map_real_smul (smulAddHom 𝕜 F a) (continuous_const.smul continuous_id) r v

end ScalarCompatibility

section Construction

open Filter Set

private theorem isEmbedding_weightedTrivializationMap
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [AddCommMonoid F] [Module ℝ F] [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    {ι : Type*} (e : ι → Trivialization F (π F E))
    (φ : BumpCovering ι B univ) (hφ : φ.IsSubordinate (fun i => (e i).baseSet))
    (f : C(TotalSpace F E, B × (ι → F)))
    (hf : ∀ p, f p = (p.proj, fun i => φ i p.proj • (e i p).2)) :
    IsEmbedding f := by
  have hbase (i : ι) (q : TotalSpace F E) (hq : φ i q.proj = 1) :
      q.proj ∈ (e i).baseSet := by
    apply hφ i
    apply subset_closure
    change φ i q.proj ≠ 0
    rw [hq]
    exact one_ne_zero
  have hleft (i : ι) (q : TotalSpace F E) (hq : φ i q.proj = 1) :
      (e i).toOpenPartialHomeomorph.symm ((f q).1, (f q).2 i) = q := by
    simp only [hf q, hq, one_smul]
    exact (e i).symm_apply_mk_proj ((e i).mem_source.mpr (hbase i q hq))
  refine ⟨isInducing_iff_nhds.mpr (fun p => ?_), ?_⟩
  · let i := φ.ind p.proj (mem_univ _)
    have hplateau : ∀ᶠ b in 𝓝 p.proj, φ i b = 1 := φ.eventuallyEq_one _ _
    have hpi : φ i p.proj = 1 := φ.ind_apply _ _
    let g : B × (ι → F) → TotalSpace F E :=
      fun z => (e i).toOpenPartialHomeomorph.symm (z.1, z.2 i)
    have hgp : g (f p) = p := hleft i p hpi
    have hg : ContinuousAt g (f p) := by
      apply ((e i).toOpenPartialHomeomorph.continuousAt_symm ?_).comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)).continuousAt
      exact (e i).mem_target.mpr (by simpa only [hf p] using hbase i p hpi)
    apply le_antisymm (f.continuous.continuousAt.le_comap)
    -- The plateau is a neighborhood on the target side, so the local inverse also
    -- recovers points along the pulled-back target neighborhood filter.
    have heq : (g ∘ f) =ᶠ[comap f (𝓝 (f p))] id := by
      have hb : ∀ᶠ z : B × (ι → F) in 𝓝 (f p), φ i z.1 = 1 := by
        have hfst : Tendsto (Prod.fst : B × (ι → F) → B) (𝓝 (f p)) (𝓝 p.proj) := by
          simpa only [hf p] using (continuous_fst.continuousAt (x := f p)).tendsto
        exact hfst.eventually hplateau
      filter_upwards [tendsto_comap.eventually hb] with q hq
      apply hleft i q
      simpa only [hf q] using hq
    have ht : Tendsto (g ∘ f) (comap f (𝓝 (f p))) (𝓝 p) := by
      have ht' := hg.tendsto.comp (tendsto_comap :
        Tendsto (⇑f) (comap f (𝓝 (f p))) (𝓝 (f p)))
      simpa only [hgp] using ht'
    simpa only [Tendsto, map_id] using ht.congr' heq
  · intro p q hpq
    let i := φ.ind p.proj (mem_univ _)
    have hpi : φ i p.proj = 1 := φ.ind_apply _ _
    have hpqbase : p.proj = q.proj := by simpa only [hf p, hf q] using congrArg Prod.fst hpq
    have hqi : φ i q.proj = 1 := hpqbase ▸ hpi
    rw [← hleft i p hpi, ← hleft i q hqi, hpq]

/-- A base-preserving, fiberwise linear embedding into a finite power of the model,
retaining the number of copies, the fiber linear maps, and the continuous embedding.
This is the weighted-coordinate embedding step of Hatcher's Proposition 1.4. -/
def finiteTrivialEmbedding (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [Module ℝ F] [ContinuousSMul ℝ F] (E : B → Type uE)
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [CompactSpace B] [NormalSpace B] :
    Σ m : ℕ, Σ L : (∀ b, E b →ₗ[𝕜] (Fin m → F)),
      { f : C(TotalSpace F E, B × (Fin m → F)) //
          IsEmbedding f ∧
          ∀ b v, f (TotalSpace.mk' F b v) = (b, L b v) } := by
  classical
  apply Classical.choice
  -- Select a finite family of genuine bundle charts, retaining their linearity.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b => (trivializationAt F E b).baseSet)
    (fun b => (trivializationAt F E b).open_baseSet)
    (by intro b _; exact mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F E b⟩)
  let c : Fin t.card ≃ t := t.equivFin.symm
  let e : Fin t.card → Trivialization F (π F E) :=
    fun i => trivializationAt F E (c i).val
  let : ∀ i, (e i).IsLinear 𝕜 := fun i =>
    inferInstanceAs ((trivializationAt F E (c i).val).IsLinear 𝕜)
  have hcover : univ ⊆ ⋃ i, (e i).baseSet := by
    intro b _
    obtain ⟨a, ha, hb⟩ := mem_iUnion₂.mp (ht (mem_univ b))
    obtain ⟨i, hi⟩ := c.surjective ⟨a, ha⟩
    apply mem_iUnion.mpr ⟨i, ?_⟩
    change b ∈ (trivializationAt F E (c i).val).baseSet
    rw [hi]
    exact hb
  obtain ⟨φ, hφ⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite isClosed_univ
    (fun i => (e i).baseSet) (fun i => (e i).open_baseSet)
    (locallyFinite_of_finite _) hcover
  -- Weight only the model coordinates; the real scalar operators are 𝕜-linear.
  let L : ∀ b, E b →ₗ[𝕜] (Fin t.card → F) := fun b =>
    LinearMap.pi fun i =>
      { toFun := fun v => φ i b • (e i).linearMapAt 𝕜 b v
        map_add' := by intro v w; rw [map_add, smul_add]
        map_smul' := by
          intro a v
          rw [map_smul]
          exact (smul_real_comm 𝕜 F a (φ i b) _).symm }
  let f : C(TotalSpace F E, B × (Fin t.card → F)) :=
    ⟨fun p => (p.proj, fun i => φ i p.proj • (e i p).2), by
      exact (FiberBundle.continuous_proj F E).prodMk
        (continuous_pi fun i => continuous_weighted_trivialization
          (FiberBundle.continuous_proj F E) (e i) (φ i) (hφ i))⟩
  have hL (b : B) (v : E b) :
      L b v = fun i => φ i b • (e i (TotalSpace.mk' F b v)).2 := by
    funext i
    change φ i b • ((e i).linearMapAt 𝕜 b v) = _
    rw [Trivialization.linearMapAt_apply]
    split_ifs with hb
    · rfl
    · have hzero : φ i b = 0 := by
        by_contra hne
        exact hb (hφ i (subset_closure hne))
      simp only [hzero, zero_smul]
  exact ⟨⟨t.card, L, f,
    ⟨by exact isEmbedding_weightedTrivializationMap e φ hφ f (fun _ => rfl),
      fun b v => congrArg (Prod.mk b) (hL b v).symm⟩⟩⟩

end Construction

variable (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Module ℝ F] [ContinuousSMul ℝ F] (E : B → Type uE)
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [CompactSpace B] [NormalSpace B]

/-- The number of copies of the model in the chosen finite trivial-bundle embedding. -/
def finiteTrivialEmbeddingCopies : ℕ :=
  (finiteTrivialEmbedding 𝕜 F E).1

/-- The fiber linear map in the chosen finite trivial-bundle embedding. Its target uses
exactly the number of model copies selected by `finiteTrivialEmbedding`. -/
def finiteTrivialEmbeddingLinearMap (b : B) :
    E b →ₗ[𝕜] (Fin (finiteTrivialEmbeddingCopies 𝕜 F E) → F) :=
  (finiteTrivialEmbedding 𝕜 F E).2.1 b

/-- The continuous total-space map in the chosen finite trivial-bundle embedding,
with the given domain topology and the product topology on its target. -/
def finiteTrivialEmbeddingMap :
    C(TotalSpace F E, B × (Fin (finiteTrivialEmbeddingCopies 𝕜 F E) → F)) :=
  (finiteTrivialEmbedding 𝕜 F E).2.2.1

/-- On a fiber, the total-space embedding is given by its chosen linear map. -/
@[simp]
theorem finiteTrivialEmbeddingMap_apply (b : B) (v : E b) :
    finiteTrivialEmbeddingMap 𝕜 F E (TotalSpace.mk' F b v) =
      (b, finiteTrivialEmbeddingLinearMap 𝕜 F E b v) :=
  (finiteTrivialEmbedding 𝕜 F E).2.2.2.2 b v

/-- The chosen finite trivial-bundle embedding preserves the base coordinate. -/
@[simp]
theorem finiteTrivialEmbeddingMap_fst (p : TotalSpace F E) :
    (finiteTrivialEmbeddingMap 𝕜 F E p).1 = p.proj := by
  rcases p with ⟨b, v⟩
  exact congrArg Prod.fst (finiteTrivialEmbeddingMap_apply 𝕜 F E b v)

/-- The chosen map is an embedding for the given total-space topology. -/
theorem isEmbedding_finiteTrivialEmbeddingMap :
    IsEmbedding (finiteTrivialEmbeddingMap 𝕜 F E) :=
  (finiteTrivialEmbedding 𝕜 F E).2.2.2.1

/-- Every chosen fiber linear map is injective. -/
theorem finiteTrivialEmbeddingLinearMap_injective (b : B) :
    Function.Injective (finiteTrivialEmbeddingLinearMap 𝕜 F E b) := by
  intro v w h
  apply TotalSpace.mk_injective (F := F) b
  apply (isEmbedding_finiteTrivialEmbeddingMap 𝕜 F E).injective
  simpa only [finiteTrivialEmbeddingMap_apply] using congrArg (Prod.mk b) h

end VectorBundle
