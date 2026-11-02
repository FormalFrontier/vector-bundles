/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import VectorBundles.Topology.Maps.FiniteChartReconstruction
public import VectorBundles.Topology.Maps.FiniteChartReconstructionContinuity
public import VectorBundles.Topology.Maps.WeightedCoordinates
public import VectorBundles.Topology.VectorBundle.FiniteRank.FiberCoordinates
public import VectorBundles.Topology.VectorBundle.FiniteRank.Projection
public import VectorBundles.Topology.VectorBundle.FiniteRank.Weights

/-!
# Closed embeddings of finite-rank atlases into finite trivial bundles

A finite-rank atlas over a compact normal base admits a fibrewise-linear closed
embedding into a finite-dimensional trivial bundle. The scalar field is real or
complex. All topologies and operations on the original fibres and total space are
retained; neither a common chart rank nor a finite original chart index is required.

The construction first selects a finite family of original charts and subordinate
nonnegative real weights. `weightedEmbedding` takes values in the full dependent
product of the selected chart models, using exactly `LinearMap.weightedCoordinates`.
Every selected factor is retained, including rank-zero factors. Scalar dual
coefficients give a continuous finite chart reconstruction. The existing
reconstruction closed-embedding theorem uses separation only of the model product,
not of the base.

Finally, `embeddingModelEquiv` is the continuous linear coordinate equivalence of
`Module.finBasis` on that product. Composing with it gives `finiteTrivialEmbedding`
into `B × (Fin A.embeddingDimension → K)`. No coordinate ordering, rank-sum formula,
or isometry property of this final equivalence is asserted.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), §1.1.
* Mathlib's finite-dimensional basis and continuous linear equivalence APIs.
* The supported weighted-coordinate and finite chart reconstruction APIs of this library.
-/

@[expose] public section

open Bundle Topology
open scoped BigOperators

universe uK uB uE uP uI

namespace Bundle.FiniteRankAtlas

variable {K : Type uK} [RCLike K]
variable {B : Type uB} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)

attribute [local instance] TotalSpace.fiberAddCommMonoid TotalSpace.fiberModule

noncomputable section

/-- The number of charts selected before constructing the weighted embedding. -/
def embeddingChartCount : ℕ :=
  Classical.choose A.exists_finite_continuous_dual_weights

/-- The selected finite family of original chart indices. -/
def embeddingChartIndex : Fin A.embeddingChartCount → A.Index :=
  Classical.choose (Classical.choose_spec A.exists_finite_continuous_dual_weights)

/-- Subordinate nonnegative real weights on the selected finite chart family. -/
def embeddingRealWeight : Fin A.embeddingChartCount → B → ℝ :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec A.exists_finite_continuous_dual_weights))

/-- The scalar weights are the casts of the selected real weights. -/
def embeddingWeight (i : Fin A.embeddingChartCount) (b : B) : K :=
  (A.embeddingRealWeight i b : K)

/-- Reconstruction coefficients are formed in the scalar field, using its scalar
dual-coefficient construction rather than casting real dual coefficients. -/
def embeddingDualWeight : Fin A.embeddingChartCount → B → K :=
  FiniteScalarWeights.dualCoeff Finset.univ A.embeddingWeight

/-- Scalar weights are exactly the casts of the real weights. -/
@[simp] theorem embeddingWeight_apply (i : Fin A.embeddingChartCount) (b : B) :
    A.embeddingWeight i b = (A.embeddingRealWeight i b : K) := rfl

/-- The reconstruction coefficients are exactly the scalar dual coefficients. -/
theorem embeddingDualWeight_apply (i : Fin A.embeddingChartCount) (b : B) :
    A.embeddingDualWeight i b =
      FiniteScalarWeights.dualCoeff Finset.univ A.embeddingWeight i b := rfl

/-- The selected chart family and weights satisfy the finite subordinate-weight
contract, including the scalar support identities and reconstruction normalization. -/
theorem embedding_weights :
    Function.Injective A.embeddingChartIndex ∧
    (∀ b : B, ∃ i : Fin A.embeddingChartCount,
      b ∈ (A.chart (A.embeddingChartIndex i)).baseSet) ∧
    (∀ i, Continuous (A.embeddingRealWeight i)) ∧
    (∀ i b, 0 ≤ A.embeddingRealWeight i b) ∧
    (∀ b, ∑ i, A.embeddingRealWeight i b = 1) ∧
    (∀ i, tsupport (A.embeddingRealWeight i) ⊆
      (A.chart (A.embeddingChartIndex i)).baseSet) ∧
    (∀ b, ∃ i ∈ Finset.univ, A.embeddingWeight i b ≠ 0) ∧
    (∀ i, Continuous (A.embeddingWeight i)) ∧
    (∀ i, tsupport (A.embeddingWeight i) = tsupport (A.embeddingRealWeight i)) ∧
    (∀ i, tsupport (A.embeddingWeight i) ⊆
      (A.chart (A.embeddingChartIndex i)).baseSet) ∧
    (∀ i, Continuous (A.embeddingDualWeight i)) ∧
    (∀ i, tsupport (A.embeddingDualWeight i) = tsupport (A.embeddingWeight i)) ∧
    (∀ i, tsupport (A.embeddingDualWeight i) ⊆
      (A.chart (A.embeddingChartIndex i)).baseSet) ∧
    (∀ b, ∑ i, A.embeddingDualWeight i b * A.embeddingWeight i b = 1) :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec A.exists_finite_continuous_dual_weights))

/-- The full dependent product of the selected finite chart models, with its standard
function-space algebraic and topological structures. No factor is discarded. -/
abbrev WeightedEmbeddingModel : Type uK :=
  ∀ i : Fin A.embeddingChartCount, Fin (A.rank (A.embeddingChartIndex i)) → K

local notation "U" =>
  (fun i : Fin A.embeddingChartCount =>
    Bundle.Trivialization.baseSet (A.chart (A.embeddingChartIndex i)))
local notation "c" =>
  (fun (i : Fin A.embeddingChartCount) (b : B) (hb : b ∈ U i) =>
    LinearEquiv.symm (A.coordFiberLinearEquiv (A.embeddingChartIndex i) hb))

/-- Weighted coordinates on the original fibre, composed with the canonical linear
identification of that fibre with its equality subtype in the original total space. -/
def weightedEmbeddingLinearMap (b : B) : E b →ₗ[K] A.WeightedEmbeddingModel :=
  (LinearMap.weightedCoordinates U A.embeddingWeight c b).comp
    (TotalSpace.fiberLinearEquivAt (E := E) K P b).toLinearMap

/-- The fibre linear map uses the exact supported weighted-coordinate map. -/
theorem weightedEmbeddingLinearMap_apply (b : B) (v : E b) :
    A.weightedEmbeddingLinearMap b v =
      LinearMap.weightedCoordinates U A.embeddingWeight c b ⟨TotalSpace.mk b v, rfl⟩ := rfl

/-- The weighted total-space embedding into the full product of the selected models. -/
def weightedEmbedding : TotalSpace P E → B × A.WeightedEmbeddingModel :=
  fun t => (t.proj,
    LinearMap.weightedCoordinates U A.embeddingWeight c t.proj ⟨t, rfl⟩)

/-- The weighted stage is exactly the existing supported weighted-coordinate map on
original equality fibres, paired with the original projection. -/
theorem weightedEmbedding_apply (t : TotalSpace P E) :
    A.weightedEmbedding t = (t.proj,
      LinearMap.weightedCoordinates U A.embeddingWeight c t.proj ⟨t, rfl⟩) := rfl

/-- On an original fibre vector, the weighted stage is the fibre linear map paired
with the original base point. -/
@[simp] theorem weightedEmbedding_mk (b : B) (v : E b) :
    A.weightedEmbedding (TotalSpace.mk b v) = (b, A.weightedEmbeddingLinearMap b v) := rfl

private theorem continuous_embedding_chart_inverse (i : Fin A.embeddingChartCount) :
    Continuous (fun z : U i × (Fin (A.rank (A.embeddingChartIndex i)) → K) =>
      (c i z.1.val z.1.property z.2).val) :=
  A.continuous_coordFiberLinearEquiv_symm (A.embeddingChartIndex i)

private theorem continuous_embedding_chart_coordinate (i : Fin A.embeddingChartCount) :
    Continuous (fun t : {t : TotalSpace P E // t.proj ∈ U i} =>
      (c i t.val.proj t.property).symm ⟨t.val, rfl⟩) := by
  simpa only [LinearEquiv.symm_symm] using
    A.continuous_coordFiberLinearEquiv (A.embeddingChartIndex i)

/-- The exact weighted stage is continuous for the given original total-space topology. -/
theorem continuous_weightedEmbedding : Continuous A.weightedEmbedding := by
  obtain ⟨_, _, _, _, _, _, _, hw, _, hsuppw, _, _, _, _⟩ := A.embedding_weights
  exact A.continuous_proj.prodMk
    (LinearMap.continuous_weightedCoordinates
      (TotalSpace.proj : TotalSpace P E → B) U A.embeddingWeight c
      A.continuous_proj hw A.continuous_embedding_chart_coordinate hsuppw)

/-- The exact weighted stage is a closed embedding. Closedness uses the Hausdorff
model product and does not require the base or original total space to be Hausdorff. -/
theorem isClosedEmbedding_weightedEmbedding : IsClosedEmbedding A.weightedEmbedding := by
  classical
  obtain ⟨_, hcover, _, _, _, _, _, _, _, _, ha, _, hsuppa, hsum⟩ := A.embedding_weights
  have hU (b : B) : ∃ i : Fin A.embeddingChartCount, b ∈ interior (U i) := by
    obtain ⟨i, hi⟩ := hcover b
    refine ⟨i, ?_⟩
    rwa [(A.chart (A.embeddingChartIndex i)).open_baseSet.interior_eq]
  let ρ (b : B) : A.WeightedEmbeddingModel →ₗ[K]
      {t : TotalSpace P E // t.proj = b} :=
    LinearMap.finiteChartReconstruction U c b
      (Finset.univ.filter (fun i => b ∈ U i)) (fun i => A.embeddingDualWeight i b)
      (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hρ : Continuous (fun z : B × A.WeightedEmbeddingModel => (ρ z.1 z.2).val) :=
    LinearMap.continuous_finiteChartReconstruction U c Finset.univ
      A.embeddingDualWeight hU A.continuous_embedding_chart_inverse
      A.continuous_embedding_chart_coordinate (fun i _ => ha i) (fun i _ => hsuppa i)
  have hleft (b : B) :
      (ρ b).comp (LinearMap.weightedCoordinates U A.embeddingWeight c b) = LinearMap.id := by
    apply LinearMap.finiteChartReconstruction_filter_comp_weightedCoordinates_of_sum_eq_one
      U A.embeddingWeight c b Finset.univ (fun i => A.embeddingDualWeight i b)
    · intro i _ hbi
      by_contra hai
      exact hbi (hsuppa i (subset_closure hai))
    · exact hsum b
  exact LinearMap.isClosedEmbedding_weightedCoordinates_of_finiteChartReconstruction
    U c Finset.univ A.embeddingDualWeight A.embeddingWeight hρ
    A.continuous_weightedEmbedding hleft

/-- The dimension of the full product of selected models. -/
def embeddingDimension : ℕ := Module.finrank K A.WeightedEmbeddingModel

/-- The target dimension is the finrank of the full weighted model product. -/
theorem embeddingDimension_eq :
    A.embeddingDimension = Module.finrank K A.WeightedEmbeddingModel := rfl

/-- Standard coordinates on the full weighted model product, supplied by its chosen
finite basis. The finite Pi structures provide all finite-dimensionality hypotheses. -/
def embeddingModelEquiv :
    A.WeightedEmbeddingModel ≃L[K] (Fin A.embeddingDimension → K) :=
  (Module.finBasis K A.WeightedEmbeddingModel).equivFunL

/-- The standard-coordinate equivalence is exactly the finite-basis equivalence. -/
theorem embeddingModelEquiv_apply (z : A.WeightedEmbeddingModel) :
    A.embeddingModelEquiv z = (Module.finBasis K A.WeightedEmbeddingModel).equivFunL z := rfl

/-- The original fibre's linear map into the standard finite-dimensional model. -/
def finiteTrivialEmbeddingLinearMap (b : B) : E b →ₗ[K] (Fin A.embeddingDimension → K) :=
  A.embeddingModelEquiv.toLinearMap.comp (A.weightedEmbeddingLinearMap b)

/-- The standard fibre linear map is the chosen continuous linear equivalence applied
to the exact weighted fibre linear map. -/
theorem finiteTrivialEmbeddingLinearMap_apply (b : B) (v : E b) :
    A.finiteTrivialEmbeddingLinearMap b v =
      A.embeddingModelEquiv (A.weightedEmbeddingLinearMap b v) := rfl

/-- The fibrewise-linear embedding of the original total space into a standard finite
trivial bundle, obtained by changing only the target coordinates of the weighted stage. -/
def finiteTrivialEmbedding : TotalSpace P E → B × (Fin A.embeddingDimension → K) :=
  Prod.map id A.embeddingModelEquiv ∘ A.weightedEmbedding

/-- The standard stage is exactly the weighted stage followed by `id × e`, where
`e` is the finite-basis continuous linear equivalence of the full model product. -/
theorem finiteTrivialEmbedding_apply (t : TotalSpace P E) :
    A.finiteTrivialEmbedding t =
      ((A.weightedEmbedding t).1, A.embeddingModelEquiv (A.weightedEmbedding t).2) := rfl

/-- The standard stage preserves the base point and is given by its fibre linear map
on every original fibre vector. -/
@[simp] theorem finiteTrivialEmbedding_mk (b : B) (v : E b) :
    A.finiteTrivialEmbedding (TotalSpace.mk b v) =
      (b, A.finiteTrivialEmbeddingLinearMap b v) := rfl

/-- The standard finite-dimensional embedding is continuous on the original total space. -/
theorem continuous_finiteTrivialEmbedding : Continuous A.finiteTrivialEmbedding :=
  (continuous_fst.prodMk (A.embeddingModelEquiv.continuous.comp continuous_snd)).comp
    A.continuous_weightedEmbedding

/-- A finite-rank atlas over a compact normal base has a fibrewise-linear closed
embedding of its original total space into the standard finite trivial bundle. -/
theorem isClosedEmbedding_finiteTrivialEmbedding :
    IsClosedEmbedding A.finiteTrivialEmbedding := by
  let e : B × A.WeightedEmbeddingModel ≃ₜ B × (Fin A.embeddingDimension → K) :=
    (Homeomorph.refl B).prodCongr A.embeddingModelEquiv.toHomeomorph
  exact e.isClosedEmbedding.comp A.isClosedEmbedding_weightedEmbedding

include A in
/-- Existence of a continuous fibrewise-linear closed embedding into a standard finite
trivial bundle. The named construction also retains its exact weighted-coordinate stage. -/
theorem exists_finiteTrivialEmbedding :
    ∃ (N : ℕ) (L : ∀ b : B, E b →ₗ[K] (Fin N → K))
      (β : TotalSpace P E → B × (Fin N → K)),
      Continuous β ∧ IsClosedEmbedding β ∧
        ∀ (b : B) (v : E b), β (TotalSpace.mk b v) = (b, L b v) :=
  ⟨A.embeddingDimension, A.finiteTrivialEmbeddingLinearMap, A.finiteTrivialEmbedding,
    A.continuous_finiteTrivialEmbedding, A.isClosedEmbedding_finiteTrivialEmbedding,
    A.finiteTrivialEmbedding_mk⟩

end

end Bundle.FiniteRankAtlas
