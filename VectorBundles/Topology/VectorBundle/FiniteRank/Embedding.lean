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

Both stages have named, matching original-fibre retractions from the same selected
charts and scalar dual weights. Their total maps are jointly continuous for the given
original total-space topology, and their fibrewise composites with the embeddings
are the identity. These retractions are not asserted to be orthogonal or canonical
independently of the selected chart and weight data.

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

/-- The weighted stage preserves the original base point. -/
@[simp] theorem weightedEmbedding_fst (t : TotalSpace P E) :
    (A.weightedEmbedding t).1 = t.proj := rfl

local notation "D" =>
  (fun b : B =>
    LinearMap.finiteChartReconstruction U c b
      (Finset.univ.filter (fun i => b ∈ U i)) (fun i => A.embeddingDualWeight i b)
      (fun i hi => And.right (Finset.mem_filter.mp hi : i ∈ Finset.univ ∧ b ∈ U i)))

open Classical in
/-- The finite chart reconstruction, unpacked into the original fibre. It uses the
same selected charts and scalar dual weights as `weightedEmbeddingLinearMap`. -/
def weightedRetractionLinearMap (b : B) : A.WeightedEmbeddingModel →ₗ[K] E b :=
  (TotalSpace.fiberLinearEquivAt (E := E) K P b).symm.toLinearMap.comp
    (D b)

open Classical in
/-- The original-fibre retraction is exactly the existing filtered chart reconstruction
followed by the canonical unpacking of the projection equality fibre. -/
theorem weightedRetractionLinearMap_apply (b : B) (z : A.WeightedEmbeddingModel) :
    A.weightedRetractionLinearMap b z =
      (TotalSpace.fiberLinearEquivAt (E := E) K P b).symm
        (LinearMap.finiteChartReconstruction U c b
          (Finset.univ.filter (fun i => b ∈ U i)) (fun i => A.embeddingDualWeight i b)
          (fun _ hi => (Finset.mem_filter.mp hi).2) z) := rfl

/-- The weighted-model retraction takes values in the original total space. -/
def weightedRetraction : B × A.WeightedEmbeddingModel → TotalSpace P E :=
  fun z => TotalSpace.mk z.1 (A.weightedRetractionLinearMap z.1 z.2)

/-- Evaluation of the total retraction uses its original-fibre linear map. -/
theorem weightedRetraction_apply (z : B × A.WeightedEmbeddingModel) :
    A.weightedRetraction z =
      TotalSpace.mk z.1 (A.weightedRetractionLinearMap z.1 z.2) := rfl

/-- Reconstruction preserves the specified base point. -/
@[simp] theorem weightedRetraction_proj (z : B × A.WeightedEmbeddingModel) :
    (A.weightedRetraction z).proj = z.1 := rfl

open Classical in
/-- Unpacking and rebuilding the equality-fibre reconstruction preserves its exact
original total-space value. -/
theorem weightedRetraction_eq_finiteChartReconstruction
    (z : B × A.WeightedEmbeddingModel) :
    A.weightedRetraction z =
      (LinearMap.finiteChartReconstruction U c z.1
        (Finset.univ.filter (fun i => z.1 ∈ U i)) (fun i => A.embeddingDualWeight i z.1)
        (fun _ hi => (Finset.mem_filter.mp hi).2) z.2).val := by
  rw [weightedRetraction_apply, weightedRetractionLinearMap_apply,
    TotalSpace.fiberLinearEquivAt_symm_apply, TotalSpace.mk_fiberEquiv_symm]

/-- Scalar dual weights make reconstruction a linear left inverse on each original fibre. -/
theorem weightedRetractionLinearMap_comp_weightedEmbeddingLinearMap (b : B) :
    (A.weightedRetractionLinearMap b).comp (A.weightedEmbeddingLinearMap b) =
      LinearMap.id := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsuppa, hsum⟩ := A.embedding_weights
  have hleft : (D b).comp
      (LinearMap.weightedCoordinates U A.embeddingWeight c b) = LinearMap.id := by
    apply LinearMap.finiteChartReconstruction_filter_comp_weightedCoordinates_of_sum_eq_one
      U A.embeddingWeight c b Finset.univ (fun i => A.embeddingDualWeight i b)
    · intro i _ hbi
      by_contra hai
      exact hbi (hsuppa i (subset_closure hai))
    · exact hsum b
  apply LinearMap.ext
  intro v
  have hv := congrArg
    (fun f : {t : TotalSpace P E // t.proj = b} →ₗ[K]
        {t : TotalSpace P E // t.proj = b} =>
      (TotalSpace.fiberLinearEquivAt (E := E) K P b).symm
        (f (TotalSpace.fiberLinearEquivAt (E := E) K P b v))) hleft
  simpa only [LinearMap.comp_apply, weightedRetractionLinearMap_apply,
    weightedEmbeddingLinearMap_apply,
    ← TotalSpace.fiberLinearEquivAt_apply (E := E) K P b,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply] using hv

/-- Reconstructing the weighted coordinates returns the original total-space point. -/
@[simp] theorem weightedRetraction_weightedEmbedding (t : TotalSpace P E) :
    A.weightedRetraction (A.weightedEmbedding t) = t := by
  rcases t with ⟨b, v⟩
  rw [weightedEmbedding_mk, weightedRetraction_apply]
  exact congrArg (TotalSpace.mk b)
    (congrArg (fun f : E b →ₗ[K] E b => f v)
      (A.weightedRetractionLinearMap_comp_weightedEmbeddingLinearMap b))

/-- The total reconstruction is a left inverse of the weighted total embedding. -/
theorem leftInverse_weightedRetraction_weightedEmbedding :
    Function.LeftInverse A.weightedRetraction A.weightedEmbedding :=
  A.weightedRetraction_weightedEmbedding

/-- Reconstruction composed with the weighted total embedding is the identity. -/
@[simp] theorem weightedRetraction_comp_weightedEmbedding :
    A.weightedRetraction ∘ A.weightedEmbedding = id :=
  funext A.weightedRetraction_weightedEmbedding

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

/-- The weighted reconstruction is jointly continuous into the original total space. -/
theorem continuous_weightedRetraction : Continuous A.weightedRetraction := by
  classical
  obtain ⟨_, hcover, _, _, _, _, _, _, _, _, ha, _, hsuppa, _⟩ := A.embedding_weights
  have hU (b : B) : ∃ i : Fin A.embeddingChartCount, b ∈ interior (U i) := by
    obtain ⟨i, hi⟩ := hcover b
    refine ⟨i, ?_⟩
    rwa [(A.chart (A.embeddingChartIndex i)).open_baseSet.interior_eq]
  have hρ : Continuous (fun z : B × A.WeightedEmbeddingModel =>
      (D z.1 z.2).val) :=
    LinearMap.continuous_finiteChartReconstruction U c Finset.univ
      A.embeddingDualWeight hU A.continuous_embedding_chart_inverse
      A.continuous_embedding_chart_coordinate (fun i _ => ha i) (fun i _ => hsuppa i)
  apply hρ.congr
  intro z
  exact (A.weightedRetraction_eq_finiteChartReconstruction z).symm

/-- Each reconstruction linear map is continuous for the given original fibre topology. -/
theorem continuous_weightedRetractionLinearMap (b : B) :
    Continuous (A.weightedRetractionLinearMap b) := by
  apply (A.inducing b).continuous_iff.mpr
  change Continuous (fun z : A.WeightedEmbeddingModel => A.weightedRetraction (b, z))
  exact A.continuous_weightedRetraction.comp (continuous_const.prodMk continuous_id)

/-- The exact weighted stage is a closed embedding. Closedness uses the Hausdorff
model product and does not require the base or original total space to be Hausdorff. -/
theorem isClosedEmbedding_weightedEmbedding : IsClosedEmbedding A.weightedEmbedding := by
  classical
  have hρ : Continuous (fun z : B × A.WeightedEmbeddingModel =>
      (D z.1 z.2).val) := by
    apply A.continuous_weightedRetraction.congr
    intro z
    exact A.weightedRetraction_eq_finiteChartReconstruction z
  have hleft (b : B) : (D b).comp
      (LinearMap.weightedCoordinates U A.embeddingWeight c b) = LinearMap.id := by
    apply LinearMap.ext
    intro u
    have hu := congrArg
      (fun f : E b →ₗ[K] E b =>
        TotalSpace.fiberLinearEquivAt (E := E) K P b
          (f ((TotalSpace.fiberLinearEquivAt (E := E) K P b).symm u)))
      (A.weightedRetractionLinearMap_comp_weightedEmbeddingLinearMap b)
    simpa only [LinearMap.comp_apply, weightedRetractionLinearMap_apply,
      weightedEmbeddingLinearMap_apply,
      ← TotalSpace.fiberLinearEquivAt_apply (E := E) K P b,
      LinearMap.id_apply, LinearEquiv.apply_symm_apply] using hu
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

/-- The standard-coordinate stage preserves the original base point. -/
@[simp] theorem finiteTrivialEmbedding_fst (t : TotalSpace P E) :
    (A.finiteTrivialEmbedding t).1 = t.proj := rfl

/-- Reconstruction from standard finite coordinates into the original fibre, using
exactly the inverse of the model equivalence in `finiteTrivialEmbeddingLinearMap`. -/
def finiteTrivialRetractionLinearMap (b : B) :
    (Fin A.embeddingDimension → K) →ₗ[K] E b :=
  (A.weightedRetractionLinearMap b).comp A.embeddingModelEquiv.symm.toLinearMap

/-- Standard-coordinate reconstruction first returns to the full selected model product. -/
theorem finiteTrivialRetractionLinearMap_apply (b : B) (z : Fin A.embeddingDimension → K) :
    A.finiteTrivialRetractionLinearMap b z =
      A.weightedRetractionLinearMap b (A.embeddingModelEquiv.symm z) := rfl

/-- The finite-trivial retraction takes values in the original total space. -/
def finiteTrivialRetraction : B × (Fin A.embeddingDimension → K) → TotalSpace P E :=
  fun z => TotalSpace.mk z.1 (A.finiteTrivialRetractionLinearMap z.1 z.2)

/-- Evaluation of the standard-coordinate retraction uses its original-fibre linear map. -/
theorem finiteTrivialRetraction_apply (z : B × (Fin A.embeddingDimension → K)) :
    A.finiteTrivialRetraction z =
      TotalSpace.mk z.1 (A.finiteTrivialRetractionLinearMap z.1 z.2) := rfl

/-- Standard-coordinate reconstruction preserves the specified base point. -/
@[simp] theorem finiteTrivialRetraction_proj (z : B × (Fin A.embeddingDimension → K)) :
    (A.finiteTrivialRetraction z).proj = z.1 := rfl

/-- The standard-coordinate retraction changes only the model coordinates of the
weighted retraction, using the inverse of the same equivalence as the embedding. -/
theorem finiteTrivialRetraction_eq_weightedRetraction
    (z : B × (Fin A.embeddingDimension → K)) :
    A.finiteTrivialRetraction z =
      A.weightedRetraction (z.1, A.embeddingModelEquiv.symm z.2) := rfl

/-- Standard-coordinate reconstruction is a linear left inverse on each original fibre. -/
theorem finiteTrivialRetractionLinearMap_comp_finiteTrivialEmbeddingLinearMap (b : B) :
    (A.finiteTrivialRetractionLinearMap b).comp (A.finiteTrivialEmbeddingLinearMap b) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change A.weightedRetractionLinearMap b
    (A.embeddingModelEquiv.symm
      (A.embeddingModelEquiv (A.weightedEmbeddingLinearMap b v))) = v
  rw [A.embeddingModelEquiv.symm_apply_apply]
  exact congrArg (fun f : E b →ₗ[K] E b => f v)
    (A.weightedRetractionLinearMap_comp_weightedEmbeddingLinearMap b)

/-- Reconstructing the finite-trivial embedding returns the original total-space point. -/
@[simp] theorem finiteTrivialRetraction_finiteTrivialEmbedding (t : TotalSpace P E) :
    A.finiteTrivialRetraction (A.finiteTrivialEmbedding t) = t := by
  rcases t with ⟨b, v⟩
  rw [finiteTrivialEmbedding_mk, finiteTrivialRetraction_apply]
  exact congrArg (TotalSpace.mk b)
    (congrArg (fun f : E b →ₗ[K] E b => f v)
      (A.finiteTrivialRetractionLinearMap_comp_finiteTrivialEmbeddingLinearMap b))

/-- The finite-trivial total retraction is a left inverse of the named total embedding. -/
theorem leftInverse_finiteTrivialRetraction_finiteTrivialEmbedding :
    Function.LeftInverse A.finiteTrivialRetraction A.finiteTrivialEmbedding :=
  A.finiteTrivialRetraction_finiteTrivialEmbedding

/-- The finite-trivial total retraction composed with the embedding is the identity. -/
@[simp] theorem finiteTrivialRetraction_comp_finiteTrivialEmbedding :
    A.finiteTrivialRetraction ∘ A.finiteTrivialEmbedding = id :=
  funext A.finiteTrivialRetraction_finiteTrivialEmbedding

/-- The finite-trivial reconstruction is jointly continuous into the original total space. -/
theorem continuous_finiteTrivialRetraction : Continuous A.finiteTrivialRetraction := by
  have h := A.continuous_weightedRetraction.comp
    (continuous_fst.prodMk (A.embeddingModelEquiv.symm.continuous.comp continuous_snd))
  apply h.congr
  intro z
  exact (A.finiteTrivialRetraction_eq_weightedRetraction z).symm

/-- Standard-coordinate reconstruction is continuous for each original fibre topology. -/
theorem continuous_finiteTrivialRetractionLinearMap (b : B) :
    Continuous (A.finiteTrivialRetractionLinearMap b) := by
  apply (A.inducing b).continuous_iff.mpr
  change Continuous (fun z : Fin A.embeddingDimension → K =>
    A.finiteTrivialRetraction (b, z))
  exact A.continuous_finiteTrivialRetraction.comp (continuous_const.prodMk continuous_id)

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

include A in
/-- A compact normal finite-rank atlas admits a matched finite-trivial embedding and
original-fibre retraction. Both total maps are continuous, the embedding is closed,
and reconstruction is a linear left inverse in every original fibre. -/
theorem exists_finiteTrivialEmbedding_and_retraction :
    ∃ (N : ℕ)
      (β : ∀ b : B, E b →ₗ[K] (Fin N → K))
      (ρ : ∀ b : B, (Fin N → K) →ₗ[K] E b),
      Continuous (fun t : TotalSpace P E => (t.proj, β t.proj t.snd)) ∧
      IsClosedEmbedding (fun t : TotalSpace P E => (t.proj, β t.proj t.snd)) ∧
      Continuous (fun z : B × (Fin N → K) =>
        (TotalSpace.mk z.1 (ρ z.1 z.2) : TotalSpace P E)) ∧
      ∀ b : B, (ρ b).comp (β b) = LinearMap.id := by
  have hβ : (fun t : TotalSpace P E =>
      (t.proj, A.finiteTrivialEmbeddingLinearMap t.proj t.snd)) =
      A.finiteTrivialEmbedding := by
    funext t
    rcases t with ⟨b, v⟩
    exact (A.finiteTrivialEmbedding_mk b v).symm
  refine ⟨A.embeddingDimension, A.finiteTrivialEmbeddingLinearMap,
    A.finiteTrivialRetractionLinearMap, ?_, ?_, A.continuous_finiteTrivialRetraction,
    A.finiteTrivialRetractionLinearMap_comp_finiteTrivialEmbeddingLinearMap⟩
  · rw [hβ]
    exact A.continuous_finiteTrivialEmbedding
  · rw [hβ]
    exact A.isClosedEmbedding_finiteTrivialEmbedding

end

end Bundle.FiniteRankAtlas
