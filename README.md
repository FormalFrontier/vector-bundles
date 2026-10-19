# Vector bundles

Foundational geometry of topological vector bundles: compatible real and complex
fiber metrics and their pullbacks, orthogonal splitting and comparison for supplied
metrics, and homeomorphisms induced by fiberwise linear equivalences, together with
products, pullbacks, cylinder charts, frames, finite embeddings, ranges and
complementary bundles. The library extends Mathlib's bundle structures and uses
their original fiber and total-space topologies. It also gives projection criteria,
canonical projection homeomorphisms, properness criteria and compactness transfer for
topological fiber bundles.

## Headline results

- **Projection criteria and canonical homeomorphisms.**
  [`FiberBundle.isOpenEmbedding_proj_iff`](VectorBundles/Topology/FiberBundle/Projection.lean)
  characterizes open-embedding projections by every original fiber being subsingleton.
  `FiberBundle.homeomorphProj` constructs the canonical projection homeomorphism when
  every fiber is also nonempty, with forward, inverse/base, dependent-pair and given-zero-section
  formulas. These results need no scalar, norm, separation or nonempty-base hypothesis;
  the model assumptions are only sufficient corollaries.
- **Proper fiber-bundle projections.**
  [`FiberBundle.isProperMap_proj_iff`](VectorBundles/Topology/FiberBundle/Proper.lean)
  characterizes proper projections by compactness of every fiber with its given
  topology. `FiberBundle.isProperMap_proj` gives the compact-model sufficient
  criterion. Properness is Mathlib's `IsProperMap` (continuity and universal
  closedness). No separation, local compactness or nonempty-base assumption is
  required; an empty base does not require a compact model.
- **Proper canonical pullback lifts.**
  [`Bundle.Pullback.isProperMap_lift`](VectorBundles/Topology/FiberBundle/Pullback/Proper.lean)
  gives a proper lift from a proper base map and continuity of the original bundle
  projection. It retains the canonical pullback and original total-space topologies,
  with independent universes and no fiber topology, local triviality or separation
  assumptions. The [two direct examples](VectorBundlesTest/Topology/FiberBundle/Pullback/Proper.lean)
  exhibit the proper noninjective base map `ℝ × Fin 2 → ℝ`, continuity of the original
  trivial-bundle projection and a noninjective proper lift, together with an
  empty-original-fiber boundary.
- **Compactness of fiber bundles without separation assumptions.**
  [`FiberBundle.compactSpace_totalSpace`](VectorBundles/Topology/FiberBundle/Proper.lean)
  gives compact total space from a compact base and compact model, including empty spaces.
  `FiberBundle.compactSpace_model` recovers compactness of the model from compactness
  of the total space and a specified base point, even when the model is empty.
  `FiberBundle.compactSpace_totalSpace_iff` characterizes compact total space by compact
  base and compact model when both base and model are nonempty. These results use only
  the original topologies and fiber-bundle structure, with no separation assumptions.
  Empty-model and empty-base examples show why the respective nonemptiness hypotheses
  in the equivalence are necessary.
- **Local compactness of fiber bundles without separation assumptions.**
  [`FiberBundle.locallyCompactSpace_model`](VectorBundles/Topology/FiberBundle/LocallyCompact.lean)
  recovers local compactness of the model from a locally compact total space and a
  specified base point, even when the model is empty.
  `FiberBundle.locallyCompactSpace_totalSpace_iff` characterizes local compactness of
  the total space by local compactness of the base and model when both are nonempty.
  The construction from locally compact base and model is Mathlib's existing
  `ChartedSpace.locallyCompactSpace`. All results retain the original topologies and
  fiber-bundle structure, with no separation assumptions.
- **Preconnected preimages under open maps.**
  [`IsPreconnected.preimage_of_isOpenMap_of_isPreconnected_fibers`](VectorBundles/Topology/Connected/Basic.lean)
  gives preconnected `f ⁻¹' s` when `f` is open, `s` is preconnected and contained
  in `Set.range f`, and `f ⁻¹' {y}` is preconnected for every `y ∈ s`.
  No continuity, global surjectivity or separation assumptions are required.
- **Connectedness of fiber bundles.**
  [`FiberBundle.isPreconnected_preimage_proj`](VectorBundles/Topology/FiberBundle/Connected.lean)
  gives preconnected projection preimages of preconnected base subsets when the
  model is preconnected. `FiberBundle.preconnectedSpace_totalSpace` and
  `FiberBundle.connectedSpace_totalSpace` give the corresponding total-space
  conclusions from preconnected, respectively connected, base and model.
  These use the given base, model, fiber and total-space topologies and fiber-bundle
  structure, with independent base, model and fiber universes and no separation assumptions.
  Preconnectedness allows empty models; `ConnectedSpace` includes nonemptiness.
  Connected total space need not imply a connected model.
- **Compatible fiber metrics.**
  [`VectorBundle.continuousHermitianMetric`](VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  constructs a continuous positive-definite Hermitian metric on a finite-dimensional
  vector bundle over a paracompact Hausdorff base, over an `RCLike` field.
  The normed model need not have an inner-product norm; the resulting metric induces
  the existing fiber topologies. The
  [real specialization](VectorBundles/Topology/VectorBundle/Metric.lean)
  returns Mathlib's continuous Riemannian metric data.
- **Positive operations on supplied metrics.**
  [`Bundle.HermitianMetric.add`](VectorBundles/Topology/VectorBundle/HermitianMetric/Operations.lean)
  adds metrics on the same family, and `rescale` multiplies by a pointwise-positive
  real function, without base topology assumptions. Their continuous counterparts use
  the same given bundle structures and continuous real weights, with no finite-dimensionality
  or uniform lower bound. The [stock-plane use](VectorBundlesTest/Topology/VectorBundle/HermitianMetric/Operations.lean)
  combines both operations over the real line for real and complex supremum-norm planes.
- **Pullback of supplied metrics.**
  [`Bundle.HermitianMetric.pullback`](VectorBundles/Topology/VectorBundle/MetricPullback.lean)
  reindexes a metric along any base map, without base topologies or bundle data.
  `Bundle.ContinuousHermitianMetric.pullback` handles `ContinuousMapClass` maps
  using Mathlib's pullback bundle structures, with the same normed model and original
  fiber structures. No finite dimension is required. Pairing formulas and pointwise
  identity/composition laws are provided; equality of continuous structures across
  different Hom-bundle topologies is not asserted.
- **Orthogonal subbundles and splitting for a supplied metric.**
  [`Bundle.ContinuousHermitianMetric.orthogonalBundle`](VectorBundles/Topology/VectorBundle/OrthogonalComplement.lean)
  constructs bundle data on the orthogonal family of an intrinsic submodule bundle
  whose total-space inclusion is an embedding. The ambient model is
  finite-dimensional over an `RCLike` field. The base is an arbitrary topological
  space: neither separation nor paracompactness is required. The complement retains
  its fiber subtype topologies and ambient-induced total topology.
  [Orthogonal addition](VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean)
  is a homeomorphism from the fiberwise product onto the ambient total space, and
  [continuous projections](VectorBundles/Topology/VectorBundle/OrthogonalProjection.lean)
  recover its two summands. The same module's
  `continuous_orthogonalProjectionOntoL`, `continuous_orthogonalProjectionL` and
  `continuous_orthogonalComplementProjectionL` assert continuity of Mathlib's
  existing continuous-linear projections as sections of the intrinsic-target and
  ambient-target Hom bundles. Both ambient fields have the same Hom topology;
  all fields retain the original model norms and bundle structures. No global
  finiteness assumption on the subbundle model or nonemptiness assumption on the
  base is needed.
- **Canonical comparison of orthogonal complements.**
  [`Bundle.ContinuousHermitianMetric.orthogonalComplementHomeomorph`](VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean)
  compares the complements of the same embedded intrinsic submodule bundle for two
  supplied continuous metrics. Only the ambient model is assumed finite-dimensional,
  over an `RCLike` field. The complement total spaces retain their ambient-induced
  topologies, with the second metric's projection as the forward map and the first
  metric's projection as its inverse. Fiberwise quotient formulas, base preservation,
  equal-metric identity and three-metric composition are provided. No global intrinsic
  finiteness or nonempty-base assumption is required.
- **Orthonormal local coordinates.**
  [`Bundle.ContinuousHermitianMetric.orthonormalizeTrivialization`](VectorBundles/Topology/VectorBundle/OrthonormalTrivialization.lean)
  changes any linear chart of a finite-dimensional `RCLike` bundle with a supplied
  continuous Hermitian metric to Euclidean coordinates on exactly the same base
  set, preserving the metric pairing. This does not install new norms or
  topologies, or assert an adapted subbundle frame or a parametric Gram–Schmidt
  algorithm.
- **Forward continuity implies inverse continuity.**
  [`VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology`](VectorBundles/Topology/VectorBundle/Isomorphism.lean)
  constructs a total-space homeomorphism from a family of algebraic fiberwise
  linear equivalences with continuous forward total map. The source normed model
  is finite-dimensional over a nontrivially normed field; the target normed model
  has `IsModuleTopology`. The complete-field constructor derives the required
  target properties at each base point. Empty bases and zero-rank bundles are
  allowed; the two models need not be globally identified.
- **Linear coordinates and operator continuity.**
  [Coordinate maps](VectorBundles/Topology/VectorBundle/CoordinateMap.lean)
  of a continuous fiberwise-linear total map have jointly continuous evaluations,
  including independent source and target bases and an arbitrary covered base map.
  For a finite-dimensional source model with its module topology, the same-base
  coordinate operators are continuous for bounded convergence.
  `VectorBundle.of_isLinear` equips an existing fiber bundle with a vector-bundle
  structure when its chosen atlas is linear and its finite-dimensional normed
  model has the module topology. The original atlas and topologies are retained.

- **Pullbacks, products and cylinder charts.**
  [Pullback total spaces](VectorBundles/Topology/FiberBundle/Pullback.lean)
  identify with compatible-pair subspaces and satisfy a universal mapping property,
  even for a base map that is not continuous. This is an underlying-space statement,
  not local triviality for a discontinuous map.
  [Fiberwise products](VectorBundles/Topology/FiberBundle/Prod.lean)
  have canonical swap and reassociation homeomorphisms for their existing topologies.
  A [vector bundle over `X × unitInterval`](VectorBundles/Topology/VectorBundle/Cylinder.lean)
  has, near each point of an arbitrary `X`, a linear chart valid for the whole
  interval, without completeness or dimension assumptions. This is not a
  homotopy-invariance theorem.
- **Finite complementary bundles.**
  [`VectorBundle.finiteComplement`](VectorBundles/Topology/VectorBundle/FiniteComplement.lean)
  constructs a finite-dimensional complement to a finite-dimensional vector bundle
  over an `RCLike` field on a compact normal base, together with a global linear
  trivialization of their fiberwise product. The complement retains its subspace
  fiber topologies and ambient-induced total topology. It is not asserted to be
  complementary or orthogonal to a prescribed ambient embedding.

## Using the library

With this package available to Lake, import the production root or a narrower module:

```lean
import VectorBundles
-- Alternatively:
-- import VectorBundles.Topology.VectorBundle.MetricExistence
```

For example, the following construction is also used in the
[Hermitian metric examples](VectorBundlesTest/Topology/VectorBundle/HermitianMetric.lean):

```lean
noncomputable example :
    Bundle.ContinuousHermitianMetric ℂ (ℂ × ℂ) (Bundle.Trivial ℝ (ℂ × ℂ)) :=
  VectorBundle.continuousHermitianMetric ℂ (ℂ × ℂ) (Bundle.Trivial ℝ (ℂ × ℂ))
```

The raw product model has its sup norm, which is not an inner-product norm.
`import VectorBundlesTest` also imports the standard and boundary examples.

## Building

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`; the sole direct dependency is
[Mathlib](https://github.com/leanprover-community/mathlib4) at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Its upstream dependencies are pinned
in `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes both `VectorBundles` and `VectorBundlesTest`.

## Contents

Paths below are relative to `VectorBundles/`. Full fiber- and vector-bundle
examples are collected by `VectorBundlesTest.lean`.

| Module | Contents |
| --- | --- |
| [`Analysis.InnerProductSpace.PositiveForm`](VectorBundles/Analysis/InnerProductSpace/PositiveForm.lean) | Bounded positive-form unit sublevels in the original topology |
| [`Analysis.Normed.Ring.Units`](VectorBundles/Analysis/Normed/Ring/Units.lean) | Value embedding for units of a seminormed ring |
| [`Topology.Algebra.Module.FiniteDimensionalOperator`](VectorBundles/Topology/Algebra/Module/FiniteDimensionalOperator.lean) | Pointwise versus bounded-convergence operator criteria |
| [`Topology.Connected.Basic`](VectorBundles/Topology/Connected/Basic.lean) | Preconnected preimages under open maps with preconnected fibers over a preconnected subset of the range |
| [`Topology.FiberBundle.Connected`](VectorBundles/Topology/FiberBundle/Connected.lean) | Preconnected projection preimages and preconnected/connected total spaces; [real and empty-model examples](VectorBundlesTest/Topology/FiberBundle/Connected.lean) |
| [`Topology.FiberBundle.Projection`](VectorBundles/Topology/FiberBundle/Projection.lean) | Sharp projection criteria, canonical homeomorphism and inverse/zero-section formulas |
| [`Topology.FiberBundle.Proper`](VectorBundles/Topology/FiberBundle/Proper.lean) | Proper projection exactly when every fiber is compact; compactness transfer and equivalence without separation |
| [`Topology.VectorBundle.CoordinateMap`](VectorBundles/Topology/VectorBundle/CoordinateMap.lean) | Linear-chart evaluations, operators and linear-atlas criterion |
| [`Topology.VectorBundle.FiniteSum`](VectorBundles/Topology/VectorBundle/FiniteSum.lean) | Locally finite sums of continuous sections |
| [`Topology.VectorBundle.SemilinearEvaluation`](VectorBundles/Topology/VectorBundle/SemilinearEvaluation.lean) | One- and two-argument evaluation on Mathlib's Hom topology |
| [`Topology.VectorBundle.WeightedForm`](VectorBundles/Topology/VectorBundle/WeightedForm.lean) | Supported weighted forms in linear charts |
| [`Topology.VectorBundle.HermitianMetric`](VectorBundles/Topology/VectorBundle/HermitianMetric.lean) | Hermitian metric data, continuity, Core conversion and real bridges |
| [`Topology.VectorBundle.HermitianMetric.Operations`](VectorBundles/Topology/VectorBundle/HermitianMetric/Operations.lean) | Addition and positive rescaling with pairing and forgetting equations |
| [`Topology.VectorBundle.Section`](VectorBundles/Topology/VectorBundle/Section.lean) | Continuous scalar multiplication of sections in the given bundle topology |
| [`Topology.Bornology.Bounded`](VectorBundles/Topology/Bornology/Bounded.lean) | Fixed scalar dilations of von Neumann bounded sets |
| [`Topology.VectorBundle.MetricModel`](VectorBundles/Topology/VectorBundle/MetricModel.lean) | Compatible forms on finite-dimensional normed models |
| [`Topology.VectorBundle.MetricExistence`](VectorBundles/Topology/VectorBundle/MetricExistence.lean) | Partition-of-unity construction of continuous Hermitian metrics |
| [`Topology.VectorBundle.Metric`](VectorBundles/Topology/VectorBundle/Metric.lean) | Real Riemannian specialization |
| [`Topology.VectorBundle.MetricPullback`](VectorBundles/Topology/VectorBundle/MetricPullback.lean) | Pointwise and continuous pullbacks of supplied Hermitian metrics |
| [`Topology.VectorBundle.Isomorphism`](VectorBundles/Topology/VectorBundle/Isomorphism.lean) | Fiberwise equivalences with only forward continuity supplied |
| [`Topology.VectorBundle.OrthogonalComplement`](VectorBundles/Topology/VectorBundle/OrthogonalComplement.lean) | Orthogonal subbundle with original subtype topologies |
| [`Topology.VectorBundle.OrthogonalComparison`](VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean) | Quotient-derived comparison of complements for two supplied metrics |
| [`Topology.VectorBundle.OrthogonalAddition`](VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean) | Prescribed addition homeomorphism |
| [`Topology.VectorBundle.OrthogonalProjection`](VectorBundles/Topology/VectorBundle/OrthogonalProjection.lean) | Continuous total-space projections, fiber formulas and Hom-section continuity of projector fields |
| [`Topology.VectorBundle.OrthonormalTrivialization`](VectorBundles/Topology/VectorBundle/OrthonormalTrivialization.lean) | Pairing-preserving Euclidean chart coordinates |
| [`Analysis.Normed.Operator.Factorization`](VectorBundles/Analysis/Normed/Operator/Factorization.lean) | Continuity of coefficients from factorization and a common positive lower bound |
| [`Analysis.Normed.Operator.LowerBound`](VectorBundles/Analysis/Normed/Operator/LowerBound.lean) | Persistence of positive lower bounds under operator perturbations |
| [`Data.Bundle`](VectorBundles/Data/Bundle.lean) | Maps of dependent total spaces and their identity and composition laws |
| [`Topology.FiberBundle.ClosedCylinder`](VectorBundles/Topology/FiberBundle/ClosedCylinder.lean) | Gluing two supplied charts across a closed cylinder cut |
| [`Topology.FiberBundle.Prod`](VectorBundles/Topology/FiberBundle/Prod.lean) | Symmetry, associativity and pullback comparison of fiberwise products |
| [`Topology.FiberBundle.Pullback`](VectorBundles/Topology/FiberBundle/Pullback.lean) | Compatible-pair total spaces and universal pullback maps |
| [`Topology.FiberBundle.Pullback.Proper`](VectorBundles/Topology/FiberBundle/Pullback/Proper.lean) | Proper canonical lifts from proper base maps and continuity of the original projection; [two direct examples](VectorBundlesTest/Topology/FiberBundle/Pullback/Proper.lean) for a noninjective two-sheeted base and empty original fibers |
| [`Topology.FiberBundle.SupportedTransport`](VectorBundles/Topology/FiberBundle/SupportedTransport.lean) | Pullback transport localized to one chart by a closed subset |
| [`Topology.MetricSpace.Antilipschitz`](VectorBundles/Topology/MetricSpace/Antilipschitz.lean) | Product embeddings from locally uniform antilipschitz bounds |
| [`Topology.VectorBundle.Cylinder`](VectorBundles/Topology/VectorBundle/Cylinder.lean) | Linear charts near a compact interval cylinder |
| [`Topology.VectorBundle.Embedding`](VectorBundles/Topology/VectorBundle/Embedding.lean) | Total-space embeddings from fiberwise injective linear maps |
| [`Topology.VectorBundle.FiniteComplement`](VectorBundles/Topology/VectorBundle/FiniteComplement.lean) | Finite-dimensional complementary bundles over compact normal bases |
| [`Topology.VectorBundle.FiniteEmbedding`](VectorBundles/Topology/VectorBundle/FiniteEmbedding.lean) | Embeddings into finite powers of the model over compact normal bases |
| [`Topology.VectorBundle.Frame`](VectorBundles/Topology/VectorBundle/Frame.lean) | Global linear trivializations and coefficient criteria from continuous fiberwise bases |
| [`Topology.VectorBundle.KernelProjection`](VectorBundles/Topology/VectorBundle/KernelProjection.lean) | Local continuous kernel projections with a common complement |
| [`Topology.VectorBundle.Range`](VectorBundles/Topology/VectorBundle/Range.lean) | Range bundles with original subtype and induced total topologies |
| [`Topology.VectorBundle.TrivialMetric`](VectorBundles/Topology/VectorBundle/TrivialMetric.lean) | Constant metrics from supplied compatible Hermitian model forms |
| [`VectorBundlesTest`](VectorBundlesTest.lean) | Full examples: projection and properness boundaries, connectedness, isomorphisms, metrics, semilinear evaluation, Hermitian metrics, metric pullbacks, shear-metric complement comparison, orthogonal complement/addition/projection, orthonormal charts, products, pullbacks, cylinder charts, frames, embeddings, ranges and finite complements |

## Conventions and limitations

Hermitian forms are conjugate-linear in the first argument and linear in the second.
Metric compatibility concerns topology, not preservation of an unrelated existing
norm. The metric and linear-geometric results put norms only on model fibers; the bundle
fibers retain their existing algebraic and topological structures. The projection
criteria require only topological fiber-bundle data. The real metric bridges use Mathlib's
Riemannian data rather than introducing a second real metric class.

Metric existence and supplied-metric splitting have different hypotheses. The
latter is not a metric-existence assertion. The finite complement construction
asserts neither classification nor complementarity to a prescribed embedding. No general
homotopy-invariance, constant-rank kernel-bundle, tensor-product or
projective-section theorem is provided here. The units embedding does not assert
that the unit locus is open or that partial inversion on the ambient ring is continuous. The finite-operator
criterion requires the source's module topology, which cannot simply be dropped
over an incomplete field.

## References

- Allen Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html),
  version 2.2 (November 2017), §1.1: Lemma 1.1, Proposition 1.2 and its Hermitian
  remark, the supplied-metric geometric ingredients of Proposition 1.3,
  finite complements in Proposition 1.4, pullbacks in Proposition 1.5, and
  the two preliminary cylinder facts used in Proposition 1.7.
- Mathlib's [bundle geometry](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/VectorBundle),
  module topology, bounded-convergence operator topology, inner products,
  orthogonal complements, partitions of unity and continuous functional calculus.
  Individual modules identify the particular APIs and contributors followed.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed to the formalization and
its documentation. The mathematics draws on Hatcher's constructions and on
Mathlib; no book text, figures or source assets are distributed. The Hermitian
metric implementation follows Sébastien Gouëzel's Riemannian metrics, and the
semilinear evaluation proofs follow work by Heather Macbeth, Floris van Doorn,
Sébastien Gouëzel, Sophie Morel and Yury Kudryashov. Their authentic notices and
the additional contributor credits in the module documentation are preserved.
Pullback bundle constructions follow Nicolò Cavalleri, Sébastien Gouëzel, Heather
Macbeth and Floris van Doorn; quotient-complement equivalences and projections
follow Yury Kudryashov's Mathlib formalization.
The Hermitian and semilinear APIs extend those prior formalizations; the other
modules document their own mathematical and formalization sources.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
