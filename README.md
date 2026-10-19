# Vector bundles

Foundational geometry of topological vector bundles: compatible real and complex
fiber metrics, orthogonal splitting for a supplied metric, and homeomorphisms
induced by fiberwise linear equivalences. The library extends Mathlib's bundle
structures and uses their original fiber and total-space topologies.

## Headline results

- **Compatible fiber metrics.**
  [`VectorBundle.continuousHermitianMetric`](VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  constructs a continuous positive-definite Hermitian metric on a finite-dimensional
  vector bundle over a paracompact Hausdorff base, over an `RCLike` field.
  The normed model need not have an inner-product norm; the resulting metric induces
  the existing fiber topologies. The
  [real specialization](VectorBundles/Topology/VectorBundle/Metric.lean)
  returns Mathlib's continuous Riemannian metric data.
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
  recover its two summands. No global finiteness assumption on the subbundle model
  or nonemptiness assumption on the base is needed.
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

Paths below are relative to `VectorBundles/`; examples use the corresponding
`VectorBundlesTest/Topology/VectorBundle/` paths.

| Module | Contents |
| --- | --- |
| [`Analysis.InnerProductSpace.PositiveForm`](VectorBundles/Analysis/InnerProductSpace/PositiveForm.lean) | Bounded positive-form unit sublevels in the original topology |
| [`Analysis.Normed.Ring.Units`](VectorBundles/Analysis/Normed/Ring/Units.lean) | Value embedding for units of a seminormed ring |
| [`Topology.Algebra.Module.FiniteDimensionalOperator`](VectorBundles/Topology/Algebra/Module/FiniteDimensionalOperator.lean) | Pointwise versus bounded-convergence operator criteria |
| [`Topology.VectorBundle.CoordinateMap`](VectorBundles/Topology/VectorBundle/CoordinateMap.lean) | Linear-chart evaluations, operators and linear-atlas criterion |
| [`Topology.VectorBundle.FiniteSum`](VectorBundles/Topology/VectorBundle/FiniteSum.lean) | Locally finite sums of continuous sections |
| [`Topology.VectorBundle.SemilinearEvaluation`](VectorBundles/Topology/VectorBundle/SemilinearEvaluation.lean) | One- and two-argument evaluation on Mathlib's Hom topology |
| [`Topology.VectorBundle.WeightedForm`](VectorBundles/Topology/VectorBundle/WeightedForm.lean) | Supported weighted forms in linear charts |
| [`Topology.VectorBundle.HermitianMetric`](VectorBundles/Topology/VectorBundle/HermitianMetric.lean) | Hermitian metric data, continuity, Core conversion and real bridges |
| [`Topology.VectorBundle.MetricModel`](VectorBundles/Topology/VectorBundle/MetricModel.lean) | Compatible forms on finite-dimensional normed models |
| [`Topology.VectorBundle.MetricExistence`](VectorBundles/Topology/VectorBundle/MetricExistence.lean) | Partition-of-unity construction of continuous Hermitian metrics |
| [`Topology.VectorBundle.Metric`](VectorBundles/Topology/VectorBundle/Metric.lean) | Real Riemannian specialization |
| [`Topology.VectorBundle.Isomorphism`](VectorBundles/Topology/VectorBundle/Isomorphism.lean) | Fiberwise equivalences with only forward continuity supplied |
| [`Topology.VectorBundle.OrthogonalComplement`](VectorBundles/Topology/VectorBundle/OrthogonalComplement.lean) | Orthogonal subbundle with original subtype topologies |
| [`Topology.VectorBundle.OrthogonalAddition`](VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean) | Prescribed addition homeomorphism |
| [`Topology.VectorBundle.OrthogonalProjection`](VectorBundles/Topology/VectorBundle/OrthogonalProjection.lean) | Continuous total-space projections and fiber formulas |
| [`Topology.VectorBundle.OrthonormalTrivialization`](VectorBundles/Topology/VectorBundle/OrthonormalTrivialization.lean) | Pairing-preserving Euclidean chart coordinates |
| [`VectorBundlesTest`](VectorBundlesTest.lean) | Full examples: isomorphisms, metrics, semilinear evaluation, Hermitian metrics, orthogonal complement/addition/projection, and orthonormal charts |

## Conventions and limitations

Hermitian forms are conjugate-linear in the first argument and linear in the second.
Metric compatibility concerns topology, not preservation of an unrelated existing
norm. Only model fibers need norms; the bundle fibers retain their existing
algebraic and topological structures. The real metric bridges use Mathlib's
Riemannian data rather than introducing a second real metric class.

Metric existence and supplied-metric splitting have different hypotheses. The
latter is not a metric-existence assertion. No stable-triviality, classification,
constant-rank kernel-bundle, tensor-product or projective-section theorem is
provided here. The units embedding does not assert that the unit locus is open
or that partial inversion on the ambient ring is continuous. The finite-operator
criterion requires the source's module topology, which cannot simply be dropped
over an incomplete field.

## References

- Allen Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html),
  version 2.2 (November 2017), §1.1: Lemma 1.1, Proposition 1.2 and its Hermitian
  remark, and the supplied-metric geometric ingredients of Proposition 1.3.
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
The Hermitian and semilinear APIs extend those prior formalizations; the other
modules document their own mathematical and formalization sources.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
