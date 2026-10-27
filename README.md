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

- **Locally varying finite-rank atlas data:** covering fibrewise-linear charts on
  given module fibres and their given total-space topology, with linear coordinate
  equivalences, pointwise finite generation of the original fibres, and fixed-model
  bundle data on each chart domain. The models include arbitrary-base product bundles
  in every finite rank and discrete families with varying ranks, including zero.
  See the [atlas API](VectorBundles/Topology/VectorBundle/FiniteRank.lean),
  [`Bundle.FiniteRankAtlas.moduleFinite_fiber`](VectorBundles/Topology/VectorBundle/FiniteRank/LinearEquiv.lean),
  [patch data](VectorBundles/Topology/VectorBundle/FiniteRank/Patch.lean),
  [product models](VectorBundles/Topology/VectorBundle/FiniteRank/Trivial.lean) and
  [discrete models](VectorBundles/Topology/VectorBundle/FiniteRank/Discrete.lean).
- **Projections, zero sections and descent for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.continuous_proj`](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  and [`Bundle.FiniteRankAtlas.isOpenMap_proj`](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  prove that the original projection is continuous and open.
  [`Bundle.FiniteRankAtlas.isQuotientMap_proj`](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  makes it a quotient map, and
  [`Bundle.FiniteRankAtlas.continuous_iff_comp_proj`](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  characterizes continuity of maps from the base to any topological space by continuity
  after composition with this projection. The canonical zero section is continuous by
  [`Bundle.FiniteRankAtlas.continuous_zeroSection`](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean).
  These results hold for any supplied finite-rank atlas. Chart ranks may vary and may
  be zero, with no common model, scalar-operation continuity or base separation hypothesis.

The [detailed results guide](docs/Results.md) groups statements and examples by
topic, with their individual hypotheses and distinctions from existing Mathlib
constructions. Selected results include:

- **Compatible fiber metrics.**
  [`VectorBundle.continuousHermitianMetric`](VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  constructs continuous positive-definite Hermitian metrics on finite-dimensional
  `RCLike` vector bundles over paracompact Hausdorff bases. They induce the original
  fiber topologies; the normed model need not have an inner-product norm.

- **Splitting and comparison for supplied metrics.**
  For a supplied continuous Hermitian metric and an intrinsic submodule bundle
  whose total-space inclusion is an embedding, with finite-dimensional `RCLike`
  ambient model, [orthogonal addition](VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean)
  is a homeomorphism onto the ambient total space; [comparison](VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean)
  identifies its complements for two such metrics using their projections.
  The base is any topological space. Complement fiber subtype and ambient-induced
  total topologies are retained; no global intrinsic-model finiteness is required.

- **Pointwise-continuous surjectivity, without a norm.**
  Over a field with a given T₁ topology making it a topological ring,
  [`LinearMap.eventually_surjective_of_continuousAt`](VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  gives surjectivity near `b₀` from surjectivity there and each fixed-vector evaluation's
  `ContinuousAt` at `b₀`; [`LinearMap.isOpen_setOf_surjective`](VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  needs each fixed-vector evaluation `Continuous` for an open locus. The base is
  arbitrary, source purely algebraic with no topology, and target finite-dimensional
  with its given `IsModuleTopology`, in four independent universes. No scalar norm,
  inversion continuity, completeness, extra target continuity/separation hypotheses
  or base separation are required.

- **Openness of joint linear families and bundle maps.**
  Over a nontrivially normed field,
  [`LinearMap.isOpenMap_prodMap`](VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  makes jointly continuous algebraic linear surjections between topological vector
  spaces open on products when the finite-dimensional target has its given
  `IsModuleTopology`. The [bundle theorem](VectorBundles/Topology/VectorBundle/OpenMap.lean)
  transfers this over a common base with given linear trivializations and original
  fiber and total-space topologies. Neither model needs a norm, the source need not
  be finite-dimensional, and no completeness is assumed.

- **Forward continuity gives bundle inverses.**
  [`VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology`](VectorBundles/Topology/VectorBundle/Isomorphism.lean)
  constructs a homeomorphism from algebraic fiberwise linear equivalences with a
  continuous forward total map over a nontrivially normed field. The source normed
  model is finite-dimensional; the target normed model has `IsModuleTopology`.
  Empty bases and zero rank are allowed, and models need not be globally identified.
  A complete-field constructor derives the target properties at each base point.

- **Scalar endomorphisms of line bundles.**
  [`VectorBundle.scalarEndHomeomorph`](VectorBundles/Topology/VectorBundle/ScalarEnd.lean)
  identifies `B × κ` with the endomorphism bundle of a line bundle modeled on a
  nontrivially normed field `κ`, for any topological base `B`, including the empty
  base. Both directions preserve the base, using the original fiber topologies
  and continuous-linear-map bundle topology.

- **Sharp projection criteria.**
  A fiber-bundle projection is an [open embedding](VectorBundles/Topology/FiberBundle/Projection.lean)
  exactly when every original fiber is subsingleton, and canonically a homeomorphism
  when each is also nonempty. It is [proper](VectorBundles/Topology/FiberBundle/Proper.lean)
  exactly when every given fiber is compact, equivalently when the base is empty or
  the model is compact. The given topologies and fiber-bundle data are retained,
  without scalar or separation assumptions.

- **Second countability of total spaces.**
  [`FiberBundle.secondCountableTopology_totalSpace_iff`](VectorBundles/Topology/FiberBundle/Countability.lean)
  says the total space is second-countable exactly when the base is empty, the model
  is empty, or both are second-countable. Given topologies, fiber-bundle data and
  independent base/model/fiber universes are retained, without compactness or
  separation assumptions. Construction from second-countable factors is Mathlib's
  existing instance.

- **Finite complementary bundles and cylinder charts.**
  [`VectorBundle.finiteComplement`](VectorBundles/Topology/VectorBundle/FiniteComplement.lean)
  gives a finite-dimensional complement for a finite-dimensional `RCLike` bundle
  on a compact normal base, with a global linear trivialization of their fiberwise product.
  Subspace fiber and ambient-induced total topologies are retained; the complement
  is not asserted complementary or orthogonal to a prescribed embedding.
  [Whole-interval cylinder charts](VectorBundles/Topology/VectorBundle/Cylinder.lean)
  exist near each point of any `X` for a vector bundle over `X × unitInterval`,
  without dimension or completeness assumptions; this is not homotopy invariance.

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

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`. The direct dependencies are
[Mathlib](https://github.com/leanprover-community/mathlib4) at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`,
[Metrization](https://github.com/FormalFrontier/metrization) at
`4dcc0f6f903ba4d0c66f230d21f7ac4c31d4ea57`, and
[ProjectiveModules](https://github.com/FormalFrontier/projective-modules) at
`8e4495425bb19187fbeb7271d40a111b8ddf36de`.
Both deliverables use the Mathlib revision listed above. Their transitive
dependencies are pinned in `lake-manifest.json`.

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
| [`Topology.Bornology.Inducing`](VectorBundles/Topology/Bornology/Inducing.lean) | `IsVonNBounded.preimage_of_isInducing` over a general `NormedDivisionRing`, without injectivity or topological vector-space hypotheses |
| [`Topology.Compactness.CountablyCompact`](VectorBundles/Topology/Compactness/CountablyCompact.lean) | Countably compact preimages under proper maps exactly when the target subset intersected with the range is countably compact |
| [`Topology.Compactness.Lindelof`](VectorBundles/Topology/Compactness/Lindelof.lean) | Lindelöf inverse images under proper maps and products with compact or σ-compact sets, without separation assumptions |
| [`Topology.Compactness.SigmaCompact`](VectorBundles/Topology/Compactness/SigmaCompact.lean) | Sigma-compact inverse images under proper maps exactly when the target subset intersected with the range is sigma-compact |
| [`Topology.Compactness.Paracompact`](VectorBundles/Topology/Compactness/Paracompact.lean) | Paracompactness of continuous retracts and domains of proper maps; open-surjective-proper codomain theorem |
| [`Topology.LocallyFinite`](VectorBundles/Topology/LocallyFinite.lean) | Locally finite images under closed maps with compact point fibers; [infinite-index example](VectorBundlesTest/Topology/LocallyFinite.lean) |
| [`Topology.CompactOpen`](VectorBundles/Topology/CompactOpen.lean) | Locally constant compact-open images for jointly continuous homeomorphism families and their inverses |
| [`Topology.FiberBundle.CoordChange`](VectorBundles/Topology/FiberBundle/CoordChange.lean) | Jointly continuous coordinate-change homeomorphisms and inverses on the original chart overlap |
| [`Topology.Maps.Proper`](VectorBundles/Topology/Maps/Proper.lean) | Proper first projection for compact-valued upper hemicontinuous correspondences, without separation or ambient closedness |
| [`Topology.Connected.Basic`](VectorBundles/Topology/Connected/Basic.lean) | Preconnected preimages under open maps with preconnected fibers over a preconnected subset of the range |
| [`Topology.FiberBundle.Connected`](VectorBundles/Topology/FiberBundle/Connected.lean) | Preconnected projection preimages and preconnected/connected total spaces; [real and empty-model examples](VectorBundlesTest/Topology/FiberBundle/Connected.lean) |
| [`Topology.Separable.Basic`](VectorBundles/Topology/Separable/Basic.lean) | Ambient-separable preimages under open maps with all ambient fibers separable; arbitrary-set preimage equivalence for open quotient maps; separable domains for separable targets |
| [`Topology.FiberBundle.Separable`](VectorBundles/Topology/FiberBundle/Separable.lean) | Separable total spaces, model reflection at a specified base point, and a global equivalence under nonempty base and model, with original topologies and bundle data; [product, ambient-strip and empty-boundary examples](VectorBundlesTest/Topology/FiberBundle/Separable.lean) |
| [`Topology.FiberBundle.Projection`](VectorBundles/Topology/FiberBundle/Projection.lean) | Sharp projection criteria, canonical homeomorphism and inverse/zero-section formulas |
| [`Topology.FiberBundle.Proper`](VectorBundles/Topology/FiberBundle/Proper.lean) | Proper projection exactly when every fiber is compact; compactness transfer and equivalence without separation |
| [`Topology.FiberBundle.Countability`](VectorBundles/Topology/FiberBundle/Countability.lean) | `FiberBundle.secondCountableTopology`: second-countable total space from second-countable base and model, with original topologies and no nonemptiness or separation assumptions; [real-plane and empty-model examples](VectorBundlesTest/Topology/FiberBundle/Countability.lean) use the instance and Mathlib's converse APIs |
| [`Topology.FiberBundle.Metrizable`](VectorBundles/Topology/FiberBundle/Metrizable.lean) | Metrizable total space from metrizable base and model; model metrizability at a specified base point; [real-plane and empty-base examples](VectorBundlesTest/Topology/FiberBundle/Metrizable.lean) |
| [`Topology.FiberBundle.SigmaCompact`](VectorBundles/Topology/FiberBundle/SigmaCompact.lean) | Sigma-compact totals over R₁ bases; model reflection at an R₀ base point; factor characterization for nonempty base and model, preserving original topologies; [real-plane and empty-space examples](VectorBundlesTest/Topology/FiberBundle/SigmaCompact.lean) |
| [`Topology.FiberBundle.SigmaCompact.Proper`](VectorBundles/Topology/FiberBundle/SigmaCompact/Proper.lean) | For compact model, sigma-compact total space iff the model is empty or the original base is sigma-compact |
| [`Topology.FiberBundle.Trivialization.SigmaCompact`](VectorBundles/Topology/FiberBundle/Trivialization/SigmaCompact.lean) | Sigma-compact preimages of sigma-compact subsets inside a trivialization's base set, using the original projection and topologies |
| [`Topology.FiberBundle.SigmaCompact.LocallyCompactBase`](VectorBundles/Topology/FiberBundle/SigmaCompact/LocallyCompactBase.lean) | Sigma-compact total space over a locally compact Lindelöf base, with no separation or nonemptiness assumptions; [direct real-cylinder, real-plane, and empty-space examples](VectorBundlesTest/Topology/FiberBundle/SigmaCompact/LocallyCompactBase.lean) |
| [`Topology.FiberBundle.Trivialization.Lindelof`](VectorBundles/Topology/FiberBundle/Trivialization/Lindelof.lean) | Lindelöf preimages of sigma-compact subsets inside an original trivialization's base set with Lindelöf model, without global projection continuity; compact subsets via `hK.isSigmaCompact` |
| [`Topology.FiberBundle.Lindelof.LocallyCompactBase`](VectorBundles/Topology/FiberBundle/Lindelof/LocallyCompactBase.lean) | Lindelöf total space over a locally compact Lindelöf base with Lindelöf model, retaining original topologies and bundle data without separation or nonemptiness assumptions; [direct real-cylinder, real-plane, and empty-space examples](VectorBundlesTest/Topology/FiberBundle/Lindelof/LocallyCompactBase.lean) |
| [`Topology.FiberBundle.Lindelof`](VectorBundles/Topology/FiberBundle/Lindelof.lean) | Lindelöf total space from a countable cover by Lindelöf original chart base sets and a σ-compact model; hereditary-Lindelöf-base corollary |
| [`Topology.FiberBundle.Paracompact`](VectorBundles/Topology/FiberBundle/Paracompact.lean) | Paracompact model from an ambient-closed nonempty chart base patch; R₀-base point consequence and compact-model total spaces; empty-aware compact-model base equivalence |
| [`Topology.VectorBundle.CoordinateMap`](VectorBundles/Topology/VectorBundle/CoordinateMap.lean) | Linear-chart evaluations, operators and linear-atlas criterion |
| [`Topology.VectorBundle.FiniteSum`](VectorBundles/Topology/VectorBundle/FiniteSum.lean) | Locally finite sums of continuous sections |
| [`Topology.VectorBundle.Hom`](VectorBundles/Topology/VectorBundle/Hom.lean) | Identity and composition of continuous native Hom sections, with the model operator-norm topology |
| [`Topology.VectorBundle.ScalarEnd`](VectorBundles/Topology/VectorBundle/ScalarEnd.lean) | Base-preserving product homeomorphism for the endomorphism bundle of a line, with the original fiber topologies |
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
| [`Topology.VectorBundle.MetricComap`](VectorBundles/Topology/VectorBundle/MetricComap.lean) | Pointwise and continuous comaps of supplied metrics along fiberwise topological linear embeddings |
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
| [`VectorBundlesTest.Topology.FiberBundle.Lindelof`](VectorBundlesTest/Topology/FiberBundle/Lindelof.lean) | Real mixed products, a singleton chart cover, a trivial real bundle and an empty model over the real base |
| [`VectorBundlesTest`](VectorBundlesTest.lean) | Full examples: projection and properness boundaries, connectedness, separability, isomorphisms, metrics, semilinear evaluation, Hermitian metrics, metric pullbacks and comaps, shear-metric complement comparison, orthogonal complement/addition/projection, orthonormal charts, products, pullbacks, cylinder charts, frames, embeddings, ranges and finite complements |

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
Fiber-bundle metrizability follows the original formalization by Formal Frontier Agents
and uses Metrization's locally finite closed-neighbourhood-cover criterion.
The locally finite and paracompactness statements use Yury Kudryashov's locally
finite-family API, Reid Barton and Yury Kudryashov's paracompactness formalization,
and Anatole Dedecker and Etienne Marion's proper-map API in Mathlib.
The scalar-endomorphism construction uses ProjectiveModules' invertible-module
topology and continuous scalar-endomorphism equivalence, and Prism's formalization
of the algebraic scalar-endomorphism equivalence.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
