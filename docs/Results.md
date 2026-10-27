# Detailed results

[Back to the overview](../README.md#headline-results) ·
[Using the library](../README.md#using-the-library) ·
[Credits and license](../README.md#credits-and-license) · [License](../LICENSE)

Each description below carries its own hypotheses, examples and dependency
distinctions. Pointwise-continuous surjectivity is separate from the stronger
normed-field product and bundle statements.

## Topics

- [Metrics and complementary bundles](#metrics-and-complementary-bundles)
- [Pointwise-continuous surjectivity](#pointwise-continuous-surjectivity)
- [Continuous linear and bundle calculus](#continuous-linear-and-bundle-calculus)
- [Projections and pullbacks](#projections-and-pullbacks)
- [Proper and open maps](#proper-and-open-maps)
- [Topological properties of bundle total spaces](#topological-properties-of-bundle-total-spaces)

## Metrics and complementary bundles

- **Compatible fiber metrics.**
  [`VectorBundle.continuousHermitianMetric`](../VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  constructs a continuous positive-definite Hermitian metric on a finite-dimensional
  vector bundle over a paracompact Hausdorff base, over an `RCLike` field.
  The normed model need not have an inner-product norm; the resulting metric induces
  the existing fiber topologies. The
  [real specialization](../VectorBundles/Topology/VectorBundle/Metric.lean)
  returns Mathlib's continuous Riemannian metric data.
- **Positive operations on supplied metrics.**
  [`Bundle.HermitianMetric.add`](../VectorBundles/Topology/VectorBundle/HermitianMetric/Operations.lean)
  adds metrics on the same family, and `rescale` multiplies by a pointwise-positive
  real function, without base topology assumptions. Their continuous counterparts use
  the same given bundle structures and continuous real weights, with no finite-dimensionality
  or uniform lower bound. The [stock-plane use](../VectorBundlesTest/Topology/VectorBundle/HermitianMetric/Operations.lean)
  combines both operations over the real line for real and complex supremum-norm planes.
- **Pullback of supplied metrics.**
  [`Bundle.HermitianMetric.pullback`](../VectorBundles/Topology/VectorBundle/MetricPullback.lean)
  reindexes a metric along any base map, without base topologies or bundle data.
  `Bundle.ContinuousHermitianMetric.pullback` handles `ContinuousMapClass` maps
  using Mathlib's pullback bundle structures, with the same normed model and original
  fiber structures. No finite dimension is required. Pairing formulas and pointwise
  identity/composition laws are provided; equality of continuous structures across
  different Hom-bundle topologies is not asserted.
- **Comaps of supplied metrics.**
  [`Bundle.HermitianMetric.comap`](../VectorBundles/Topology/VectorBundle/MetricComap.lean)
  pulls a supplied metric back along same-base fiberwise continuous-linear
  topological embeddings; injectivity alone is not enough. The induced pairing is
  `g.inner b (a b v) (a b w)`. Pointwise comap needs no base topology, models
  or bundle structures. `Bundle.ContinuousHermitianMetric.comap` requires a
  continuous section of the native Hom bundle with its model operator-norm topology.
  Both bundles keep their original model norms, fiber and total-space topologies,
  and exact `FiberBundle`/`VectorBundle` structures; only the models are normed.
  Over `RCLike` scalars, bases and ranks are arbitrary and universes independent:
  no finite dimension, separation, nonemptiness or uniform lower bound is assumed.
  Forgetful, identity and contravariant composition laws preserve these pairings.
- **Orthogonal subbundles and splitting for a supplied metric.**
  [`Bundle.ContinuousHermitianMetric.orthogonalBundle`](../VectorBundles/Topology/VectorBundle/OrthogonalComplement.lean)
  constructs bundle data on the orthogonal family of an intrinsic submodule bundle
  whose total-space inclusion is an embedding. The ambient model is
  finite-dimensional over an `RCLike` field. The base is an arbitrary topological
  space: neither separation nor paracompactness is required. The complement retains
  its fiber subtype topologies and ambient-induced total topology.
  [Orthogonal addition](../VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean)
  is a homeomorphism from the fiberwise product onto the ambient total space, and
  [continuous projections](../VectorBundles/Topology/VectorBundle/OrthogonalProjection.lean)
  recover its two summands. The same module's
  `continuous_orthogonalProjectionOntoL`, `continuous_orthogonalProjectionL` and
  `continuous_orthogonalComplementProjectionL` assert continuity of Mathlib's
  existing continuous-linear projections as sections of the intrinsic-target and
  ambient-target Hom bundles. Both ambient fields have the same Hom topology;
  all fields retain the original model norms and bundle structures. No global
  finiteness assumption on the subbundle model or nonemptiness assumption on the
  base is needed.
- **Canonical comparison of orthogonal complements.**
  [`Bundle.ContinuousHermitianMetric.orthogonalComplementHomeomorph`](../VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean)
  compares the complements of the same embedded intrinsic submodule bundle for two
  supplied continuous metrics. Only the ambient model is assumed finite-dimensional,
  over an `RCLike` field. The complement total spaces retain their ambient-induced
  topologies, with the second metric's projection as the forward map and the first
  metric's projection as its inverse. Fiberwise quotient formulas, base preservation,
  equal-metric identity and three-metric composition are provided. No global intrinsic
  finiteness or nonempty-base assumption is required.
- **Orthonormal local coordinates.**
  [`Bundle.ContinuousHermitianMetric.orthonormalizeTrivialization`](../VectorBundles/Topology/VectorBundle/OrthonormalTrivialization.lean)
  changes any linear chart of a finite-dimensional `RCLike` bundle with a supplied
  continuous Hermitian metric to Euclidean coordinates on exactly the same base
  set, preserving the metric pairing. This does not install new norms or
  topologies, or assert an adapted subbundle frame or a parametric Gram–Schmidt
  algorithm.
- **Finite complementary bundles.**
  [`VectorBundle.finiteComplement`](../VectorBundles/Topology/VectorBundle/FiniteComplement.lean)
  constructs a finite-dimensional complement to a finite-dimensional vector bundle
  over an `RCLike` field on a compact normal base, together with a global linear
  trivialization of their fiberwise product. The complement retains its subspace
  fiber topologies and ambient-induced total topology. It is not asserted to be
  complementary or orthogonal to a prescribed ambient embedding.

## Pointwise-continuous surjectivity

- **Surjectivity loci of pointwise-continuous linear families.**
  Over a field with a T₁ topology making it a topological ring,
  [`LinearMap.eventually_surjective_of_continuousAt`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  gives local persistence of surjectivity from continuity of each fixed-vector evaluation
  at a base point.
  [`LinearMap.isOpen_setOf_surjective`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  gives an open surjectivity locus for pointwise-continuous families. The source module
  needs no topology; the finite-dimensional target retains its given `IsModuleTopology`.
  No scalar norm, continuous inversion or completeness is assumed.

## Continuous linear and bundle calculus

- **Scalar endomorphisms of a line bundle.**
  [`VectorBundle.scalarEndHomeomorph`](../VectorBundles/Topology/VectorBundle/ScalarEnd.lean)
  identifies `B × κ` with the endomorphism bundle of a line bundle modeled on a
  nontrivially normed field `κ`, over an arbitrary topological base `B`, including
  the empty base. Both directions preserve the base coordinate, using the original
  fiber topologies and the bundle topology of continuous linear maps.

- **Openness of surjective linear families and bundle maps.**
  Over a nontrivially normed field,
  [`LinearMap.isOpenMap_prodMap`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  makes a jointly continuous family of algebraic linear surjections between topological
  vector spaces open on products when the finite-dimensional target carries its given
  `IsModuleTopology`.
  [`Bundle.isOpenMap_totalSpaceMap`](../VectorBundles/Topology/VectorBundle/OpenMap.lean)
  transfers this to bundles over their common base with given linear trivializations,
  retaining the original fibre and total-space topologies. Neither model requires a
  norm; the source need not be finite-dimensional, and no completeness is assumed.
- **Forward continuity implies inverse continuity.**
  [`VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology`](../VectorBundles/Topology/VectorBundle/Isomorphism.lean)
  constructs a total-space homeomorphism from a family of algebraic fiberwise
  linear equivalences with continuous forward total map. The source normed model
  is finite-dimensional over a nontrivially normed field; the target normed model
  has `IsModuleTopology`. The complete-field constructor derives the required
  target properties at each base point. Empty bases and zero-rank bundles are
  allowed; the two models need not be globally identified.
- **Linear coordinates and operator continuity.**
  [Coordinate maps](../VectorBundles/Topology/VectorBundle/CoordinateMap.lean)
  of a continuous fiberwise-linear total map have jointly continuous evaluations,
  including independent source and target bases and an arbitrary covered base map.
  For a finite-dimensional source model with its module topology, the same-base
  coordinate operators are continuous for bounded convergence.
  `VectorBundle.of_isLinear` equips an existing fiber bundle with a vector-bundle
  structure when its chosen atlas is linear and its finite-dimensional normed
  model has the module topology. The original atlas and topologies are retained.

- **Pullbacks, products and cylinder charts.**
  [Pullback total spaces](../VectorBundles/Topology/FiberBundle/Pullback.lean)
  identify with compatible-pair subspaces and satisfy a universal mapping property,
  even for a base map that is not continuous. This is an underlying-space statement,
  not local triviality for a discontinuous map.
  [Fiberwise products](../VectorBundles/Topology/FiberBundle/Prod.lean)
  have canonical swap and reassociation homeomorphisms for their existing topologies.
  A [vector bundle over `X × unitInterval`](../VectorBundles/Topology/VectorBundle/Cylinder.lean)
  has, near each point of an arbitrary `X`, a linear chart valid for the whole
  interval, without completeness or dimension assumptions. This is not a
  homotopy-invariance theorem.

## Projections and pullbacks

- **Projection criteria and canonical homeomorphisms.**
  [`FiberBundle.isOpenEmbedding_proj_iff`](../VectorBundles/Topology/FiberBundle/Projection.lean)
  characterizes open-embedding projections by every original fiber being subsingleton.
  `FiberBundle.homeomorphProj` constructs the canonical projection homeomorphism when
  every fiber is also nonempty, with forward, inverse/base, dependent-pair and given-zero-section
  formulas. These results need no scalar, norm, separation or nonempty-base hypothesis;
  the model assumptions are only sufficient corollaries.
  [`FiberBundle.isEmpty_totalSpace_iff`](../VectorBundles/Topology/FiberBundle/Basic.lean)
  characterizes empty total space by emptiness of the base or model, without compactness assumptions.
- **Proper fiber-bundle projections.**
  [`FiberBundle.isProperMap_proj_iff`](../VectorBundles/Topology/FiberBundle/Proper.lean)
  characterizes proper projections by compactness of every fiber with its given
  topology. `FiberBundle.isProperMap_proj` gives the compact-model sufficient
  criterion. `FiberBundle.isProperMap_proj_iff_isEmpty_or_compactSpace` states the
  equivalent model-space criterion: the base is empty or the model is compact.
  Properness is Mathlib's `IsProperMap` (continuity and universal closedness).
  These statements use the given base, model, total-space and fiber topologies and
  their fiber-bundle structure, with independent universes and no separation,
  local compactness or nonemptiness assumptions.
- **Proper canonical pullback lifts.**
  [`Bundle.Pullback.isProperMap_lift`](../VectorBundles/Topology/FiberBundle/Pullback/Proper.lean)
  gives a proper lift from a proper base map and continuity of the original bundle
  projection. It retains the canonical pullback and original total-space topologies,
  with independent universes and no fiber topology, local triviality or separation
  assumptions. The [two direct examples](../VectorBundlesTest/Topology/FiberBundle/Pullback/Proper.lean)
  exhibit the proper noninjective base map `ℝ × Fin 2 → ℝ`, continuity of the original
  trivial-bundle projection and a noninjective proper lift, together with an
  empty-original-fiber boundary.

## Proper and open maps

- **Compact inverse images and ranges of proper maps.**
  [`IsProperMap.isCompact_preimage_iff`](../VectorBundles/Topology/Maps/Proper.lean)
  characterizes compactness of `f ⁻¹' s` by compactness of `s ∩ Set.range f` for a
  proper map `f : X → Y`. For `s ⊆ Set.range f`,
  `IsProperMap.isCompact_preimage_iff_of_subset_range` reduces this to compactness of
  `s`; `IsProperMap.compactSpace_iff_isCompact_range` characterizes compactness of
  the domain by compactness of the range. The original topologies and independent
  universes are retained, without separation, nonemptiness or surjectivity assumptions.
  The [examples](../VectorBundlesTest/Topology/Maps/Proper.lean) use the real two-sheeted
  projection over `[0, 1]` and the closed-interval inclusion into the noncompact real line.
- **Countable compactness and proper maps.**
  [`IsProperMap.isCountablyCompact_preimage_iff`](../VectorBundles/Topology/Compactness/CountablyCompact.lean)
  characterizes countable compactness of `f ⁻¹' s` by that of `s ∩ Set.range f` for
  a proper map `f : X → Y`. The subset-of-range corollary removes the intersection,
  and `IsProperMap.countablyCompactSpace_iff_isCountablyCompact_range` characterizes
  a countably compact domain by a countably compact range. These results use cluster
  points of nonbottom countably generated filters, with the original topologies and
  independent universes, without separation or surjectivity assumptions. The
  [examples](../VectorBundlesTest/Topology/Compactness/CountablyCompact.lean) use the real
  two-sheeted projection over `[0, 1]` and the nonsurjective closed-interval inclusion.
- **Sigma-compactness and proper maps.**
  [`IsProperMap.isSigmaCompact_preimage_iff`](../VectorBundles/Topology/Compactness/SigmaCompact.lean)
  characterizes sigma-compactness of `f ⁻¹' s` by that of `s ∩ Set.range f`;
  `IsProperMap.sigmaCompactSpace` gives the sigma-compact-domain consequence.
  [`FiberBundle.sigmaCompactSpace_totalSpace_iff_of_compactSpace_model`](../VectorBundles/Topology/FiberBundle/SigmaCompact/Proper.lean)
  characterizes sigma-compactness of a compact-model bundle's total space by
  `IsEmpty F ∨ SigmaCompactSpace B`. These results retain the original topologies
  and independent universes, without separation, local compactness, surjectivity
  or nonemptiness assumptions. The
  [proper-map examples](../VectorBundlesTest/Topology/Compactness/SigmaCompact.lean)
  include the real two-sheeted projection, an interval under the identity, and
  an arbitrary subset outside an empty range. The
  [bundle examples](../VectorBundlesTest/Topology/FiberBundle/SigmaCompact/Proper.lean)
  include reflection for the one-point real cylinder and an empty model over
  an arbitrary base.
- **Compact-open images and joint coordinate changes.**
  [`TopologicalSpace.CompactOpens.isLocallyConstant_map`](../VectorBundles/Topology/CompactOpen.lean)
  gives locally constant images of a compact open set under a family of
  homeomorphisms with jointly continuous forward and inverse evaluations.
  [`Bundle.Trivialization.continuous_coordChange_uncurry`](../VectorBundles/Topology/FiberBundle/CoordChange.lean)
  and `Bundle.Trivialization.continuous_coordChangeHomeomorph_symm_uncurry`
  give both joint continuities on the original overlap subtype times the model.
  These results retain the original topologies and independent universes, without
  local compactness, separation or nonemptiness assumptions. The
  [examples](../VectorBundlesTest/Topology/CompactOpen.lean) use a nonempty proper
  compact open set in a two-point space and the canonical trivial real bundle.
- **Proper graph projections.**
  [`Set.isProperMap_fst_of_upperHemicontinuous`](../VectorBundles/Topology/Maps/Proper.lean)
  gives a proper first projection from a subset of a product when its fibers are
  compact and vary upper hemicontinuously. The original topologies and independent
  base and fiber universes are retained, without separation, local compactness,
  nonemptiness or ambient closedness assumptions. The
  [examples](../VectorBundlesTest/Topology/CompactOpen.lean) include the real strip
  `ℝ ×ˢ Icc 0 1` and an empty fiber.
- **Preconnected preimages under open maps.**
  [`IsPreconnected.preimage_of_isOpenMap_of_isPreconnected_fibers`](../VectorBundles/Topology/Connected/Basic.lean)
  gives preconnected `f ⁻¹' s` when `f` is open, `s` is preconnected and contained
  in `Set.range f`, and `f ⁻¹' {y}` is preconnected for every `y ∈ s`.
  No continuity, global surjectivity or separation assumptions are required.
- **Ambient-separable preimages under open maps.**
  [`TopologicalSpace.IsSeparable.preimage_of_isOpenMap_of_isSeparable_fibers`](../VectorBundles/Topology/Separable/Basic.lean)
  gives ambient-separable `f ⁻¹' s` from ambient-separable `s`, an open map `f : X → Y`,
  and ambient separability of `f ⁻¹' {y}` for every `y : Y`. Ambient countable
  witnesses need not lie in the sets they approximate. The original topologies
  and independent universes are retained; no continuity, surjectivity, range
  condition, nonemptiness or separation assumption is required. For an open quotient
  map with the same all-fibers hypothesis,
  `IsOpenQuotientMap.isSeparable_preimage_iff` characterizes ambient separability of
  an arbitrary set by ambient separability of its preimage. Neither ambient space
  need be separable, and the set need not be open or nonempty.
- **Separable domains of open maps.**
  [`IsOpenMap.separableSpace_of_isSeparable_fibers`](../VectorBundles/Topology/Separable/Basic.lean)
  gives `SeparableSpace X` from `SeparableSpace Y`, openness of `f : X → Y`
  and ambient separability of every original fiber, with no continuity or
  surjectivity assumption.

## Topological properties of bundle total spaces

- **Lindelöf products, proper inverse images and fiber bundles.**
  [`IsProperMap.isLindelof_preimage`](../VectorBundles/Topology/Compactness/Lindelof.lean)
  gives Lindelöf inverse images of arbitrary Lindelöf subsets under proper maps,
  without separation, local compactness or nonemptiness assumptions.
  `IsProperMap.isLindelof_preimage_iff` characterizes Lindelöfness of an inverse
  image by Lindelöfness of the target subset intersected with the map's range,
  without requiring surjectivity. The
  [examples](../VectorBundlesTest/Topology/Maps/ProperLindelof.lean) use a two-sheeted
  real projection over a noncompact ray and over the empty set.
  [Lindelöf sets times compact or σ-compact sets](../VectorBundles/Topology/Compactness/Lindelof.lean)
  are Lindelöf in arbitrary topological spaces.
  [`FiberBundle.lindelofSpace_of_countable_trivializationAt_cover`](../VectorBundles/Topology/FiberBundle/Lindelof.lean)
  gives a Lindelöf total space for a σ-compact model when a countable family of
  the given `trivializationAt` base sets covers the base and each selected base set
  is Lindelöf. In particular,
  `FiberBundle.lindelofSpace_of_hereditarilyLindelof` applies to a hereditarily
  Lindelöf base and a σ-compact model. Both results retain the given topologies
  on the base, model, total space and individual fibers and the given `FiberBundle`
  structure, with no separation or nonemptiness assumptions.
- **[Lindelöf total spaces with compact models](../VectorBundles/Topology/FiberBundle/Lindelof/Proper.lean).**
  `FiberBundle.lindelofSpace_totalSpace` gives a Lindelöf total space from a Lindelöf base and compact model,
  retaining the original topologies, given fiber-bundle structure and independent universes.
  For a compact model `F` over a base `B`,
  `FiberBundle.lindelofSpace_totalSpace_iff` characterizes a Lindelöf total space by
  `IsEmpty F ∨ LindelofSpace B`; an empty model does not force the base to be Lindelöf.
- **Compactness of fiber bundles without separation assumptions.**
  [`FiberBundle.compactSpace_totalSpace`](../VectorBundles/Topology/FiberBundle/Proper.lean)
  gives compact total space from a compact base and compact model, including empty spaces.
  `FiberBundle.compactSpace_model` recovers compactness of the model from compactness
  of the total space and a specified base point, even when the model is empty.
  `FiberBundle.compactSpace_totalSpace_iff` characterizes compact total space by compact
  base and compact model when both base and model are nonempty.
  `FiberBundle.compactSpace_totalSpace_iff_isEmpty_or_compactSpace` states the
  characterization without nonemptiness assumptions: the base is empty, the model
  is empty, or both are compact. These statements use the four given topologies and
  their fiber-bundle structure, with independent universes and no separation or
  local compactness assumptions. The [examples](../VectorBundlesTest/Topology/FiberBundle/Proper.lean)
  include the two-point bundle over a point, an empty base with real model, and
  an empty model over the real line.
- **Local compactness of fiber bundles without separation assumptions.**
  [`FiberBundle.locallyCompactSpace_model`](../VectorBundles/Topology/FiberBundle/LocallyCompact.lean)
  recovers local compactness of the model from a locally compact total space and a
  specified base point, even when the model is empty.
  `FiberBundle.locallyCompactSpace_totalSpace_iff` characterizes local compactness of
  the total space by local compactness of the base and model when both are nonempty.
  The construction from locally compact base and model is Mathlib's existing
  `ChartedSpace.locallyCompactSpace`. All results retain the original topologies and
  fiber-bundle structure, with no separation assumptions.
- **Connectedness of fiber bundles.**
  [`FiberBundle.isPreconnected_preimage_proj`](../VectorBundles/Topology/FiberBundle/Connected.lean)
  gives preconnected projection preimages of preconnected base subsets when the
  model is preconnected. `FiberBundle.preconnectedSpace_totalSpace` and
  `FiberBundle.connectedSpace_totalSpace` give the corresponding total-space
  conclusions from preconnected, respectively connected, base and model.
  These use the given base, model, fiber and total-space topologies and fiber-bundle
  structure, with independent base, model and fiber universes and no separation assumptions.
  Preconnectedness allows empty models; `ConnectedSpace` includes nonemptiness.
  Connected total space need not imply a connected model.
- **Sharp second countability for fiber bundles.**
  [`FiberBundle.secondCountableTopology_totalSpace_iff`](../VectorBundles/Topology/FiberBundle/Countability.lean)
  characterizes second countability of the total space: either the base is empty,
  the model is empty, or both base and model are second-countable. The supplied
  topologies and fiber-bundle structure are unchanged, and base, model and fibers
  may lie in independent universes. No compactness, separation, nonemptiness or
  vector-space assumption is needed. The existing `FiberBundle.secondCountableTopology`
  instance supplies the forward construction from second-countable factors.
  The [real-plane and empty-base/model examples](../VectorBundlesTest/Topology/FiberBundle/Countability.lean)
  apply the criterion, including a noncompact real model and empty total spaces
  without countability assumptions on the unused factor.

- **Metrizability of fiber bundles.**
  [`FiberBundle.metrizableSpace_totalSpace`](../VectorBundles/Topology/FiberBundle/Metrizable.lean)
  gives a metrizable total space from a metrizable base and model, with their original
  topologies and fiber-bundle structure. `FiberBundle.metrizableSpace_model` recovers
  metrizability of the model from the total space at a specified base point.
  Base, model and fibers have independent universes; neither result requires an inhabited
  model or scalar or vector-space structure. The [real-plane and empty-base examples](../VectorBundlesTest/Topology/FiberBundle/Metrizable.lean)
  show the uses and the need for a base point in the model conclusion. No converse for the
  base is asserted.
- **Separability of fiber bundles.**
  [`FiberBundle.separableSpace_totalSpace`](../VectorBundles/Topology/FiberBundle/Separable.lean)
  gives a separable total space from a separable base and model, using the
  given fiber-bundle data and all four original topologies. The base, model
  and fiber universes are independent; this direction needs no second-countability,
  separation or nonemptiness assumption. `FiberBundle.separableSpace_model`
  recovers model separability from the total space at a specified base point,
  even for an empty model. For a nonempty model, base reflection is Mathlib's exact
  `(FiberBundle.isQuotientMap_proj F E).separableSpace`.
  `FiberBundle.separableSpace_totalSpace_iff` characterizes separable total space
  by separability of both base and model when both are nonempty, as an explicit
  theorem rather than a backward instance. The
  [examples](../VectorBundlesTest/Topology/FiberBundle/Separable.lean) include generic
  products, arbitrary ambient strips, the original bundle projection, and cheap
  empty-model and empty-base boundaries. The subset equivalence uses the generic
  open-quotient theorem on the original bundle projection.
- **Sigma-compactness of fiber-bundle total spaces.**
  [`FiberBundle.sigmaCompactSpace`](../VectorBundles/Topology/FiberBundle/SigmaCompact.lean)
  gives a sigma-compact total space from an R₁ sigma-compact base and a sigma-compact
  model, retaining the original topologies and fiber-bundle structure. Base, model
  and fibers have independent universes; no nonemptiness, local compactness, scalar
  or finite-dimensionality assumption is needed, nor separation of the model or
  total space. `FiberBundle.sigmaCompactSpace_model` reflects sigma-compactness to
  the model at any specified point of an R₀ base, even when the model is empty.
  `FiberBundle.sigmaCompactSpace_totalSpace_iff` characterizes sigma-compact totals
  by sigma-compact base and model when the base is R₁ and both factors are nonempty.
  The chart-level `Bundle.Trivialization.sigmaCompactSpace_model_of_isClosed`
  reflects sigma-compactness of the original ambient space to the model when the
  original projection is continuous and a closed nonempty subset of the base lies
  in the chart's base set. The [real-plane and empty-space examples](../VectorBundlesTest/Topology/FiberBundle/SigmaCompact.lean)
  use these results directly without replacing the original bundle data.
  The same module's `FiberBundle.sigmaCompactSpace_of_countable_closed_compact_cover`
  gives another sufficient condition: a sigma-compact base without separation and a
  countable cover of the model by closed compact sets.
  `FiberBundle.sigmaCompactSpace_of_r1Space_model` derives the R₁ sigma-compact-model
  case, with no base separation. Direct examples include the canonical Sierpiński
  base and both empty boundaries.
  For a sigma-compact base and quasi-separated model,
  `FiberBundle.sigmaCompactSpace_of_countable_open_compact_cover` instead uses a
  countable cover by compact open sets, which need not be closed.
  `FiberBundle.sigmaCompactSpace_of_open_nhdsKer_cover` applies when the model is
  sigma-compact and covered by open neighborhood kernels of singletons; not every
  singleton kernel must be open. Both retain the original topologies without
  nonemptiness or base-separation assumptions. The
  [compact-open examples](../VectorBundlesTest/Topology/FiberBundle/SigmaCompactKernel.lean)
  include direct uses and empty-model boundaries.
- **Sigma-compactness over locally compact Lindelöf bases.**
  [`FiberBundle.sigmaCompactSpace_of_locallyCompactSpace_base`](../VectorBundles/Topology/FiberBundle/SigmaCompact/LocallyCompactBase.lean)
  gives sigma-compactness of the original total space from a locally compact
  Lindelöf base and sigma-compact model, without separation or nonemptiness
  assumptions. All four topology instances and the original fiber-bundle data
  are retained, with independent base, model, and fiber universes.
  The chart-level
  [`Bundle.Trivialization.isSigmaCompact_preimage`](../VectorBundles/Topology/FiberBundle/Trivialization/SigmaCompact.lean)
  applies to any sigma-compact subset of a chart's base set and does not require
  global continuity of the projection. The
  [direct examples](../VectorBundlesTest/Topology/FiberBundle/SigmaCompact/LocallyCompactBase.lean)
  treat a compact real cylinder, the real-plane trivial bundle, an empty base,
  and an empty model.
- **Lindelöf bundles over locally compact Lindelöf bases.**
  [`FiberBundle.lindelofSpace_of_locallyCompactSpace_base`](../VectorBundles/Topology/FiberBundle/Lindelof/LocallyCompactBase.lean)
  gives a Lindelöf original total space from a locally compact Lindelöf base
  and a Lindelöf model; the model need not be sigma-compact. The original
  base, model, total-space and fiber topologies and the coupled `FiberBundle`
  data are retained, with independent universes and no separation or
  nonemptiness assumptions. The chart-level
  [`Bundle.Trivialization.isLindelof_preimage`](../VectorBundles/Topology/FiberBundle/Trivialization/Lindelof.lean)
  applies to a sigma-compact subset contained in the original chart's base set
  when the model is Lindelöf, without global continuity of the projection.
  Compact supported subsets use the same theorem via `hK.isSigmaCompact`.
  The [direct examples](../VectorBundlesTest/Topology/FiberBundle/Lindelof/LocallyCompactBase.lean)
  treat the compact real cylinder, the real plane, an empty base, and an empty model.
- **Lindelöf model reflection.**
  The [reflection module](../VectorBundles/Topology/FiberBundle/Lindelof/Reflection.lean)
  states that a chart of a continuous map with Lindelöf domain has Lindelöf model
  when its base set contains a nonempty subset closed in the ambient base. For a
  fiber bundle, Lindelöfness of the original total space and a specified point of
  an R₀ base imply Lindelöfness of the model. Both statements retain the original
  topologies and allow an empty model; the chart statement requires no separation
  assumptions on the base or model.
- **Paracompact retracts and bundle models.**
  A [continuous retract](../VectorBundles/Topology/Compactness/Paracompact.lean) of a
  paracompact space is paracompact, without separation or nonemptiness assumptions.
  The [chart and bundle results](../VectorBundles/Topology/FiberBundle/Paracompact.lean)
  reflect paracompactness of the original domain to the model over an ambient-closed
  nonempty chart base patch, for a continuous projection. The patch need not be compact.
  For a fiber bundle, a specified point of an R₀ base suffices. The original base,
  model, total-space and fiber topologies are retained, and the model may be empty.
- **Proper inverse images and compact-model total spaces.**
  [`IsProperMap.paracompactSpace`](../VectorBundles/Topology/Compactness/Paracompact.lean)
  gives a paracompact domain for a proper map to a paracompact space.
  [`FiberBundle.paracompactSpace_totalSpace`](../VectorBundles/Topology/FiberBundle/Paracompact.lean)
  gives a paracompact total space from a paracompact base and compact model.
  Both retain the original topologies and independent universes, without separation,
  surjectivity or nonemptiness assumptions; the bundle keeps its given structure.
- **Locally finite images and compact-model base characterization.**
  [`IsClosedMap.locallyFinite_image`](../VectorBundles/Topology/LocallyFinite.lean)
  states that a closed map with compact point fibers sends arbitrary locally finite
  families to locally finite families, without continuity, openness or surjectivity.
  [`IsProperMap.paracompactSpace_codomain`](../VectorBundles/Topology/Compactness/Paracompact.lean)
  states paracompactness of the codomain of an open surjective proper map from a
  paracompact space.
  [`FiberBundle.paracompactSpace_totalSpace_iff`](../VectorBundles/Topology/FiberBundle/Paracompact.lean)
  states, for a compact model, that the original total space is paracompact exactly
  when the model is empty or the base is paracompact. The statements
  retain the original topologies and independent universes,
  without separation or nonemptiness assumptions. The
  [locally finite example](../VectorBundlesTest/Topology/LocallyFinite.lean) uses an
  infinite family of nonempty fibers of `ℕ × Fin 2 → ℕ`; the
  [paracompactness examples](../VectorBundlesTest/Topology/FiberBundle/Paracompact.lean)
  apply the statements to the two-sheeted real projection, the canonical two-sheeted
  real bundle, and an empty model over an arbitrary topological base.
