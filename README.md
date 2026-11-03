# Vector bundles

Foundational geometry of topological vector bundles: compatible real and complex
fiber metrics and their pullbacks, orthogonal splitting and comparison for supplied
metrics, and homeomorphisms induced by fiberwise linear equivalences, together with
products, pullbacks, cylinder charts, finite ordered cylinder transport, frames,
finite embeddings, ranges and complementary bundles. The library extends Mathlib's
bundle structures and uses their original fiber and total-space topologies. It also gives projection criteria,
canonical projection homeomorphisms, properness criteria and compactness transfer for
topological fiber bundles.

## Headline results

- Over a possibly incomplete nontrivially normed field, a family of existing continuous linear
  maps between given seminormed norm-compatible vector spaces, with finite-dimensional original
  domain, is continuous in the original operator-norm topology exactly when every original
  fixed-vector evaluation is continuous
  (`ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional` in
  [module](VectorBundles/Topology/Module/FiniteCoordinates/FiniteDimensional.lean)).

These families are proved here, with the original fiber and total-space topologies.
The [catalogue](docs/HeadlineResults.md) gives the individual statements and variants;
the [detailed guide](docs/Results.md) adds examples and distinguishes Mathlib constructions.

- **Nearby noncommuting idempotents.** For bounded idempotents `P` and `Q` on a
  normed space over a nontrivially normed field, finite-dimensional range of `P`
  and `‖Q - P‖ < 1` give continuous linear equivalences between their ranges and
  between their kernels. The
  [compression and kernel-coordinate constructions](VectorBundles/Analysis/Normed/Operator/NearbyIdempotent.lean)
  use the original subspace norms; neither the field nor the ambient space needs
  to be complete. Finite dimension of the range of `Q` is a consequence, not an
  extra hypothesis. For a continuous family of idempotents over an arbitrary
  topological base, the kernel graph on the norm neighborhood has product
  coordinates preserving the base point. A kernel section is continuous exactly
  when its fixed-kernel coordinate is continuous.

- **Supported weighted coordinates.** Given module families over a commutative semiring
  and linear chart equivalences on arbitrary subsets, the
  [weighted coordinate map](VectorBundles/LinearAlgebra/WeightedCoordinates.lean)
  takes values in the full dependent product of model modules. Its membership,
  nonmembership, zero-weight and chart-evaluation rules are explicit. At each point,
  generating the unit ideal by the valid chart weights suffices for fibrewise
  injectivity. In particular, one valid unit weight suffices; no individual
  weight need be a unit in the general criterion.
  On the original equality fibres of a topological projection, with given module
  operations and inherited topology, the
  [total coordinate map](VectorBundles/Topology/Maps/WeightedCoordinates.lean)
  is continuous when the projection, weights and exact inverse coordinates are
  continuous, scalar multiplication on each model is continuous, and the closure
  of each weight's cozero set lies in its domain. No openness, finite-index,
  finite-dimensionality, norm or continuity of fibre operations is required.

- **Additive sum–kernel coordinates.** For a projection `p : T → B` with given
  additive monoid structures on its equality fibres, additive maps `β b` into a
  topological abelian group `A` and retractions `ρ b` give a
  [homeomorphism](VectorBundles/Topology/Maps/FiberwiseSplitting.lean)
  from `{z : T × A // ρ (p z.1) z.2 = 0}` to `B × A` when their two total maps
  are continuous. Its coordinates are `(p t, β (p t) ⟨t,rfl⟩ + v)`; its inverse
  uses the given retraction and residual `a - β b (ρ b a)`. Continuity into the
  original subspace is equivalent to continuity of the base and sum coordinates.
  No continuity of fibre operations or scalar topology is required. Given
  semiring-linear maps specialize this scalar-free construction by forgetting
  linearity, retaining their original scalar actions.

- **Prescribed finite-dimensional projection families.** Over a nontrivially normed
  field `K`, let the original finite-dimensional normed ambient `A` have its
  module topology (`[IsModuleTopology K A]`). Linear encoders and retractions
  between the equality fibres of `p : T → B` and `A`, with `ρ b (β b u) = u`,
  yield an
  [operator-norm-continuous family of idempotents](VectorBundles/Topology/Maps/FiberwiseProjection.lean)
  acting by `β b (ρ b a)` when the two exact total maps are continuous.
  The complete-field frontend obtains this module topology locally from finite
  dimensionality; the core construction needs no scalar completeness.
  The existing complementary continuous-map expression acts by
  `a - β b (ρ b a)`, lies in the retraction kernel and vanishes on encoded
  vectors; it gives the image–kernel decomposition of every ambient vector.
  No fibre norm or continuity of fibre operations, ambient completeness,
  nontriviality of `A`, or separation of the base is assumed. Neither
  orthogonality nor commutation at different parameters is asserted; the
  ambient norm stays unchanged, including the standard sup norm for finite Pi.

- **Joint evaluation of algebraic semilinear families.** For possibly noncommutative
  semirings `R,S`, a ring homomorphism `σ : R →+* S` and a finite `R`-basis of the source,
  assume that its scalar coordinates composed with `σ` are continuous. Joint continuity
  of a family of `σ`-semilinear maps is then equivalent to continuity at each basis vector.
  Only `S`, the source, target and parameter carry topologies; the target needs continuous
  addition and jointly continuous `S`-scalar multiplication. No continuity of source
  operations or of `σ` is assumed. The linear criterion is the identity specialization.
  Over a complete nontrivially normed field, a finite-dimensional Hausdorff topological
  source module needs no explicit basis data: joint continuity is equivalent to continuity
  at every fixed vector. For continuous linear maps between normed spaces this also agrees
  with continuity into the operator space. See
  [JointEvaluation](VectorBundles/Analysis/Normed/Module/JointEvaluation.lean).

- **Total-space continuity of semilinear maps from finite local bases.**
  Let `p : T → X` be continuous, with given `R`-module structures and subspace
  topologies on its equality-subtype fibres, and let `σ : R →+* S` be a homomorphism
  of semirings, with a topology on `S`. Coordinate models with finite bases may vary
  over an arbitrary open cover. If their scalar basis coordinates composed with `σ`
  and exact inverse vector coordinates are continuous, parameter-continuity of the
  images of the basis vectors gives continuity of the total semilinear fibre map
  into any `S`-module with continuous addition and scalar multiplication. No topology
  on `R`, continuity of `σ`, continuous operations on the models or fibres,
  injectivity, forward-realization continuity, norm, completeness or separation is
  required. See
  [`LinearMap.continuous_total_of_local_coordinates_of_basis_semilinear`](VectorBundles/Topology/Module/LocalCoordinates.lean).
  The linear criterion
  [`LinearMap.continuous_total_of_local_coordinates_of_basis`](VectorBundles/Topology/Module/LocalCoordinates.lean)
  is the identity-hom specialization.
  Over a complete nontrivially normed field, finite-dimensional Hausdorff
  topological coordinate models supply the bases and scalar-coordinate continuity;
  fixed-vector frame continuity gives the corollary
  [`LinearMap.continuous_total_of_local_coordinates`](VectorBundles/Topology/Module/LocalCoordinates.lean).

- **Module topologies on retracts and finite-basis coordinates.** Over a semiring with
  a given scalar topology, a continuous linear retract of a module with the module
  topology inherits that topology, even when the continuous section is nonlinear.
  In particular, the range of an algebraic idempotent of such a module has its
  module topology as the inherited subspace topology. Over a topological semiring,
  a supplied finite basis of a module with the module topology gives a continuous
  linear equivalence with the standard finite scalar product;
  neither a field, a norm, completeness nor separation is required. See
  [module-topology descent](VectorBundles/Topology/Module/ModuleTopology.lean) and
  [finite-basis coordinates](VectorBundles/Topology/Module/Basis.lean).
  The [complete-field comparison](VectorBundles/Topology/Module/Basis/FiniteDimensional.lean)
  agrees exactly with Mathlib's `Module.Basis.equivFunL` without assuming a source norm.

- **Local constancy of fibre finrank.** Over a division ring, given pointwise
  [linear equivalences to fixed models](VectorBundles/Topology/Module/Finrank.lean)
  on sets whose interiors cover the base make natural-number fibre finrank locally
  constant. Neither finite-dimensionality nor topology on the modules is assumed.
  Infinite-dimensional modules have finrank zero; this is not a claim about their
  cardinal dimension.

- **Closed fiber embeddings.** For continuous `p : T → X`, give its equality-subtype fibers
  their subspace topologies and `RCLike` module structures. An arbitrary open cover with
  finite-dimensional normed linear coordinates, jointly continuous realizations and continuous
  exact inverse-coordinate maps on the total-space restrictions gives a [closed embedding into `X × A`](VectorBundles/Analysis/InnerProductSpace/FiberEmbedding.lean)
  from supplied injective algebraic fiber maps whose local frames are parameter-continuous at
  each fixed vector. The normed inner-product target need not be complete; local ranks may vary.
  The inverse extends to a jointly continuous fiberwise linear retraction on the product.

- **Finite Euclidean embeddings from weighted local coordinates.**
  For a continuous map `p : T → X` over `K = ℝ` or `ℂ`, finitely many normed
  finite-dimensional local models for the original equality-subtype fibre
  modules give a closed embedding `T → X × E` into a finite Euclidean product.
  The supplied domains need not be open: their forward realizations and exact
  inverse coordinates are continuous on the given subspaces, and the continuous
  scalar weights have no common zero and closed cozero supports contained in
  their specified domains. The nonzero-weight sets provide an open cover. The second
  coordinate is the weighted coordinate map followed by the inverse of a linear
  equivalence from `E` to the full product of models. That product keeps its
  supremum norm; no isometry is asserted. The inverse on the image extends to a
  jointly continuous fibrewise linear retraction on all of `X × E`, preserving
  the given fibre operations and inherited topologies. No positivity,
  normalization, or separation of `X` is required. See
  [`exists_retraction_isClosedEmbedding_of_weighted_local_coordinates`](VectorBundles/Analysis/InnerProductSpace/WeightedFiberEmbedding.lean).

- **Retractions and projection continuity.** Over real or complex scalars, original fibers
  with [inducing realizations](VectorBundles/Analysis/InnerProductSpace/InducingRetraction.lean),
  jointly continuous local realizations on an open cover, finite-dimensional seminormed coordinate models
  and injective algebraic fiber maps into a normed inner-product space with fixed-vector-continuous local frames admit continuous-linear
  retractions, jointly continuous realizations and operator-norm-continuous orthogonal projections.
  No fiber norms or ambient completeness are needed. Separately, a given self-adjoint idempotent
  family is [continuous](VectorBundles/Analysis/InnerProductSpace/ProjectionContinuity.lean) if its
  images have local injective finite-dimensional algebraic frames with fixed-vector continuity;
  those frame domains need no topology.

- **Metrics and finite complements.** A finite-dimensional real or complex bundle over a
  paracompact Hausdorff base admits a continuous positive-definite [Hermitian metric](VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  inducing its original fiber topologies. Over a compact normal base, a finite-dimensional
  `RCLike` bundle has a [finite-dimensional complement](VectorBundles/Topology/VectorBundle/FiniteComplement.lean)
  whose product is linearly trivial, not necessarily a complement to a prescribed embedding.

- **Orthogonal splitting.** For a supplied continuous Hermitian metric, an intrinsic submodule
  bundle with embedded total-space inclusion and a finite-dimensional `RCLike` ambient model,
  [orthogonal addition](VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean) is a homeomorphism
  with continuous projections, over any base. [Comparison](VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean)
  identifies complements for two supplied metrics with their induced topologies; no metric is constructed.

<a id="given-adjoint-partners"></a>

- **Given adjoint partners.** For `RCLike` inner products, a supplied partner `S : A → H`
  [bundles linearly](VectorBundles/Analysis/InnerProductSpace/AdjointPair.lean) when `H` is normed and
  `A` seminormed; a pointwise norm bound on the first map makes it continuous-linear. A continuous-linear
  first map supplies the bound, without completeness. The catalogue also gives the algebraic
  semiring-valued pairing result; the partner is supplied, not constructed.

<a id="joint-continuity-of-given-adjoint-partners"></a>
<a id="complete-domain-adjoints-and-composition"></a>
<a id="continuous-inverse-gram-families"></a>

- **Adjoints and Gram families.** A continuous linear map from a complete normed `RCLike`
  inner-product space to a seminormed one has an [adjoint](VectorBundles/Analysis/InnerProductSpace/Adjoint.lean).
  For given raw adjoint partners between seminormed spaces, operator-norm continuity of the forward
  family gives [joint continuity](VectorBundles/Analysis/InnerProductSpace/AdjointPairFamily.lean) of the partners.
  On a finite-dimensional normed domain with normed ambient space, injective forward operators and
  given continuous-linear adjoint partners have [continuous inverse Gram composites](VectorBundles/Analysis/InnerProductSpace/GramRetraction.lean)
  when the forward family is operator-norm continuous. On a complete finite-dimensional normed
  inner-product domain, a jointly continuous injective family instead [constructs canonical adjoints,
  left inverses and projections](VectorBundles/Analysis/InnerProductSpace/GramFamily.lean) continuously.
  None of these results requires completeness of the ambient space.

<a id="norms-of-idempotents"></a>
<a id="images-and-orthogonal-kernels"></a>

- **Algebraic orthogonal retractions and distance.** An injective linear map from a plain module into
  a normed `RCLike` inner-product space has an [algebraic retraction](VectorBundles/Analysis/InnerProductSpace/Projection/LinearMap.lean)
  when its range has orthogonal projection; finite dimension of the module suffices. Given the
  orthogonal-retraction laws, [best-approximation and squared-error formulas](VectorBundles/Analysis/InnerProductSpace/Projection/Distance.lean)
  hold without completeness or a topology on the coefficient module. In a seminormed ambient space,
  zero residual norm detects range closure; in a normed one, `β.range = r.kerᗮ` and minimizers are unique.
  The catalogue also gives the [nonzero-idempotent norm bound](VectorBundles/Analysis/Normed/Ring/Idempotent.lean).

- **Finite orthogonal idempotent families.** Over any semiring and finite index type, the
  [matched-product sum](VectorBundles/Algebra/Ring/OrthogonalIdempotents.lean) intertwines two orthogonal
  idempotent families. If it is a unit, that same unit simultaneously conjugates them and forces both
  families to sum to one; completeness of the families is a conclusion, not a hypothesis.

- **Close idempotents and rank stability.** On a normed space over a nontrivially normed field,
  [idempotents at operator-norm distance less than one](VectorBundles/Analysis/Normed/Operator/Idempotent.lean)
  have equal cardinal ranks of ranges and kernels; these ranks are locally constant in continuous
  families, without completeness. When geometric series are summable in the endomorphism ring
  (in particular for a complete space), one normalized unit gives continuous-linear equivalences of both.

- **Fixed-kernel coordinates.** For seminormed spaces over a nontrivially normed field, a family
  `Γ d : H →L[K] A` with supplied algebraic retractions `r d` has [product coordinates for its total kernel](VectorBundles/Analysis/Normed/Operator/KernelFamilyCoordinates.lean)
  on any topological parameter domain where `q₀ ∘ Γ d` is a unit. Here `q₀` is fixed and continuous-linear;
  joint continuity of the difference between the original and normalized ambient projections suffices.
  No separate continuity of `r` or completeness is needed. The [catalogue](docs/HeadlineResults.md#fixed-kernel-coordinates-on-unit-domains)
  gives the formulas, unit-subtype version and distinction between a unit comparison and a retraction.

- **Linear families and bundle inverses.** Over a field with a T₁ topology making it a topological
  ring, pointwise-continuous algebraic linear families have an [open surjectivity locus](VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  for a finite-dimensional target with its module topology; the source needs no topology. Over a
  nontrivially normed field, continuous-forward fiberwise linear equivalences give [bundle homeomorphisms](VectorBundles/Topology/VectorBundle/Isomorphism.lean)
  when the source normed model is finite-dimensional and the target normed model has its module topology.

<a id="finite-ambient-open-grids-for-compact-products"></a>
<a id="finite-subdivisions-of-closed-real-intervals"></a>

- **Compact refinements and partitions of unity.** An ambient open cover of two compact subsets'
  product admits [finite ambient open grids](VectorBundles/Topology/Compactness/Product.lean) with each
  full rectangle in a chosen cover member, without separation assumptions. [Closed-interval subdivisions](VectorBundles/Topology/UnitInterval.lean)
  allow repeated cuts and singleton intervals. A finite open cover of a normal space admits [continuous
  weights](VectorBundles/Topology/ContinuousMap/FiniteWeights.lean) in `[0,1]` summing to one, with closed
  cozero supports subordinate to the cover; no T₁ hypothesis is needed.
  On a [closed subset of a normal space](VectorBundles/Topology/FiniteNormalWeights.lean),
  a finite open cover similarly admits nonnegative continuous weights with closed
  supports in its members, sum at most one everywhere and exactly one on that subset.

<a id="finite-product-chart-selection"></a>

- **Finite selection from supplied product charts.** For compact `X`, arbitrary topological `Y`
  and chosen `y₀`, supplied whole-product charts with both base laws and agreement in both directions
  with specified original charts at `y₀` admit a [finite ordered open cover](VectorBundles/Topology/FiberBundle/FiniteCylinderCover.lean).
  This retains varying models and, when provided, matching linear coordinates over any semiring. It selects supplied
  charts, not charts from an arbitrary atlas over `Y`, and needs neither compactness of `Y` nor projection continuity.

- **Heterogeneous cylinder gluing.** For a continuous projection over `X × T`, with `T` linearly
  ordered and topological with closed upper and lower rays, supplied base-preserving charts on the
  closed half-cylinders may have different models. The [gluer](VectorBundles/Topology/FiberBundle/ClosedCylinder.lean)
  gives a whole-cylinder homeomorphism into the left model, retaining its entire left chart.

- **Whole-cylinder charts and transport.** An open base-preserving atlas for a continuous projection
  over `X × unitInterval` gives [local whole-interval charts](VectorBundles/Topology/FiberBundle/ClosedCylinderSubdivisionData.lean),
  with linear coordinates when the input coordinates are linear, over any semiring. Separately, finite ordered whole-cylinder charts with continuous
  weights in `[0,1]` summing to one and closed cozero supports inside the chart base sets give [base-preserving,
  bottom-fixing transport](VectorBundles/Topology/FiberBundle/FiniteTransport/Projection.lean) from the standard pullback
  of the entire zero slice. A [finite open cylinder cover on a normal base](VectorBundles/Topology/FiberBundle/FiniteTransport/Existence.lean)
  supplies the weights. Models may vary; full homotopy invariance is not asserted.

- **Varying-rank atlases.** Over a field with a given topology, a supplied [finite-rank linear atlas](VectorBundles/Topology/VectorBundle/FiniteRank.lean)
  allows unbounded, locally varying ranks, including zero, on the original fibers and total space. Its
  [projection is continuous, open and quotient](VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean),
  and its zero section is an embedding. Further separation and countability results use the corresponding
  base and exact chart-coordinate hypotheses, not continuous scalar operations or a global fixed model.

- **Sharp projection criteria.** A fiber-bundle projection is an [open embedding](VectorBundles/Topology/FiberBundle/Projection.lean)
  exactly when every original fiber is subsingleton, and [proper](VectorBundles/Topology/FiberBundle/Proper.lean)
  exactly when each fiber is compact. Its total space is [second-countable](VectorBundles/Topology/FiberBundle/Countability.lean)
  exactly when the base or model is empty, or both are second-countable, without separation hypotheses.
  Further compactness, separability and Lindelöf criteria are in the [detailed guide](docs/Results.md#topological-properties-of-bundle-total-spaces).

## Using the library

Add the released library to your `lakefile.toml`:

```toml
[[require]]
name = "vector-bundles"
git = "https://github.com/FormalFrontier/vector-bundles.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake keeps the resolved commit in
`lake-manifest.json` until you update it; use a full release commit instead of
`main` to pin a specific version.

Import the production root or a narrower module:

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

For total-space continuity and its finite-dimensional corollary, import
`VectorBundles.Topology.Module.LocalCoordinates` directly.
For the closed-embedding criterion, import the leaf module
`VectorBundles.Analysis.InnerProductSpace.FiberEmbedding` directly.
The normal-space cutoff and closed-subset weight results require
`VectorBundles.Topology.FiniteNormalWeights`; local constancy of finrank requires
`VectorBundles.Topology.Module.Finrank`. These are also direct imports rather
than re-exports of `VectorBundles`.

The raw product model has its sup norm, which is not an inner-product norm.
`import VectorBundlesTest` also imports the standard and boundary examples.

## Building

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`. The direct dependencies are
[Mathlib](https://github.com/leanprover-community/mathlib4) at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`,
[Metrization](https://github.com/FormalFrontier/metrization) at
`4dcc0f6f903ba4d0c66f230d21f7ac4c31d4ea57`, and
[ProjectiveModules](https://github.com/FormalFrontier/projective-modules) at
`77a601ffd885a18a7c0fd90e311b7f530ac4762b`.
Both deliverables use the Mathlib revision listed above. Their transitive
dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes both `VectorBundles` and `VectorBundlesTest`.

## Contents

Paths below are relative to `VectorBundles/`. Full fiber- and vector-bundle
examples are collected by `VectorBundlesTest.lean`; the [import guide](docs/Results.md#adjoint-partners-gram-operators-and-imports)
identifies analysis modules and examples requiring direct imports.

| Module | Contents |
| --- | --- |
| [`LinearAlgebra.WeightedCoordinates`](VectorBundles/LinearAlgebra/WeightedCoordinates.lean) | Supported weighted maps into the full dependent product; unit-ideal spanning and unit-coordinate injectivity |
| [`Topology.Maps.WeightedCoordinates`](VectorBundles/Topology/Maps/WeightedCoordinates.lean) | Continuity on original equality fibres with closed cozero supports |
| [`Topology.Maps.FiberwiseSplitting`](VectorBundles/Topology/Maps/FiberwiseSplitting.lean) | Additive sum–kernel homeomorphism on the original subspace, with a base-and-sum continuity criterion |
| [`Topology.Maps.FiberwiseProjection`](VectorBundles/Topology/Maps/FiberwiseProjection.lean) | Prescribed operator-norm-continuous idempotent families on an arbitrary finite-dimensional ambient space, with complementary kernel and decomposition laws |
| [`Topology.FiniteNormalWeights`](VectorBundles/Topology/FiniteNormalWeights.lean) | Normal-space cutoffs, closed-subset weights and finite partition-of-unity components |
| [`Topology.Module.Finrank`](VectorBundles/Topology/Module/Finrank.lean) | Locally constant fibre finrank from a neighbourhood cover of linear models |
| [`VectorBundles.Algebra.Ring.CommutingIdempotent`](VectorBundles/Algebra/Ring/CommutingIdempotent.lean) | Cubic identities for commuting idempotents in nonunital rings |
| [`VectorBundles.Algebra.Ring.Idempotent`](VectorBundles/Algebra/Ring/Idempotent.lean) | Normalized intertwiners and prescribed conjugacy |
| [`VectorBundles.Algebra.Ring.OrthogonalIdempotents`](VectorBundles/Algebra/Ring/OrthogonalIdempotents.lean) | Matched-product sums and unit conjugacy of finite orthogonal families |
| [`VectorBundles.Analysis.InnerProductSpace.FiberEmbedding`](VectorBundles/Analysis/InnerProductSpace/FiberEmbedding.lean) | Closed embeddings from normed local coordinates on original fibers |
| [`VectorBundles.Analysis.InnerProductSpace.GramFamily`](VectorBundles/Analysis/InnerProductSpace/GramFamily.lean) | Canonical fixed-domain adjoint, inverse Gram and projection families |
| [`VectorBundles.Analysis.InnerProductSpace.InducingRetraction`](VectorBundles/Analysis/InnerProductSpace/InducingRetraction.lean) | Continuous retractions from inducing realizations and local finite frames |
| [`VectorBundles.Analysis.InnerProductSpace.ProjectionContinuity`](VectorBundles/Analysis/InnerProductSpace/ProjectionContinuity.lean) | Continuity of given projections from local algebraic frames |
| [`VectorBundles.Analysis.Normed.Operator.Idempotent`](VectorBundles/Analysis/Normed/Operator/Idempotent.lean) | Range and kernel transport and cardinal-rank stability |
| [`VectorBundles.Analysis.Normed.Operator.KernelFamilyCoordinates`](VectorBundles/Analysis/Normed/Operator/KernelFamilyCoordinates.lean) | Fixed-kernel product coordinates on unit domains |
| [`VectorBundles.Analysis.Normed.Ring.CommutingIdempotent`](VectorBundles/Analysis/Normed/Ring/CommutingIdempotent.lean) | Seminorm gaps and rigidity of close commuting idempotents |
| [`VectorBundles.Analysis.Normed.Ring.CommutingIdempotent.Topology`](VectorBundles/Analysis/Normed/Ring/CommutingIdempotent/Topology.lean) | Local constancy from eventual nearby commutation |
| [`LinearAlgebra.Pairing.Adjoint`](VectorBundles/LinearAlgebra/Pairing/Adjoint.lean) | Raw adjoint relations and linear bundling from right-linear pairings with separating columns |
| [`Analysis.InnerProductSpace.AdjointPair`](VectorBundles/Analysis/InnerProductSpace/AdjointPair.lean) | Given inner-product adjoint partners, norm bounds and exact linear/continuous-linear bundling |
| [`Analysis.InnerProductSpace.AdjointPairFamily`](VectorBundles/Analysis/InnerProductSpace/AdjointPairFamily.lean) | Joint continuity of raw partner evaluations from forward operator-norm continuity |
| [`Analysis.InnerProductSpace.Adjoint`](VectorBundles/Analysis/InnerProductSpace/Adjoint.lean) | Complete-domain adjoint construction and composition laws |
| [`Analysis.InnerProductSpace.GramRetraction`](VectorBundles/Analysis/InnerProductSpace/GramRetraction.lean) | Supplied-unit normalization, pairing and kernel laws, finite-dimensional adjoint retractions and continuity |
| [`Analysis.Normed.Operator.UnitGramContinuity`](VectorBundles/Analysis/Normed/Operator/UnitGramContinuity.lean) | Normalizer and ambient-projection continuity along eventually unit Grams, without completeness |
| [`Analysis.Normed.Ring.UnitContinuity`](VectorBundles/Analysis/Normed/Ring/UnitContinuity.lean) | Inversion within the unit locus of a seminormed ring and along eventual units |
| [`Analysis.InnerProductSpace.Projection.Distance`](VectorBundles/Analysis/InnerProductSpace/Projection/Distance.lean) | Distance, projected-image contraction and image/orthogonal-kernel laws for supplied retractions |
| [`Analysis.InnerProductSpace.PositiveForm`](VectorBundles/Analysis/InnerProductSpace/PositiveForm.lean) | Bounded positive-form unit sublevels in the original topology |
| [`Analysis.InnerProductSpace.Projection.LinearMap`](VectorBundles/Analysis/InnerProductSpace/Projection/LinearMap.lean) | Projection/preimage retractions onto injective images of plain modules, with a finite-dimensional specialization |
| [`Analysis.InnerProductSpace.Projection.Fiberwise`](VectorBundles/Analysis/InnerProductSpace/Projection/Fiberwise.lean) | Algebraic total-space retractions on given projection fibres, with projection and left-inverse laws |
| [`Analysis.Normed.Module.JointEvaluation`](VectorBundles/Analysis/Normed/Module/JointEvaluation.lean) | Joint evaluation from continuous finite-basis coordinates over semirings; finite-dimensional topological-module criterion and operator-space comparison |
| [`Topology.Module.LocalCoordinates`](VectorBundles/Topology/Module/LocalCoordinates.lean) | Total-space continuity of semilinear maps from finite local bases over semirings; linear and finite-dimensional topological-module corollaries |
| [`Analysis.InnerProductSpace.FiberEmbedding`](VectorBundles/Analysis/InnerProductSpace/FiberEmbedding.lean) | Closed fibre embeddings and extending retractions under normed inner-product hypotheses; reexports the local-coordinate continuity criteria |
| [`Analysis.Normed.Ring.Units`](VectorBundles/Analysis/Normed/Ring/Units.lean) | Value embedding for units of a seminormed ring |
| [`Topology.Algebra.GroupWithZero`](VectorBundles/Topology/Algebra/GroupWithZero.lean) | Continuity of reciprocal selected finite sums of real squares under pointwise nonzero coverage |
| [`Topology.ContinuousMap.FiniteWeights`](VectorBundles/Topology/ContinuousMap/FiniteWeights.lean) | Finite partitions of unity on normal spaces, with all-index closed-cozero subordination and no further separation assumptions |
| [`Topology.Algebra.Module.FiniteDimensionalOperator`](VectorBundles/Topology/Algebra/Module/FiniteDimensionalOperator.lean) | Pointwise versus bounded-convergence operator criteria |
| [`Topology.Bornology.Inducing`](VectorBundles/Topology/Bornology/Inducing.lean) | `IsVonNBounded.preimage_of_isInducing` over a general `NormedDivisionRing`, without injectivity or topological vector-space hypotheses |
| [`Topology.Compactness.CountablyCompact`](VectorBundles/Topology/Compactness/CountablyCompact.lean) | Countably compact preimages under proper maps exactly when the target subset intersected with the range is countably compact |
| [`Topology.Compactness.Lindelof`](VectorBundles/Topology/Compactness/Lindelof.lean) | Lindelöf inverse images under proper maps and products with compact or σ-compact sets, without separation assumptions |
| [`Topology.Compactness.SigmaCompact`](VectorBundles/Topology/Compactness/SigmaCompact.lean) | Sigma-compact inverse images under proper maps exactly when the target subset intersected with the range is sigma-compact |
| [`Topology.Compactness.Paracompact`](VectorBundles/Topology/Compactness/Paracompact.lean) | Paracompactness of continuous retracts and domains of proper maps; open-surjective-proper codomain theorem |
| [`Topology.Compactness.Product`](VectorBundles/Topology/Compactness/Product.lean) | Finite ambient open covers of two compact subsets with every full pairwise product contained in an original open-cover member, without separation assumptions |
| [`Topology.UnitInterval`](VectorBundles/Topology/UnitInterval.lean) | Positive finite monotone subdivisions subordinate to open interval covers; common-neighbourhood subdivisions and compact-base closed-slab refinements |
| [`Topology.LocallyFinite`](VectorBundles/Topology/LocallyFinite.lean) | Locally finite images under closed maps with compact point fibers; [infinite-index example](VectorBundlesTest/Topology/LocallyFinite.lean) |
| [`Topology.CompactOpen`](VectorBundles/Topology/CompactOpen.lean) | Locally constant compact-open images for jointly continuous homeomorphism families and their inverses |
| [`Topology.FiberBundle.CoordChange`](VectorBundles/Topology/FiberBundle/CoordChange.lean) | Jointly continuous coordinate-change homeomorphisms and inverses on the original chart overlap |
| [`Topology.Maps.Proper`](VectorBundles/Topology/Maps/Proper.lean) | Proper first projection for compact-valued upper hemicontinuous correspondences, without separation or ambient closedness |
| [`Topology.Connected.Basic`](VectorBundles/Topology/Connected/Basic.lean) | Preconnected preimages under open maps with preconnected fibers over a preconnected subset of the range |
| [`Topology.FiberBundle.Connected`](VectorBundles/Topology/FiberBundle/Connected.lean) | Preconnected projection preimages and preconnected/connected total spaces; [real and empty-model examples](VectorBundlesTest/Topology/FiberBundle/Connected.lean) |
| [`Topology.Separable.Basic`](VectorBundles/Topology/Separable/Basic.lean) | Ambient-separable preimages under open maps with all ambient fibers separable; arbitrary-set preimage equivalence for open quotient maps; separable domains for separable targets |
| [`Topology.ShrinkingLemma`](VectorBundles/Topology/ShrinkingLemma.lean) | Open and nested shrinkings supported on a finite subset of an arbitrary index type in a normal space, without T1 |
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
| [`Topology.VectorBundle.Hom`](VectorBundles/Topology/VectorBundle/Hom.lean) | Identity and composition of continuous Hom sections, with the model operator-norm topology |
| [`Topology.VectorBundle.ScalarEnd`](VectorBundles/Topology/VectorBundle/ScalarEnd.lean) | Base-preserving product homeomorphism for the endomorphism bundle of a line, with the original fiber topologies |
| [`Topology.VectorBundle.SemilinearEvaluation`](VectorBundles/Topology/VectorBundle/SemilinearEvaluation.lean) | One- and two-argument evaluation on Mathlib's Hom topology |
| [`Topology.VectorBundle.WeightedForm`](VectorBundles/Topology/VectorBundle/WeightedForm.lean) | Supported weighted forms in linear charts |
| [`Topology.ContinuousMap.PairingExtension`](VectorBundles/Topology/ContinuousMap/PairingExtension.lean) | Constant extensions of pairings on arbitrary subsets |
| [`Topology.ContinuousMap.WeightedExtension`](VectorBundles/Topology/ContinuousMap/WeightedExtension.lean) | Zero extensions of continuously weighted maps |
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
| [`Topology.FiberBundle.SupportedTransport`](VectorBundles/Topology/FiberBundle/SupportedTransport.lean) | Pullback transport localized to one chart by a closed subset, with independent original dummy and chart model; given linear coordinates make each fiber map linear over an arbitrary semiring |
| [`Topology.FiberBundle.FiniteTransport`](VectorBundles/Topology/FiberBundle/FiniteTransport.lean) | Weighted finite ordered cylinder transport on a given family, with prefix laws, independent endpoint transport and linearity from given coordinates over any semiring |
| [`Topology.FiberBundle.FiniteTransport.Projection`](VectorBundles/Topology/FiberBundle/FiniteTransport/Projection.lean) | Transport from the standard pullback of the entire original zero restriction to the same given projection space, with ordered chart-lift characterization, both base and bottom laws, original-fiber linearity and independent full-slice endpoints |
| [`Topology.FiberBundle.FiniteTransport.Existence`](VectorBundles/Topology/FiberBundle/FiniteTransport/Existence.lean) | Finite open cylinder-chart covers of normal spaces supply weights for family transport; with original-fiber modules and matching linear coordinates, the projection theorem returns the same weighted constructor, linearity and endpoint comparison |
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
projective-section theorem is provided here. Finite cylinder transport assumes a
finite ordered family of whole-interval charts. It does not assert independence
from weights or chart order, or the full statement of Hatcher's Proposition 1.7.
The units embedding does not assert that the unit locus is open. The separate
inverse-continuity API works within that locus or under supplied eventual-unit
hypotheses, not on an automatically available ambient neighborhood. The finite-operator
criterion requires the source's module topology, which cannot simply be dropped
over an incomplete field.

## References

- Allen Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html),
  version 2.2 (November 2017), §1.1: Lemma 1.1, Proposition 1.2 and its Hermitian
  remark, the supplied-metric geometric ingredients of Proposition 1.3,
  finite complements in Proposition 1.4, pullbacks in Proposition 1.5, and
  the two preliminary cylinder facts used in Proposition 1.7.
- Finite normal shrinking and Urysohn's lemma give the finite partitions of unity.
  The latter uses Yury Kudryashov's
  [Mathlib formalization](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/UrysohnsLemma.lean).
  Hatcher's version 2.2, printed p. 20 (PDF p. 24), motivates this finite-cover formulation.
- Hatcher's Proposition 1.7 is a motivating comparison problem for finite cylinder
  transport. The results here assume finitely many ordered cylinder charts,
  allow arbitrary semirings and varying chart models, and do not assert the full
  proposition.
- Mathlib's [bundle geometry](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/VectorBundle),
  module topology, bounded-convergence operator topology, inner products,
  submodule-valued orthogonal projections, inherited finite-dimensional completeness,
  orthogonal complements, partitions of unity and continuous functional calculus.
  Individual modules identify the particular APIs and contributors followed.

- ProjectiveModules' `ContinuousLinearMap.equivProdKerOfRightInverse` provides the
  pointwise continuous-linear splitting used for additive sum–kernel coordinates.
  Mathlib's injective commutativity transport and canonical natural-number modules
  give its scalar-free application here.
- The prescribed projection family composes the two total maps to obtain joint
  continuity. Fixed-base slices give continuous linear maps, and
  `Module.Basis.continuous_clm_apply_iff` yields continuity in the original
  operator norm. Its complete-field frontend uses Mathlib's
  `isModuleTopologyOfFiniteDimensional` locally.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed to the formalization and
its documentation. The mathematics draws on Hatcher and Mathlib; prior formalizations,
contributors and authentic notices are acknowledged in [Credits](CREDITS.md) and
individual modules. Licensed under Apache-2.0; see [LICENSE](LICENSE).

## Finite normal covers and Euclidean coordinates

`ContinuousLinearMap.exists_retraction_isClosedEmbedding_of_finite_normal_cover`
in `VectorBundles.Analysis.InnerProductSpace.WeightedFiberEmbedding` constructs
supported continuous real weights and a closed embedding of a total space into
a product of its base with Euclidean space. It assumes a normal base, a finite
family of normed finite-dimensional local models, and arbitrary chart domains
whose interiors cover the base. The given projection, chart realizations and
inverse vector coordinates must be continuous. No inner product on the given
models, T1 or compact base, nonempty index type, or positive rank is required.

The equality-subtype fibres keep their given module structures and inherited
topologies. The inverse extends to a jointly continuous fibrewise linear
retraction on the whole product. The Euclidean dimension is exactly the finrank
of the full product of local models; its linear equivalence with that auxiliary
supremum-norm product is not asserted to be isometric. The construction reuses
the finite real weights and the supplied-weight embedding theorem.


## Finite-coordinate operator spaces

`VectorBundles.Topology.Module.FiniteCoordinates` identifies continuous linear maps from a
finite scalar product with their columns:

```text
((ι → K) →L[K] F) ≃L[K] (ι → F).
```

Here `K` is a nontrivially normed field and `F` is a topological additive group with a
continuous `K`-module structure. The scalar field need not be complete, and the target need
not be normed, separated, complete, or finite dimensional. The construction uses the given
product and bounded-convergence topologies; in normed spaces this is the operator-norm
topology with the given norms and scalar actions.

A supplied continuous linear coordinate equivalence gives finite-evaluation criteria for
continuity, continuity at a point, and continuity on or within a set. For a finite basis whose
given topology satisfies `IsModuleTopology`, the existing basis coordinate equivalence
supplies these data. The parameter space is an arbitrary topological space, with no required algebraic
structure. Joint continuity reuses the finite-basis semilinear evaluation criterion.

`VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional` compares the scalar-source
equivalence with Mathlib's complete-field `ContinuousLinearEquiv.piRing` at the same field,
target, and index type. These supplied-coordinate and module-topology hypotheses are
sufficient inputs, not a necessity assertion for every normed finite-dimensional operator
criterion.
