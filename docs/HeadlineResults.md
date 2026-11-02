# Result catalogue

[Overview](../README.md#headline-results) · [Using the library](../README.md#using-the-library) ·
[Detailed results and examples](Results.md) · [Credits](../CREDITS.md)

The sections below give the individual statements and hypotheses behind the
overview. The [detailed results guide](Results.md) adds examples and further
bundle-topology results, distinguishing these constructions from Mathlib APIs.

## Topics

- [Closed embeddings from normed local coordinates](#closed-embeddings-from-normed-local-coordinates)
- [Retractions from inducing realizations and local finite frames](#retractions-from-inducing-realizations-and-local-finite-frames)
- [Continuity from local finite frames](#continuity-from-local-finite-frames)
- [Joint continuity of given adjoint partners](#joint-continuity-of-given-adjoint-partners)
- [Given adjoint partners](#given-adjoint-partners)
- [Images and orthogonal kernels](#images-and-orthogonal-kernels)
- [Complete-domain adjoints and composition](#complete-domain-adjoints-and-composition)
- [Continuous inverse Gram families](#continuous-inverse-gram-families)
- [Canonical Gram families on a fixed domain](#canonical-gram-families-on-a-fixed-domain)
- [Continuity along supplied units](#continuity-along-supplied-units)
- [Fixed-kernel coordinates on unit domains](#fixed-kernel-coordinates-on-unit-domains)
- [Norms of idempotents](#norms-of-idempotents)
- [Finite orthogonal idempotent families](#finite-orthogonal-idempotent-families)
- [Close idempotent operators](#close-idempotent-operators)
- [Finite ambient open grids for compact products](#finite-ambient-open-grids-for-compact-products)
- [Finite subdivisions of closed real intervals](#finite-subdivisions-of-closed-real-intervals)
- [Finite product-chart selection](#finite-product-chart-selection)
- [Algebraic retractions and distance](#algebraic-retractions-and-distance)
- [Supported weighted coordinates](#supported-weighted-coordinates)
- [Local constancy of fibre finrank](#local-constancy-of-fibre-finrank)
- [Supported pairings and partitions of unity](#supported-pairings-and-partitions-of-unity)
- [Cylinder charts and transport](#cylinder-charts-and-transport)
- [Varying-rank atlases](#varying-rank-atlases)
- [Finite cover shrinkings](#finite-cover-shrinkings)
- [Bundle geometry and topological criteria](#bundle-geometry-and-topological-criteria)

## Closed embeddings from normed local coordinates

For a continuous map `p : T → X`, give each equality-subtype fibre its
subspace topology and a module structure over `ℝ` or `ℂ`. An arbitrary open
cover may have normed finite-dimensional coordinate models of varying,
unbounded, or zero rank. If the coordinate realizations and their exact
inverses are continuous, injective algebraic fibre maps into a normed
inner-product space `A`, parameter-continuous at each fixed coordinate
vector, give a closed embedding `T → X × A`. Its inverse extends to a
jointly continuous fibrewise linear retraction on `X × A`. Neither
completeness of `A` nor separation of `X` is required. See
[`exists_retraction_isClosedEmbedding_of_local_coordinates`](../VectorBundles/Analysis/InnerProductSpace/FiberEmbedding.lean).

## Retractions from inducing realizations and local finite frames

Over `ℝ` or `ℂ`, injective algebraic linear maps `βₓ : Fₓ →ₗ[K] A` admit
continuous linear retractions `ρₓ : A →L[K] Fₓ` when the original normless
fibres retain their given topologies induced by realization maps `jₓ`, the
local realizations are jointly continuous, and the raw ambient frames are
parameter-continuous at each fixed vector. The finite-dimensional seminormed
local models `Gᵢ` may vary over an arbitrary open cover; the ambient
inner-product space `A` is normed and need not be complete. The realizations
`(x, a) ↦ jₓ (ρₓ a)` are jointly continuous, and
the self-adjoint idempotents `Pₓ a = βₓ (ρₓ a)` vary continuously in operator
norm. See
[`exists_retraction_of_inducing_local_finite_frames`](../VectorBundles/Analysis/InnerProductSpace/InducingRetraction.lean).

## Continuity from local finite frames

A given family of self-adjoint idempotents is
operator-norm continuous when its images have local injective finite-dimensional
algebraic frames with fixed-vector parameter continuity. The frame domains may vary
and need no norm or topology; the given normed inner-product ambient space need not
be complete. See [ProjectionContinuity](../VectorBundles/Analysis/InnerProductSpace/ProjectionContinuity.lean).

## Joint continuity of given adjoint partners

For given raw adjoint partners `S t` of continuous linear maps `Γ t` between
seminormed inner-product spaces over real or complex scalars,
`norm_sub_apply_le` controls simultaneous variation in the input and forward
operator. If `Γ` varies continuously in operator norm over any topological
parameter space, `continuous_uncurry` gives joint continuity of `(t, a) ↦ S t a`.
Neither space needs completeness or separation, and no linearity or uniqueness
of the partners is assumed.

## Given adjoint partners

Right-linear pairings over a semiring bundle a given adjoint partner as a linear
map when the first pairing's columns separate points, without linearity of the
left-hand map. For inner products, `Function.IsAdjointPair.toLinearMap` applies
to raw maps with a normed target and a seminormed source. A pointwise norm bound
on the first map gives `toContinuousLinearMapOfBound`; the continuous-linear
first-map specialization is `toContinuousLinearMap`. All constructions retain
the given partner exactly, with no completeness assumptions.

For the inner-product specialization, the normed space is the **target of the
partner**: with `Γ : H → A` and `S : A → H`, `H` is normed and `A` may be
seminormed. The [right-linear pairing construction](../VectorBundles/LinearAlgebra/Pairing/Adjoint.lean),
`Function.IsAdjointPair.toLinearMapOfInjective`, needs only semiring modules on
the partner's source, target and pairing values; the left index types are arbitrary.
The [inner-product API](../VectorBundles/Analysis/InnerProductSpace/AdjointPair.lean)
provides the displayed bundling operations, evaluation/coercion equations, uniqueness
and proof-independence laws. For `toContinuousLinearMapOfBound`, the input bound is
`∀ v, ‖Γ v‖ ≤ (C : ℝ) * ‖v‖` with `C : NNReal`; no linearity of `Γ` is assumed.
These operations bundle an already specified `S`; they are not adjoint-existence
results. The complete-domain construction below instead produces a partner from
`Γ`, using completeness of `H` and the Fréchet–Riesz equivalence.

## Images and orthogonal kernels

For given algebraic maps `β : F →ₗ[K] A` and `r : A →ₗ[K] F` that form an orthogonal retraction, `closure (Set.range β)` is the inner-product orthogonal complement of `r.ker` in the original seminormed inner-product space `A`. If `A` is normed, `β.range = r.kerᗮ`. The scalar field is real or complex; `F` needs only its additive group and module structures, and no completeness is assumed. See the [distance and image API](../VectorBundles/Analysis/InnerProductSpace/Projection/Distance.lean).

Here the seminormed statement uses
`LinearMap.IsOrthogonalRetraction.closure_range_eq_orthogonalBilin_ker` and the
given sesquilinear form `innerₛₗ K`; its right-hand side is
`(r.ker.orthogonalBilin (innerₛₗ K) : Set A)`.
The normed specialization is `range_eq_orthogonal_ker`. Neither result supplies
`r` or its orthogonal-retraction witness; the [distance account](#algebraic-retractions-and-distance)
keeps these laws separate from projection/preimage constructions.

## Complete-domain adjoints and composition

For an `RCLike` field `K`, a complete normed inner-product space `H` and a
seminormed inner-product space `A`,
[`ContinuousLinearMap.adjointMap`](../VectorBundles/Analysis/InnerProductSpace/Adjoint.lean)
constructs the adjoint of `H →L[K] A`, without completeness or separation of `A`.
It preserves the identity. For `Γ₁ : H →L[K] M`, `Γ₂ : M →L[K] A` and a raw
adjoint partner `S₂ : A → M`, `adjointMap_comp_apply_of_isAdjointPair` gives
`adjointMap (Γ₂.comp Γ₁) a = adjointMap Γ₁ (S₂ a)`, with no linearity or
continuity assumption on `S₂` and no completeness of the seminormed spaces `M`
and `A`. There is also a bundled-partner equality. When `M` is itself normed
and complete, `adjointMap_comp` expresses this entirely using `adjointMap`.
These laws generalize Mathlib's `ContinuousLinearMap.adjoint_comp`; the existing
`adjointMap_eq_adjoint` bridge identifies the normed complete specialization.

## Continuous inverse Gram families

Over an `RCLike` field `K`, for finite-dimensional normed inner-product `H`,
normed inner-product `A` and
families `Γ b : H →L[K] A`, `S b : A →L[K] H` of adjoint pairs,
[`ContinuousLinearMap.continuous_inverseGramComp`](../VectorBundles/Analysis/InnerProductSpace/GramRetraction.lean)
shows that injectivity of each `Γ b` and continuity of `Γ` alone imply
continuity of `b ↦ inverseGramComp (Γ b) (S b)`.
`continuous_inverseGramComp_apply` gives joint continuity in the parameter and
the ambient vector. Neither theorem requires completeness of `A` or a separate
continuity hypothesis on `S`; the inversion takes place in the endomorphisms of `H`.

For more general normalization, `inverseGramComp Γ S` is the total expression
`(Ring.inverse (S.comp Γ)).comp S`. Over a semiring with the given module
topologies, a supplied unit `S.comp Γ` gives a left inverse of `Γ`, an idempotent
ambient composite and recovery of `S` after applying the Gram map. The normalizer
has the same kernel as `S`. With subtraction on the ambient module, `S` annihilates
the full residual; no continuity of subtraction is required. These facts alone
do not imply orthogonality. Given adjoint pairings give pairing preservation;
explicit star symmetry of the ambient pairing gives self-adjointness, and for
the original seminormed inner products the residual is orthogonal to the image.
In the normed finite-dimensional adjoint setting above, `isUnit_comp_iff`
identifies the Gram-unit condition with injectivity of `Γ`, including zero domains,
and `inverseGramComp_isOrthogonalRetraction` gives the corresponding retraction.

## Canonical Gram families on a fixed domain

For a jointly continuous, pointwise injective family `f x : E →L[K] F`, with
`E` complete and finite-dimensional and both spaces carrying their given normed
inner products over an `RCLike` field,
[`ContinuousLinearMap.gramFamily_properties`](../VectorBundles/Analysis/InnerProductSpace/GramFamily.lean)
gives operator-norm continuity of the characteristic adjoint `g`, the canonical
left inverse `r = (g f)⁻¹ g`, and the ambient projection `P = f r`. Pointwise,
`r f = 1`; `P` is idempotent and self-adjoint, has the same range as `f`, and
has kernel `range(f)ᗮ`. The full residual `w - P w` is orthogonal to the image.
No completeness or finite dimension of `F`, nonempty base, isometry assumption,
or global bound on the inverses is required. This is an independent fixed-domain
analytic result, not a variable-bundle complement theorem or the full statement
of Hatcher's Proposition 1.7.

## Continuity along supplied units

In a seminormed ring, [inverse continuity](../VectorBundles/Analysis/Normed/Ring/UnitContinuity.lean)
holds on the unit locus: `Ring.continuousOn_inverse_units`. More generally,
`Ring.tendsto_inverse_of_eventually_isUnit` takes convergence to a unit and an
eventual-unit hypothesis along the same filter. Supplied units whose forward
values converge have convergent inverse values. These statements require neither
completeness nor separation, and assert neither openness of the unit locus nor
existence of an ambient neighborhood consisting of units.

For seminormed spaces over a nontrivially normed field, the
[unit-Gram family API](../VectorBundles/Analysis/Normed/Operator/UnitGramContinuity.lean)
applies this to given continuous-linear maps `Γ : H →L[K] A` and `S : A →L[K] H`.
Convergence of both operator families, a unit limit Gram and eventual unit Grams
give operator-norm convergence of `inverseGramComp Γ S` and of its ambient
composite `Γ.comp (inverseGramComp Γ S)`. There are `ContinuousWithinAt`,
`ContinuousAt` and global versions; the global versions assume every Gram is a
unit. Neither space needs completeness or separation, and no inner product or
adjoint relation is assumed. Thus this is distinct from the finite-dimensional
adjoint-family theorem above, which derives partner continuity from `Γ`.
The `continuousAt_inverseGramComp` theorem in `GramRetraction` instead assumes
complete normed `H`, continuous `Γ` and `S` at the point, and a unit Gram there;
it obtains an ambient inversion neighborhood without an extra eventual-unit input.

## Fixed-kernel coordinates on unit domains

See [KernelFamilyCoordinates](../VectorBundles/Analysis/Normed/Operator/KernelFamilyCoordinates.lean).

Let `K` be a nontrivially normed field. Both `H` and `A` retain their given
seminormed additive commutative group and `NormedSpace K` structures; neither
norm definiteness nor completeness is required for either space. Let `D` be a
topological parameter space, with `Γ d : H →L[K] A` and supplied linear
retractions `r d : A →ₗ[K] H` satisfying `r d (Γ d h) = h`.

Fix `q0 : A →L[K] H` such that `q0.comp (Γ d)` is a unit in the
continuous-linear endomorphism ring for every `d`. The map `q0` need not
itself retract every `Γ d`: the canonical
`q_d = ContinuousLinearMap.inverseGramComp (Γ d) q0` supplies the normalized
retractions. If the joint difference
`(d, a) ↦ Γ d (r d a) - Γ d (q_d a)` is continuous, then
`ContinuousLinearMap.kerFamilyHomeomorphOfIsUnit` gives

```lean
{p : D × A // r p.1 p.2 = 0} ≃ₜ D × LinearMap.ker q0.toLinearMap
```

with the original product and subtype topologies. No individual continuity
of the supplied `r d` is assumed. The parameter space may be empty. On the
subtype where `q0.comp (Γ b)` is a unit, retraction data are needed only on
that subtype, with no openness assumption or extension outside it.

The public equations
`ContinuousLinearMap.kerFamilyHomeomorphOfIsUnit_apply_snd` and
`ContinuousLinearMap.kerFamilyHomeomorphOfIsUnit_symm_apply_snd` give ambient
coordinates `a - Γ d (q_d a)` and `b - Γ d (r d b)`; both maps preserve the
base point. Equality of the supplied retraction with `q0.toLinearMap` gives
identity on that fibre, whereas an anchor `q0.comp (Γ d) = id` alone does not.
`ContinuousLinearMap.kerFamilyHomeomorphOfContinuous` gives the same
coordinates from operator-seminorm continuity of `Γ` and joint continuity of
the original projection `(d, a) ↦ Γ d (r d a)`.

## Norms of idempotents

[`IsIdempotentElem.one_le_norm`](../VectorBundles/Analysis/Normed/Ring/Idempotent.lean)
shows that a nonzero idempotent in a non-unital normed ring has norm at least one.
If its norm is at most one, `IsIdempotentElem.norm_eq_one` gives norm exactly one.

## Finite orthogonal idempotent families

[Orthogonal idempotent families](../VectorBundles/Algebra/Ring/OrthogonalIdempotents.lean)
`p q : I → R` over any semiring and finite index type satisfy
`u * p j = q j * p j = q j * u`, where `u = ∑ i, q i * p i`.
If `u` is a unit, that prescribed unit simultaneously conjugates `p` to `q`,
and both families sum to one. Completeness is an output, not a hypothesis.
No commutativity, nontriviality, or nonempty-index assumption is needed.
The diagonal matched-product sum is `∑ i, p i`, not necessarily one.

## Close idempotent operators

Here `E` is a normed space over a nontrivially normed field `K`.

[Close idempotent endomorphisms](../VectorBundles/Analysis/Normed/Operator/Idempotent.lean)
with `‖p - q‖ < 1` have continuously linearly equivalent ranges and kernels, using
the same normalized unit `q * p + (1 - q) * (1 - p)` and its inverse. Hence both
cardinal module ranks are equal. For a continuous idempotent family over any
topological parameter space, both rank functions are locally constant. The
unit/equivalence assertion assumes `HasSummableGeomSeries (E →L[K] E)`, supplied
when `E` is complete. Rank equality and local constancy need no geometric-summability
or completeness hypothesis. The given norms are retained and the zero space is allowed.

## Finite ambient open grids for compact products

[`IsCompact.exists_fin_open_cover_prod_subset`](../VectorBundles/Topology/Compactness/Product.lean)
refines an ambient open cover of `S × T`, where `S` and `T` are compact subsets
of arbitrary topological spaces, into finite ambient open covers `V` of `S`
and `W` of `T`. Every full product `V j × W k` lies in a selected member of the
original cover. The spaces may have independent universes, with no separation
assumptions. The original labels may belong to any sort, and either finite
family may be empty.

## Finite subdivisions of closed real intervals

[`exists_fin_monotone_Icc_subset_open_cover_Icc`](../VectorBundles/Topology/UnitInterval.lean)
subdivides any nonempty closed real interval into finitely many monotone closed slabs,
each contained in a selected member of the given open cover. The cuts include
both endpoints and the slabs cover the interval exactly. Covers may be indexed
by any sort; repeated cuts and at least one slab also cover singleton intervals.
The product-neighbourhood theorem
`exists_open_nhds_prod_Icc_subset_open_cover_unitInterval` provides a common open
neighbourhood for all slabs without separation assumptions on the base space.

[`IsCompact.exists_fin_open_cover_prod_Icc_subset`](../VectorBundles/Topology/UnitInterval.lean)
combines the compact-product open grid with the finite interval subdivision to
give a rectangular refinement over any compact subset of an arbitrary topological
space: one finite monotone grid and one finite ambient open base cover, common to
all slabs. The base cover is the same one supplied by the compact-product theorem.
Every full base-set × closed-slab rectangle lies in a selected member of the
original ambient open cover. The cuts include both endpoints, and the slabs
cover the real interval exactly. No separation assumption is needed; the base
family may be empty, and singleton intervals still have at least one slab.

## Finite product-chart selection

For a compact base `X` and an arbitrary topological parameter space `Y` with a
chosen point `y₀`, local whole-product charts near every point of `X` admit a
finite ordered open cover. The selected charts retain their original varying
models, their homeomorphisms on the original projection preimages, both base
laws, and agreement with the original coordinates in both directions on the
slice at `y₀`.

With the given module structures on the original projection fibers over an
arbitrary semiring, the linear version retains linear coordinates at every
parameter, their forward and inverse formulas for the same homeomorphism, and
their identification with the original linear coordinates at `y₀`. The base may
be empty; the semiring need not be commutative or carry a topology.

The results are
[`exists_finiteProductCover_of_local`](../VectorBundles/Topology/FiberBundle/FiniteCylinderCover.lean)
and
[`exists_finiteLinearProductCover_of_local`](../VectorBundles/Topology/FiberBundle/FiniteCylinderCover.lean).
The cylinder-cover APIs are their exact specializations to `Y = I`, `y₀ = 0`.
The whole-product charts are hypotheses: this does not construct them from an
ordinary local atlas over an arbitrary parameter space. Neither compactness of
`Y` nor continuity of the projection is assumed.

## Algebraic retractions and distance

- **Algebraic projection/preimage retractions:** for an injective linear map
  `β : F →ₗ[K] A` from a given plain module over an `RCLike` field into a given
  inner product space, `[β.range.HasOrthogonalProjection]` gives
  [`LinearMap.orthogonalRetraction`](../VectorBundles/Analysis/InnerProductSpace/Projection/LinearMap.lean).
  Its embedded value is Mathlib's orthogonal projection, and it retracts `β`.
  Finite-dimensional `F` supplies this capability through inherited range
  completeness, without choosing a norm or topology on `F` or requiring `A` to be
  complete. The [family API](../VectorBundles/Analysis/InnerProductSpace/Projection/Fiberwise.lean)
  gives `R : X × A → E` for any given `p : E → X`, module structures on its
  fibres `{t : E // p t = x}`, and injective fibre embeddings with this projection
  capability; finite-dimensional fibres suffice. It proves `p (R (x, a)) = x`
  and `R (p t, β (p t) ⟨t, rfl⟩) = t`, including a left-inverse law for any
  specified map with that image formula. No topology on the base or total space,
  nonemptiness, or positive-rank hypothesis is needed. The
  [real-axis example](../VectorBundlesTest/OrthogonalRetraction.lean) uses the
  finite-dimensional construction on the original fibres of `Bool × ℝ → Bool`.
  These APIs do not assert continuity or a general residual-orthogonality theorem.

- **Distance and closure for a given orthogonal retraction:** for
  `h : β.IsOrthogonalRetraction r`, the
  [distance API](../VectorBundles/Analysis/InnerProductSpace/Projection/Distance.lean)
  decomposes squared error and identifies `‖a - β (r a)‖` with the metric
  distance from `a` to the range of `β`. The point `β (r a)` attains this
  distance, and the scalar residual norm is 1-Lipschitz. In a seminormed ambient
  inner product space, membership in the closure of the range is equivalent to
  `‖a - β (r a)‖ = 0`, and `β v` has the same error exactly when its distance
  from `β (r a)` is zero. In a normed ambient space, the range is closed and
  minimum error is equivalent to `v = r a`. No topology or norm on the
  coefficient module or completeness assumption is needed.
  The same supplied witness gives `norm_image_le`, namely `‖β (r a)‖ ≤ ‖a‖`,
  and `dist_image_image_le`, namely
  `dist (β (r a)) (β (r b)) ≤ dist a b`. These are bounds for the `A`-valued
  projected image, not for `r` in any chosen coefficient norm. The
  [real-axis example](../VectorBundlesTest/OrthogonalRetractionDistance.lean)
  also identifies the real axis as the orthogonal complement of the imaginary
  kernel, including the real and imaginary units, and checks the distance bound.

## Supported weighted coordinates

Over a commutative semiring `K`, take arbitrary module families `F x` and `G i`,
arbitrary subsets `U i` of a base `X`, scalar weights `w i : X → K`, and given
linear equivalences `c i x : G i ≃ₗ[K] F x` whenever `x ∈ U i`.
[`LinearMap.weightedCoordinates`](../VectorBundles/LinearAlgebra/WeightedCoordinates.lean)
maps `F x` linearly into the **full dependent product** of the `G i`. Coordinate
`i` is `w i x • (c i x).symm v` on its domain and zero outside. Membership,
nonmembership, zero-weight and chart-evaluation rules expose these values.
`weightedCoordinates_injective_of_span_eq_top` gives fibrewise injectivity when
all weights of the **valid charts at that point** generate the unit ideal:
`Ideal.span ((fun i => w i x) '' {i | x ∈ U i}) = ⊤`.
No individual weight need be a unit, and the index set need not be finite.
`weightedCoordinates_injective_of_isUnit` is the sufficient special case of one
valid coordinate with a **unit** weight; a merely nonzero chosen weight does not
suffice over a general commutative semiring.

For the original equality fibres `{t : T // p t = x}`, give the inherited
subspace topologies and module structures, without assuming the fibre operations
continuous. With topologies on `K` and every `G i` and continuous scalar
multiplication on each model,
[`LinearMap.continuous_weightedCoordinates`](../VectorBundles/Topology/Maps/WeightedCoordinates.lean)
proves continuity of the total coordinate map if `p`, the weights, and the exact
inverse-coordinate maps on `p ⁻¹' U i` are continuous, and
`closure {x | w i x ≠ 0} ⊆ U i` for every `i`. Containment of the cozero set alone
is not this support hypothesis. The result reuses weighted zero extension into
each model and continuity into the product.

Neither result requires a finite index set, finite-dimensional models, norms or
nontrivial modules; the continuity helper's domains need not be open. The charts
and weights are **given**, not an atlas or weight-existence construction, and
this is not itself a total-space embedding theorem.

## Local constancy of fibre finrank

Over a division ring `K`, let `F x` be algebraic modules on a topological base
`X` and let `G i` be model modules, with independent universes and an arbitrary
index type. Suppose the interiors of sets `U i` cover `X`, and for each
`x ∈ U i` there exists a linear equivalence `F x ≃ₗ[K] G i`.
[`Module.isLocallyConstant_finrank_of_linearEquiv_cover`](../VectorBundles/Topology/Module/Finrank.lean)
then makes `x ↦ Module.finrank K (F x)` locally constant.

The sets need not themselves be open, and the equivalences are only pointwise:
no continuous choice, module topology, finite index set, finite-dimensionality
or uniform dimension bound is required. This is **natural-number finrank**,
which is zero for infinite-dimensional modules, not a cardinal-dimension result.
The argument uses invariance of finrank under the supplied linear equivalences;
it neither constructs a bundle atlas nor changes the given module structures.

## Supported pairings and partitions of unity

- **Constant extension of supported pairings:** for arbitrary topological spaces
  and a continuous pairing `μ : M × V → W` with `μ(m₀, v) = w₀`, a continuous
  weight `w : X → M` and map `g : U → V` admit a continuous extension of
  `μ(w x, g x)` by `w₀` whenever `closure {x | w x ≠ m₀} ⊆ U`.
  The [pairing API](../VectorBundles/Topology/ContinuousMap/PairingExtension.lean)
  constructs the uniquely characterized map. The subset need not be open or closed;
  no separation or nonemptiness assumptions are needed. The
  [scalar-action specialization](../VectorBundles/Topology/ContinuousMap/WeightedExtension.lean)
  extends weighted maps by zero and is used for finite bundle embeddings.

- **Finite partitions of unity on normal spaces:**
  [`ContinuousMap.exists_finite_weights`](../VectorBundles/Topology/ContinuousMap/FiniteWeights.lean)
  gives continuous real weights for any normal topological space `X`, arbitrary index type
  `J`, finite index set `s : Finset J` and family `U : J → Set X` whose members on `s` are
  open and cover `X`. The weights are defined at every index, lie in `[0, 1]`, vanish as
  continuous maps off `s`, and sum to one over `s` at each point. For every index `i`,
  `closure {x | w i x ≠ 0} ⊆ U i`. No compactness, nonemptiness, T1 or Hausdorff assumption,
  finiteness of `J`, or openness off `s` is required.

- **Normal-space cutoffs with closed support:** for a closed set `C` contained
  in an open set `U` of a normal space,
  [`IsClosed.exists_continuous_one_tsupport_subset`](../VectorBundles/Topology/FiniteNormalWeights.lean)
  supplies a continuous real function in `[0, 1]`, equal to one on `C`, with
  `tsupport g ⊆ U`. Here `tsupport` is the closure of the cozero set; pointwise
  vanishing outside `U` alone would be weaker.

- **Finite weights on a closed subset:** for a finite index type, a closed set
  `s` in a normal space and open sets `U i` covering `s`,
  [`IsClosed.exists_finite_continuous_partition_of_unity`](../VectorBundles/Topology/FiniteNormalWeights.lean)
  constructs continuous nonnegative real weights with `tsupport (w i) ⊆ U i`.
  Their sum is at most one on the whole base and equals one on `s`; a cover of
  the whole base is not assumed. There is no T₁, Hausdorff, compactness or
  nonemptiness hypothesis. Empty index types are allowed: the cover premise
  then forces `s` empty, not the whole base.

- **Components of a given finite partition:** on an arbitrary topological
  space, [`PartitionOfUnity.finite_continuous_weights`](../VectorBundles/Topology/FiniteNormalWeights.lean)
  extracts the same continuity, nonnegativity, sum bounds and closed-support
  containments from a supplied finite `PartitionOfUnity ι X s` subordinate to
  `U`. This extraction needs neither normality, closedness of `s` nor openness
  of `U` once the partition and subordination are given. It is distinct from
  constructing the partition.

## Cylinder charts and transport

- **Heterogeneous closed-cylinder gluing:** for a continuous projection
  `p : Z → X × T`, with linearly ordered topological `T` having closed
  lower and upper rays, supplied projection-preserving charts on its two
  closed half-cylinders may have different topological models. The
  [gluer](../VectorBundles/Topology/FiberBundle/ClosedCylinder.lean)
  gives a whole-cylinder homeomorphism into the left model, retaining its
  entire left chart. See the [foundation guide](Results.md#cylinder-foundations)
  for this construction, common-neighborhood subdivision and selection from
  given whole-interval charts.

- **Whole-cylinder charts from local atlases:** an open, base-preserving atlas for
  a continuous projection `p : T → X × unitInterval` gives an open neighborhood `U`
  of each point of `X` and a homeomorphism
  `{z : T // (p z).1 ∈ U} ≃ₜ (U × unitInterval) × F j₀`.
  Both directions preserve the cylinder base point and agree at time zero with
  one input chart. If `X` is compact, finitely many such neighborhoods cover `X`,
  without any normality assumption. The
  [subdivision API](../VectorBundles/Topology/FiberBundle/ClosedCylinderSubdivisionData.lean)
  records the recursively glued charts and their successor and endpoint laws.
  When the input coordinates on each original projection fiber are linear, the
  [linear refinement](../VectorBundles/Topology/FiberBundle/ClosedCylinderSubdivisionDataLinear.lean)
  gives linear coordinates for the same homeomorphism at every time. The scalar
  semiring may be noncommutative, chart models may vary, and the original total
  space, fiber operations and topologies are unchanged. No fiber norm, finite-rank
  or scalar-topology assumption is imposed.

- **Finite ordered cylinder transport with given weights:**
  [`Bundle.Trivialization.finiteCylinderTransport`](../VectorBundles/Topology/FiberBundle/FiniteTransport.lean)
  gives a homeomorphism from the iterated standard pullback of the entire original
  zero-time restriction to the same given total space over `X × unitInterval`.
  The input is an ordered family of charts indexed by `Fin n`, with possibly
  varying topological models `F j` independent of the unstructured total-space
  parameter `P`, covering cylinders `U j × unitInterval` whose sets `U j` cover `X`.
  Continuous real weights lie in `[0, 1]`, sum to one, and satisfy
  `closure {x | w j x ≠ 0} ⊆ U j`. No normality of `X` or openness of `U j` is needed.
  Both directions preserve the entire cylinder base point and fix every bottom
  point. The [prefix API](../VectorBundles/Topology/FiberBundle/FiniteTransport.lean)
  gives zero, ordered successor and last-stage laws, including unchanged original
  points off each closed support. The top restriction agrees with the independently
  ordered `finiteCylinderEndpointTransport` between the standard endpoint pullbacks.

- **Cylinder transport for a given projection:**
  [`Bundle.Trivialization.finiteCylinderTransportOfProjection`](../VectorBundles/Topology/FiberBundle/FiniteTransport/Projection.lean)
  applies the same weighted construction to any map `p : T → X × unitInterval`
  with the given topology on `T` and the cylinder charts above. Its source is the
  standard product-subspace pullback of the entire original zero restriction;
  its target is the same `T`. Continuity of `p` follows from the covering charts.
  Both directions preserve the whole base point and fix every original bottom
  point, including points in the closed supports.
  `finiteCylinderTransportOfProjection_apply_eq_last` characterizes its value at
  every time by an ordered sequence of the original chart lifts in `T`.
  The independently constructed `finiteCylinderEndpointTransportOfProjection`
  compares the entire original zero and one slices, with their inherited topologies,
  and agrees with cylinder transport on the top slice.
  Given modules on the original fibers and the models `F j` over any possibly
  noncommutative semiring `R`, and linear coordinate equivalences agreeing with
  the charts, the [family](../VectorBundles/Topology/FiberBundle/FiniteTransport.lean)
  and [projection](../VectorBundles/Topology/FiberBundle/FiniteTransport/Projection.lean)
  linearity theorems make this same transport fiberwise `R`-linear. Real numbers
  parametrize time only: no topology on `R` or continuity of module operations
  is required, nor a common model, rank, finite-dimensionality, field, further
  separation or nonempty-fiber hypothesis.

- **Finite open cylinder-chart covers, without given weights:**
  For a normal topological space `X`, a finite ordered family of given charts
  covering whole cylinders `U j × unitInterval`, where the `U j` are open and
  cover `X`, gives the
  [family transport](../VectorBundles/Topology/FiberBundle/FiniteTransport/Existence.lean)
  `Bundle.Trivialization.exists_finiteCylinderTransport` without input weights.
  With the original-fiber modules and matching linear chart coordinates above,
  [`Bundle.Trivialization.exists_finiteCylinderTransportOfProjection`](../VectorBundles/Topology/FiberBundle/FiniteTransport/Existence.lean)
  returns subordinate weights and their bounds, sum and closed-cozero certificates,
  together with a homeomorphism equal to `finiteCylinderTransportOfProjection`
  for those same weights. Its conclusions include both base and bottom laws,
  linearity on the given original fibers over `R`, and top-slice equality with
  the independently constructed full-slice endpoint transport using those same
  weights. No separation assumption beyond `NormalSpace X` is added.

## Varying-rank atlases

- **Locally varying finite-rank atlas data:** covering fibrewise-linear charts on
  given module fibres and their given total-space topology, with linear coordinate
  equivalences, pointwise finite generation of the original fibres, and fixed-model
  bundle data on each chart domain. The models include arbitrary-base product bundles
  in every finite rank and discrete families with varying ranks, including zero.
  See the [atlas API](../VectorBundles/Topology/VectorBundle/FiniteRank.lean),
  [`Bundle.FiniteRankAtlas.moduleFinite_fiber`](../VectorBundles/Topology/VectorBundle/FiniteRank/LinearEquiv.lean),
  [patch data](../VectorBundles/Topology/VectorBundle/FiniteRank/Patch.lean),
  [product models](../VectorBundles/Topology/VectorBundle/FiniteRank/Trivial.lean) and
  [discrete models](../VectorBundles/Topology/VectorBundle/FiniteRank/Discrete.lean).
- **Projections, zero sections and descent for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.continuous_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  and [`Bundle.FiniteRankAtlas.isOpenMap_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  prove that the original projection is continuous and open.
  [`Bundle.FiniteRankAtlas.isQuotientMap_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  makes it a quotient map.
  [`Bundle.FiniteRankAtlas.isOpen_iff_preimage_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  and [`Bundle.FiniteRankAtlas.isClosed_iff_preimage_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  characterize open and closed base subsets by their projection preimages.
  [`Bundle.FiniteRankAtlas.continuous_iff_comp_proj`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  characterizes continuity of maps from the base to any topological space by continuity
  after composition with this projection. The canonical zero section is continuous by
  [`Bundle.FiniteRankAtlas.continuous_zeroSection`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean).
  It is a topological embedding by
  [`Bundle.FiniteRankAtlas.isEmbedding_zeroSection`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean).
  [`Bundle.FiniteRankAtlas.continuous_iff_zeroSection_comp`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  characterizes continuity of maps from any topological domain into the base by
  continuity after composition with the zero section, using the given total-space
  topology and no additional continuity hypotheses.
  These results hold for any supplied finite-rank atlas. Chart ranks may vary and may
  be zero, with no common model, scalar-operation continuity or base separation hypothesis.

- **Hausdorff total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.t2Space_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves that the original total space is Hausdorff when the given base and every
  chart-coordinate space `Fin (A.rank i) → K` are Hausdorff. These coordinate spaces
  use the Pi topology from the given scalar topology. Ranks may vary and may be zero;
  no Hausdorff scalar-field hypothesis is required.

- **Locally compact total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.locallyCompactSpace_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves local compactness of the original total space when the given base and every
  chart-coordinate space `Fin (A.rank i) → K` are locally compact. These coordinate
  spaces use the Pi topology from the given scalar topology. Ranks may vary and may
  be zero; neither local compactness of the scalar field nor Hausdorffness is required.

- **First-countable total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.firstCountableTopology_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves first countability of the original total space when the given base and every
  exact chart-coordinate space `Fin (A.rank i) → K` are first countable. These coordinate
  spaces carry the Pi topology from the given scalar topology. Ranks may vary without
  a global bound, including zero with its singleton zero fibre. No scalar-field
  first-countability, second-countability or countable-atlas hypothesis is required.

- **T0 total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.t0Space_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves that the original total space is T0 when the given base and every exact
  chart-coordinate space `Fin (A.rank i) → K` are T0. These coordinate spaces carry
  the Pi topology from the given scalar topology. Ranks may vary without a global
  bound, including zero with its singleton zero fibre; the scalar field need not be
  T0. No T1, Hausdorffness or countability hypothesis is required.

- **T1 total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.t1Space_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves that the original total space is T1 when the given base and every exact
  chart-coordinate space `Fin (A.rank i) → K` are T1. These coordinate spaces carry
  the Pi topology from the given scalar topology. Ranks may vary without a global
  bound, including zero with its singleton zero fibre; the scalar field need not be
  T1. No Hausdorffness or countability hypothesis is required.

- **Regular total spaces for finite-rank atlases:**
  [`Bundle.FiniteRankAtlas.regularSpace_totalSpace_iff`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean)
  proves that the original total space is regular exactly when the given base is
  regular, assuming every exact chart-coordinate space `Fin (A.rank i) → K` is regular.
  These coordinate spaces carry the Pi topology from the given scalar topology.
  The base-to-total implication is also available as
  [`Bundle.FiniteRankAtlas.regularSpace_totalSpace`](../VectorBundles/Topology/VectorBundle/FiniteRank/Projection.lean).
  Ranks may vary without a global bound, including zero with its singleton zero fibre.
  No scalar-field regularity, Hausdorffness, local compactness or countability
  hypothesis is required.

## Finite cover shrinkings

- **Finite-support shrinking in normal spaces:**
  [`Set.Finite.exists_open_cover_shrinking`](../VectorBundles/Topology/ShrinkingLemma.lean)
  shrinks a cover indexed by a finite subset `s` of an arbitrary index type to an
  all-open cover, empty off `s`, with closure containment at every index. Only the
  original sets indexed by `s` must be open and cover the space. No T1 assumption
  or finiteness of the whole index type is required.
  [`Set.Finite.exists_nested_open_cover_shrinking`](../VectorBundles/Topology/ShrinkingLemma.lean)
  gives two such covering families with nested closure containment.

## Bundle geometry and topological criteria

The [detailed results guide](Results.md) groups statements and examples by
topic, with their individual hypotheses and distinctions from existing Mathlib
constructions. Selected results include:

- **Compatible fiber metrics.**
  [`VectorBundle.continuousHermitianMetric`](../VectorBundles/Topology/VectorBundle/MetricExistence.lean)
  constructs continuous positive-definite Hermitian metrics on finite-dimensional
  `RCLike` vector bundles over paracompact Hausdorff bases. They induce the original
  fiber topologies; the normed model need not have an inner-product norm.

- **Splitting and comparison for supplied metrics.**
  For a supplied continuous Hermitian metric and an intrinsic submodule bundle
  whose total-space inclusion is an embedding, with finite-dimensional `RCLike`
  ambient model, [orthogonal addition](../VectorBundles/Topology/VectorBundle/OrthogonalAddition.lean)
  is a homeomorphism onto the ambient total space; [comparison](../VectorBundles/Topology/VectorBundle/OrthogonalComparison.lean)
  identifies its complements for two such metrics using their projections.
  The base is any topological space. Complement fiber subtype and ambient-induced
  total topologies are retained; no global intrinsic-model finiteness is required.

- **Pointwise-continuous surjectivity, without a norm.**
  Over a field with a given T₁ topology making it a topological ring,
  [`LinearMap.eventually_surjective_of_continuousAt`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  gives surjectivity near `b₀` from surjectivity there and each fixed-vector evaluation's
  `ContinuousAt` at `b₀`; [`LinearMap.isOpen_setOf_surjective`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  needs each fixed-vector evaluation `Continuous` for an open locus. The base is
  arbitrary, source purely algebraic with no topology, and target finite-dimensional
  with its given `IsModuleTopology`, in four independent universes. No scalar norm,
  inversion continuity, completeness, extra target continuity/separation hypotheses
  or base separation are required.

- **Openness of joint linear families and bundle maps.**
  Over a nontrivially normed field,
  [`LinearMap.isOpenMap_prodMap`](../VectorBundles/Topology/Algebra/Module/OpenMap.lean)
  makes jointly continuous algebraic linear surjections between topological vector
  spaces open on products when the finite-dimensional target has its given
  `IsModuleTopology`. The [bundle theorem](../VectorBundles/Topology/VectorBundle/OpenMap.lean)
  transfers this over a common base with given linear trivializations and original
  fiber and total-space topologies. Neither model needs a norm, the source need not
  be finite-dimensional, and no completeness is assumed.

- **Forward continuity gives bundle inverses.**
  [`VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology`](../VectorBundles/Topology/VectorBundle/Isomorphism.lean)
  constructs a homeomorphism from algebraic fiberwise linear equivalences with a
  continuous forward total map over a nontrivially normed field. The source normed
  model is finite-dimensional; the target normed model has `IsModuleTopology`.
  Empty bases and zero rank are allowed, and models need not be globally identified.
  A complete-field constructor derives the target properties at each base point.

- **Reciprocal finite sums of real squares.**
  [`continuous_inv_finset_sum_sq`](../VectorBundles/Topology/Algebra/GroupWithZero.lean)
  gives continuity of the reciprocal of a selected finite sum of real squares
  when the selected weights are continuous and, at each point, some selected
  weight is nonzero. Weights outside the selected set are unrestricted; the
  topological base may be empty. This is a real, ordered-square specialization,
  not a statement about sums of complex squares.

- **Scalar endomorphisms of line bundles.**
  [`VectorBundle.scalarEndHomeomorph`](../VectorBundles/Topology/VectorBundle/ScalarEnd.lean)
  identifies `B × κ` with the endomorphism bundle of a line bundle modeled on a
  nontrivially normed field `κ`, for any topological base `B`, including the empty
  base. Both directions preserve the base, using the original fiber topologies
  and continuous-linear-map bundle topology.

- **Sharp projection criteria.**
  A fiber-bundle projection is an [open embedding](../VectorBundles/Topology/FiberBundle/Projection.lean)
  exactly when every original fiber is subsingleton, and canonically a homeomorphism
  when each is also nonempty. It is [proper](../VectorBundles/Topology/FiberBundle/Proper.lean)
  exactly when every given fiber is compact, equivalently when the base is empty or
  the model is compact. The given topologies and fiber-bundle data are retained,
  without scalar or separation assumptions.

- **Second countability of total spaces.**
  [`FiberBundle.secondCountableTopology_totalSpace_iff`](../VectorBundles/Topology/FiberBundle/Countability.lean)
  says the total space is second-countable exactly when the base is empty, the model
  is empty, or both are second-countable. Given topologies, fiber-bundle data and
  independent base/model/fiber universes are retained, without compactness or
  separation assumptions. The existing `FiberBundle.secondCountableTopology` instance
  in this library supplies the forward construction, using Mathlib's countable-cover
  and trivialization APIs.

- **Finite complementary bundles and cylinder charts.**
  [`VectorBundle.finiteComplement`](../VectorBundles/Topology/VectorBundle/FiniteComplement.lean)
  gives a finite-dimensional complement for a finite-dimensional `RCLike` bundle
  on a compact normal base, with a global linear trivialization of their fiberwise product.
  Subspace fiber and ambient-induced total topologies are retained; the complement
  is not asserted complementary or orthogonal to a prescribed embedding.
  [Whole-interval cylinder charts](../VectorBundles/Topology/VectorBundle/Cylinder.lean)
  exist near each point of any `X` for a vector bundle over `X × unitInterval`,
  without dimension or completeness assumptions; this is not homotopy invariance.
