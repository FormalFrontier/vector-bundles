# Credits and license

[Library overview](README.md) · [Result catalogue](docs/HeadlineResults.md)

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
Compact rectangular refinements use Mathlib's tube lemma and finite-subcover API
in `Topology.Compactness.Compact` (Johannes Hölzl, Mario Carneiro and Yury Kudryashov)
and follow the finite slice-neighbourhood argument in
`Topology.Compactness.Paracompact` (Reid Barton and Yury Kudryashov), following
Dan Ma's [compact-times-paracompact exposition](https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-is-paracompact/).
The real closed-slab refinement combines the compact-product grid with the finite
interval subdivision API, using Patrick Massot and Kim Morrison's Mathlib
unit-interval formalization.
The Hermitian and semilinear APIs extend those prior formalizations; the other
modules document their own mathematical and formalization sources. Finite cylinder
transport reuses Mathlib's bundle, pullback-topology and trivialization APIs through
the supported chart transport and standard pullback comparisons.
Fiber-bundle metrizability follows the original formalization by Formal Frontier Agents
and uses Metrization's locally finite closed-neighbourhood-cover criterion.
The locally finite and paracompactness statements use Yury Kudryashov's locally
finite-family API, Reid Barton and Yury Kudryashov's paracompactness formalization,
and Anatole Dedecker and Etienne Marion's proper-map API in Mathlib.
The scalar-endomorphism construction uses ProjectiveModules' invertible-module
topology and continuous scalar-endomorphism equivalence, and follows the earlier
Formal Frontier formalization of the algebraic scalar-endomorphism equivalence.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
