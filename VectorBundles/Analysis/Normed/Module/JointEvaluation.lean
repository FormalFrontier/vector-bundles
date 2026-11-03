/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Joint continuity of semilinear evaluation

For a finite basis over a semiring `R` and a ring homomorphism `σ : R →+* S`, assume
that the scalar coordinates composed with `σ` are continuous. A family of algebraic
`σ`-semilinear maps is jointly continuous exactly when its evaluations at the basis
vectors are continuous. No topology on `R` or continuity of `σ` is required. The source
needs no continuous operations; the target only needs continuous addition and jointly
continuous `S`-scalar multiplication. The linear criterion is the identity-hom specialization.

Over a complete nontrivially normed field, a family of algebraic linear maps from
a finite-dimensional Hausdorff topological module to a topological module with
continuous addition and scalar multiplication is jointly continuous exactly when
its evaluations at fixed vectors are continuous. All topological structures are
the given ones; no separation assumption is imposed on the target.

For continuous linear maps from a finite-dimensional seminormed space to any seminormed
space over a possibly incomplete nontrivially normed field, joint continuity is equivalent
to continuity of the family in the given operator-norm topology. Neither space needs to
be separated or complete.

## References

The finite-basis expansion uses Mathlib's `Module.Basis.sum_repr` and semilinear-map API.
The finite-dimensional specialization uses Mathlib's `Module.Basis.continuous_coe_repr`
and agrees with `continuous_clm_apply` from its finite-dimensional normed-module API,
developed by Sébastien Gouëzel. The seminormed operator-space criterion uses the
finite-evaluation bound over an incomplete field and Mathlib's `Continuous.clm_apply`.
-/

@[expose] public section

open scoped BigOperators

universe uR uι uK uG uA uZ
universe uS

namespace Module.Basis

/-- For a finite basis whose scalar coordinates become continuous after applying `σ`,
a family of `σ`-semilinear maps is jointly continuous exactly when its evaluations at
the basis vectors are continuous. No topology on the source semiring is required;
only the target needs continuous addition and jointly continuous scalar multiplication. -/
theorem continuous_uncurry_iff_semilinear
    {R : Type uR} [Semiring R]
    {S : Type uS} [Semiring S] [TopologicalSpace S]
    {σ : R →+* S}
    {ι : Type uι} [Finite ι]
    {G : Type uG} [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    {A : Type uA} [AddCommMonoid A] [Module S A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul S A]
    {Z : Type uZ} [TopologicalSpace Z]
    (b : Module.Basis ι R G)
    (hcoord : ∀ i, Continuous (fun g : G => σ (b.repr g i)))
    {L : Z → G →ₛₗ[σ] A} :
    Continuous (fun p : Z × G => L p.1 p.2) ↔
      ∀ i, Continuous (fun z : Z => L z (b i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hL i
    exact hL.comp (continuous_id.prodMk continuous_const)
  · intro hL
    have hexp (z : Z) (v : G) :
        L z v = ∑ i, σ (b.repr v i) • L z (b i) := by
      calc
        L z v = L z (∑ i, (b.repr v i) • b i) :=
          congrArg (fun w : G => L z w) (b.sum_repr v).symm
        _ = ∑ i, σ (b.repr v i) • L z (b i) := by
          simp only [map_sum, LinearMap.map_smulₛₗ]
    have hsum : Continuous (fun p : Z × G =>
        ∑ i, σ (b.repr p.2 i) • L p.1 (b i)) := by
      exact continuous_finsetSum Finset.univ (fun i _ =>
        ((hcoord i).comp continuous_snd).smul ((hL i).comp continuous_fst))
    exact hsum.congr (fun p => (hexp p.1 p.2).symm)

/-- For a finite basis with continuous scalar coordinates, a family of linear maps
is jointly continuous exactly when its evaluations at the basis vectors are continuous.
Only the target needs continuous addition and scalar multiplication. -/
theorem continuous_uncurry_iff
    {R : Type uR} [Semiring R] [TopologicalSpace R]
    {ι : Type uι} [Finite ι]
    {G : Type uG} [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul R A]
    {Z : Type uZ} [TopologicalSpace Z]
    (b : Module.Basis ι R G)
    (hcoord : ∀ i, Continuous (fun v : G => b.repr v i))
    {L : Z → G →ₗ[R] A} :
    Continuous (fun p : Z × G => L p.1 p.2) ↔
      ∀ i, Continuous (fun z : Z => L z (b i)) := by
  exact b.continuous_uncurry_iff_semilinear (σ := RingHom.id R) (L := L) hcoord

end Module.Basis

namespace LinearMap

/-- Joint evaluation of a family of linear maps from a finite-dimensional Hausdorff
topological module to a module with continuous addition and scalar multiplication is
continuous exactly when every fixed-vector evaluation is continuous. -/
theorem continuous_uncurry_iff_of_finiteDimensional
    {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
    {G : Type uG} [AddCommGroup G] [Module K G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [ContinuousSMul K G] [FiniteDimensional K G]
    {A : Type uA} [AddCommMonoid A] [Module K A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul K A]
    {Z : Type uZ} [TopologicalSpace Z]
    {L : Z → G →ₗ[K] A} :
    Continuous (fun p : Z × G => L p.1 p.2) ↔
      ∀ v : G, Continuous (fun z : Z => L z v) := by
  constructor
  · intro hL v
    exact hL.comp (continuous_id.prodMk continuous_const)
  · intro hL
    let b := Module.finBasis K G
    exact (b.continuous_uncurry_iff
      (fun i => (continuous_apply i).comp b.continuous_coe_repr)).2
        (fun i => hL (b i))

end LinearMap

namespace ContinuousLinearMap

/-- A family of continuous linear maps from a finite-dimensional seminormed space is
continuous in the given operator-norm topology exactly when its joint evaluation is continuous.
The scalar field may be incomplete, and the original domain and target need not be separated
or complete. Finite-dimensionality refers to the module underlying the given domain normed
space. -/
theorem continuous_iff_continuous_uncurry_of_finiteDimensional
    {K : Type uK} [kK : NontriviallyNormedField K]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace K G kK.toNormedField sG]
    [hG : @FiniteDimensional K G (inferInstance : DivisionRing K)
      sG.toAddCommGroup nG.toModule]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    {Z : Type uZ} [tZ : TopologicalSpace Z]
    {L : Z → G →L[K] A} :
    Continuous L ↔ Continuous (fun p : Z × G => L p.1 p.2) := by
  constructor
  · intro hL
    exact (hL.comp continuous_fst).clm_apply continuous_snd
  · intro hL
    exact (continuous_iff_apply_of_finiteDimensional
      (K := K) (A := G) (G := A) (kK := kK) (sA := sG) (nA := nG) (hA := hG)
      (sG := sA) (nG := nA) L).2
        (fun v => hL.comp (continuous_id.prodMk continuous_const))

end ContinuousLinearMap
