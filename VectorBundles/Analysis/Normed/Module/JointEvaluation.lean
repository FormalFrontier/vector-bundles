/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Joint continuity of linear evaluation

For a finite basis with continuous scalar coordinates over a semiring with a given topology,
a family of algebraic linear maps is jointly continuous exactly when its evaluations
at the basis vectors are continuous. The source needs no continuous operations;
the target only needs continuous addition and scalar multiplication.

Over a complete nontrivially normed field, a family of algebraic linear maps from
a finite-dimensional Hausdorff topological module to a topological module with
continuous addition and scalar multiplication is jointly continuous exactly when
its evaluations at fixed vectors are continuous. All topological structures are
the given ones; no separation assumption is imposed on the target.

For continuous linear maps between normed spaces, this is also equivalent to
continuity of the family into the operator space.

## References

The finite-dimensional specialization uses Mathlib's `Module.Basis.continuous_coe_repr`
and agrees with `continuous_clm_apply` from its finite-dimensional normed-module API,
developed by Sébastien Gouëzel.
-/

@[expose] public section

open scoped BigOperators

universe uR uι uK uG uA uZ

namespace Module.Basis

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
  classical
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hL i
    exact hL.comp (continuous_id.prodMk continuous_const)
  · intro hL
    have hexp (z : Z) (v : G) :
        L z v = ∑ i, (b.repr v i) • L z (b i) := by
      calc
        L z v = L z (∑ i, (b.repr v i) • b i) :=
          congrArg (fun w : G => L z w) (b.sum_repr v).symm
        _ = ∑ i, (b.repr v i) • L z (b i) := by
          simp only [map_sum, map_smul]
    have hsum : Continuous (fun p : Z × G =>
        ∑ i, (b.repr p.2 i) • L p.1 (b i)) := by
      exact continuous_finsetSum Finset.univ (fun i _ =>
        ((hcoord i).comp continuous_snd).smul ((hL i).comp continuous_fst))
    exact hsum.congr (fun p => (hexp p.1 p.2).symm)

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

/-- A family of continuous linear maps on a finite-dimensional normed space is
continuous into the operator space exactly when its joint evaluation is continuous. -/
theorem continuous_iff_continuous_uncurry_of_finiteDimensional
    {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace K G]
    [FiniteDimensional K G]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {Z : Type uZ} [TopologicalSpace Z]
    {L : Z → G →L[K] A} :
    Continuous L ↔ Continuous (fun p : Z × G => L p.1 p.2) := by
  rw [continuous_clm_apply]
  exact (LinearMap.continuous_uncurry_iff_of_finiteDimensional
    (L := fun z => (L z).toLinearMap)).symm

end ContinuousLinearMap
