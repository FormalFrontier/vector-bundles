/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Adjoint
public import VectorBundles.Analysis.InnerProductSpace.GramRetraction
import VectorBundles.Analysis.Normed.Operator.UnitGramContinuity
import Mathlib.Tactic

/-!
# Canonical Gram families on a fixed domain

Let `f x : E →L[K] F` be injective at every parameter, with jointly continuous
evaluation. The domain `E` is a complete finite-dimensional normed inner-product
space, and `F` has its given normed inner-product structure. The characteristic
adjoint, inverse Gram composite and ambient projection are continuous in operator
norm. The normalized composite is a left inverse, and the projection has the
same range as `f x`, is idempotent and self-adjoint, and has kernel equal to the
orthogonal complement of that range. Its residual is orthogonal to the image.

The construction uses the given norms and inner products throughout. It requires
neither completeness nor finite dimension of `F`, and allows an empty parameter
space and the zero domain. Continuity of the original operator family follows
from joint continuity by the finite-dimensional evaluation criterion; it is not
an additional hypothesis.

## Implementation notes

This is a fixed-domain analytic result. It does not construct a complement for a
variable bundle or assert the full statement of Hatcher's Proposition 1.7.

## References

The proof reuses Mathlib's finite-dimensional evaluation topology and the
one-sided adjoint construction of this library, together with its adjoint-pair
norm and inverse Gram APIs. The analytic argument is independent of a
passage-level translation from a bundle-complement theorem.
-/

@[expose] public section

universe uX uK uE uF

namespace ContinuousLinearMap

variable {X : Type uX} {K : Type uK} {E : Type uE} {F : Type uF}
  [TopologicalSpace X] [RCLike K]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace K E] [InnerProductSpace K F]
  [CompleteSpace E] [FiniteDimensional K E]

/-- For a jointly continuous injective family on a fixed complete finite-dimensional
inner-product domain, the characteristic adjoints, inverse Gram composites and
range projections are operator-norm continuous for the given norms. These same
projections have the image, kernel, symmetry and residual properties of orthogonal
projections. No completeness of the ambient inner-product space is required. -/
theorem gramFamily_properties (f : X → E →L[K] F)
    (hjoint : Continuous (fun p : X × E => f p.1 p.2))
    (hinj : ∀ x : X, Function.Injective (f x)) :
    let g : X → F →L[K] E := fun x => adjointMap (f x)
    let r : X → F →L[K] E := fun x => inverseGramComp (f x) (g x)
    let P : X → F →L[K] F := fun x => (f x).comp (r x)
    (∀ (x : X) (v : E) (w : F), inner K (f x v) w = inner K v (g x w)) ∧
    (∀ x : X, r x = (Ring.inverse ((g x).comp (f x))).comp (g x)) ∧
    (∀ x : X, P x = (f x).comp (r x)) ∧
    Continuous g ∧ Continuous r ∧ Continuous P ∧
    (∀ x : X, (r x).comp (f x) = ContinuousLinearMap.id K E) ∧
    ∀ x : X,
      (P x).comp (P x) = P x ∧
      LinearMap.range ((P x).toLinearMap) = LinearMap.range ((f x).toLinearMap) ∧
      (∀ u v : F, inner K (P x u) v = inner K u (P x v)) ∧
      LinearMap.ker ((P x).toLinearMap) =
        (LinearMap.range ((f x).toLinearMap)).orthogonal ∧
      ∀ (v : E) (w : F), inner K (f x v) (w - P x w) = 0 := by
  classical
  let g : X → F →L[K] E := fun x => adjointMap (f x)
  let r : X → F →L[K] E := fun x => inverseGramComp (f x) (g x)
  let P : X → F →L[K] F := fun x => (f x).comp (r x)
  have hAdj (x : X) : Function.IsAdjointPair (inner K) (inner K) (f x) (g x) := by
    exact (isAdjointPair_iff_eq_adjointMap (f x) (g x)).mpr rfl
  have hf : Continuous f := by
    rw [continuous_clm_apply]
    intro v
    exact hjoint.comp (continuous_id.prodMk continuous_const)
  have hg : Continuous g := by
    have hcont : Continuous f ↔ Continuous g := by
      apply Function.IsAdjointPair.continuous_iff
      exact hAdj
    exact hcont.mp hf
  have hG (x : X) : IsUnit ((g x).comp (f x)) :=
    (Function.IsAdjointPair.isUnit_comp_iff (hAdj x)).mpr (hinj x)
  have hr : Continuous r := by
    apply ContinuousLinearMap.continuous_inverseGramComp_of_isUnit <;> assumption
  have hP : Continuous P := by
    apply ContinuousLinearMap.continuous_gramProjection_of_isUnit <;> assumption
  refine ⟨fun x v w => (hAdj x).apply v w, fun _ => rfl, fun _ => rfl,
    hg, hr, hP, ?_, ?_⟩
  · intro x
    exact inverseGramComp_comp_of_isUnit (hG x)
  · intro x
    refine ⟨comp_inverseGramComp_idempotent_of_isUnit (hG x), ?_, ?_, ?_, ?_⟩
    · apply le_antisymm
      · rintro w ⟨u, hu⟩
        exact ⟨r x u, hu⟩
      · rintro w ⟨v, hv⟩
        refine ⟨f x v, ?_⟩
        calc
          P x (f x v) = f x v :=
            comp_inverseGramComp_apply_image_of_isUnit (hG x) v
          _ = w := hv
    · intro u v
      exact (isAdjointPair_inner_comp_inverseGramComp_of_isUnit
        (hG x) (hAdj x)).apply u v
    · ext w
      constructor
      · intro hw
        have hw0 : P x w = 0 := hw
        have hrw : r x w = 0 := by
          apply hinj x
          calc
            f x (r x w) = P x w := rfl
            _ = 0 := hw0
            _ = f x 0 := (map_zero (f x)).symm
        have hgw : g x w = 0 :=
          (inverseGramComp_eq_zero_iff_of_isUnit (hG x) w).mp hrw
        rw [Submodule.mem_orthogonal]
        rintro _ ⟨v, rfl⟩
        calc
          inner K (f x v) w = inner K v (g x w) := (hAdj x).apply v w
          _ = 0 := by rw [hgw, inner_zero_right]
      · intro hw
        rw [Submodule.mem_orthogonal] at hw
        have hgww : inner K (g x w) (g x w) = 0 := by
          calc
            inner K (g x w) (g x w) = inner K (f x (g x w)) w :=
              ((hAdj x).apply (g x w) w).symm
            _ = 0 := hw (f x (g x w)) ⟨g x w, rfl⟩
        have hgw : g x w = 0 := inner_self_eq_zero.mp hgww
        have hrw : r x w = 0 :=
          (inverseGramComp_eq_zero_iff_of_isUnit (hG x) w).mpr hgw
        change f x (r x w) = 0
        rw [hrw, map_zero]
    · intro v w
      exact inner_comp_inverseGramComp_residual_of_isUnit (hG x) (hAdj x) v w

/-- A jointly continuous pointwise-injective family with a complete finite-dimensional
inner-product domain admits operator-norm continuous characteristic adjoints,
Gram retractions and orthogonal range projections, all for the original given
norms. The witnesses are exactly those displayed in `gramFamily_properties`. -/
theorem exists_gramFamily (f : X → E →L[K] F)
    (hjoint : Continuous (fun p : X × E => f p.1 p.2))
    (hinj : ∀ x : X, Function.Injective (f x)) :
    ∃ (g r : X → F →L[K] E) (P : X → F →L[K] F),
      (∀ (x : X) (v : E) (w : F), inner K (f x v) w = inner K v (g x w)) ∧
      (∀ x : X, r x = (Ring.inverse ((g x).comp (f x))).comp (g x)) ∧
      (∀ x : X, P x = (f x).comp (r x)) ∧
      Continuous g ∧ Continuous r ∧ Continuous P ∧
      (∀ x : X, (r x).comp (f x) = ContinuousLinearMap.id K E) ∧
      ∀ x : X,
        (P x).comp (P x) = P x ∧
        LinearMap.range ((P x).toLinearMap) = LinearMap.range ((f x).toLinearMap) ∧
        (∀ u v : F, inner K (P x u) v = inner K u (P x v)) ∧
        LinearMap.ker ((P x).toLinearMap) =
          (LinearMap.range ((f x).toLinearMap)).orthogonal ∧
        ∀ (v : E) (w : F), inner K (f x v) (w - P x w) = 0 := by
  let g : X → F →L[K] E := fun x => adjointMap (f x)
  let r : X → F →L[K] E := fun x => inverseGramComp (f x) (g x)
  let P : X → F →L[K] F := fun x => (f x).comp (r x)
  exact ⟨g, r, P, gramFamily_properties f hjoint hinj⟩

end ContinuousLinearMap
