/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Operator.GramCoordinates
public import VectorBundles.Analysis.InnerProductSpace.Adjoint

/-!
# Gram normalization under a change of auxiliary space

Let `β : E →L[K] A` have a supplied adjoint `g`, and let `e : G ≃L[K] E`
have a supplied adjoint which is the underlying map of `h : E ≃L[K] G`.
An independently selected adjoint `g'` of `β.comp e.toContinuousLinearMap`
then gives the Gram congruence `g' β e = h (g β) e`.

When `g.comp β` is a unit, the Gram ring inverses transform in inverse
order by `e.symm` and `h.symm`. The separately evaluated Gram normalizations
transform by `e.symm`, and their ambient projections are equal. The change
`e` need not preserve inner products; in particular, its adjoint `h` need
not be `e.symm`.

The results use the original inner products, norms and topologies. Only
`E` is required to be normed; `G` and `A` may be seminormed. The comparison
of normalizations also holds without an adjoint equivalence `h`, provided
both Gram operators are units and the two adjoint identities are supplied.
This comparison is dimension-free and uses the retraction and kernel
characterizations of the constructed normalizers.

When `E` is finite-dimensional, the old Gram unit and the new adjoint
identity imply the new Gram unit. The normalization and ambient-operator
comparisons then require only the old unit. The unit step needs only a
normed space structure on `E`, not its inner product or the old adjoint
identity. No completeness hypothesis or construction of adjoints is asserted.
-/

public section

universe uK uE uG uA uF

namespace ContinuousLinearMap

variable {K : Type uK} [RCLike K]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {G : Type uG} [SeminormedAddCommGroup G] [InnerProductSpace K G]
variable {A : Type uA} [SeminormedAddCommGroup A] [InnerProductSpace K A]

private theorem adjointPartner_comp_equiv_eq
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g') :
    g' = h.toContinuousLinearMap.comp g := by
  ext a
  have hpartner : h.symm (g' a) = g a := by
    apply ext_inner_left K
    intro x
    calc
      inner K x (h.symm (g' a)) =
          inner K (e.symm x) (g' a) := by
        have he_apply := he.apply (e.symm x) (h.symm (g' a))
        change inner K (e (e.symm x)) (h.symm (g' a)) =
          inner K (e.symm x) (h (h.symm (g' a))) at he_apply
        simpa only [e.apply_symm_apply, h.apply_symm_apply] using he_apply
      _ = inner K (β x) a := by
        have hβe_apply := hβe.apply (e.symm x) a
        change inner K (β (e (e.symm x))) a =
          inner K (e.symm x) (g' a) at hβe_apply
        simpa only [e.apply_symm_apply] using hβe_apply.symm
      _ = inner K x (g a) := hβ.apply x a
  exact (h.apply_symm_apply (g' a)).symm.trans (congrArg h hpartner)

/-- Gram congruence for an independently selected adjoint after a change of
auxiliary space. The supplied adjoint of the change is not required to be its
inverse. -/
theorem gram_comp_equiv_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g') :
    g'.comp (β.comp e.toContinuousLinearMap) =
      h.toContinuousLinearMap.comp ((g.comp β).comp e.toContinuousLinearMap) := by
  rw [adjointPartner_comp_equiv_eq β g e h g' hβ he hβe]
  simp only [comp_assoc]

/-- A change of auxiliary space preserves the Gram-unit condition when the
changed Gram operator is formed with an independently selected adjoint. -/
theorem isUnit_gram_comp_equiv_iff_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g') :
    IsUnit (g'.comp (β.comp e.toContinuousLinearMap)) ↔ IsUnit (g.comp β) := by
  rw [gram_comp_equiv_of_isAdjointPair β g e h g' hβ he hβe]
  exact isUnit_comp_comp_equiv_iff (g.comp β) e h

/-- The Gram inverse in the continuous-linear endomorphism ring transforms
in inverse order under a change of auxiliary space. -/
theorem inverse_gram_comp_equiv_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    Ring.inverse (g'.comp (β.comp e.toContinuousLinearMap)) =
      e.symm.toContinuousLinearMap.comp
        ((Ring.inverse (g.comp β)).comp h.symm.toContinuousLinearMap) := by
  rw [gram_comp_equiv_of_isAdjointPair β g e h g' hβ he hβe]
  exact inverse_comp_comp_equiv_of_isUnit (g.comp β) e h hunit

/-- Transformation law for the constructed Gram normalization under a change of
auxiliary space, even when the changed adjoint is selected independently. -/
theorem inverseGramComp_comp_equiv_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    inverseGramComp (β.comp e.toContinuousLinearMap) g' =
      e.symm.toContinuousLinearMap.comp (inverseGramComp β g) := by
  rw [adjointPartner_comp_equiv_eq β g e h g' hβ he hβe]
  exact inverseGramComp_comp_equiv_of_isUnit β g e h hunit

/-- Pointwise transformation law for the constructed Gram normalization. -/
theorem inverseGramComp_comp_equiv_apply_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) (a : A) :
    inverseGramComp (β.comp e.toContinuousLinearMap) g' a =
      e.symm (inverseGramComp β g a) := by
  exact congrArg (fun L : A →L[K] G => L a)
    (inverseGramComp_comp_equiv_of_isAdjointPair β g e h g' hβ he hβe hunit)

/-- The ambient operator obtained from the constructed Gram normalization is
independent of the auxiliary coordinates and the independently selected adjoint. -/
theorem comp_inverseGramComp_comp_equiv_of_isAdjointPair
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (he : Function.IsAdjointPair (inner K) (inner K)
      e.toContinuousLinearMap h.toContinuousLinearMap)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    (β.comp e.toContinuousLinearMap).comp
        (inverseGramComp (β.comp e.toContinuousLinearMap) g') =
      β.comp (inverseGramComp β g) := by
  rw [adjointPartner_comp_equiv_eq β g e h g' hβ he hβe]
  exact comp_inverseGramComp_comp_equiv_of_isUnit β g e h hunit

private theorem adjointPartner_ker_imp
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (a : A) (ha : g' a = 0) : g a = 0 := by
  apply ext_inner_left K
  intro y
  calc
    inner K y (g a) = inner K (β y) a := (hβ.apply y a).symm
    _ = inner K (e.symm y) (g' a) := by
      have hβe_apply := hβe.apply (e.symm y) a
      change inner K (β (e (e.symm y))) a =
        inner K (e.symm y) (g' a) at hβe_apply
      simpa only [e.apply_symm_apply] using hβe_apply
    _ = inner K y 0 := by simp only [ha, inner_zero_right]

/-- The constructed normalizations for two supplied adjoint partners agree
contravariantly under any coefficient equivalence when both Gram operators are
units. No adjoint equivalence of the coefficient change is needed. -/
theorem inverseGramComp_comp_equiv_of_isAdjointPair_of_isUnit
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β))
    (hunit' : IsUnit (g'.comp (β.comp e.toContinuousLinearMap))) :
    inverseGramComp (β.comp e.toContinuousLinearMap) g' =
      e.symm.toContinuousLinearMap.comp (inverseGramComp β g) := by
  apply inverseGramComp_comp_equiv_of_ker_le_of_isUnit β g e g' ?_ hunit hunit'
  intro a ha
  exact adjointPartner_ker_imp β g e g' hβ hβe a ha

/-- With both Gram units given, two supplied adjoint partners yield the same
ambient operator after any continuous linear change of coefficient space. -/
theorem comp_inverseGramComp_comp_equiv_of_isAdjointPair_of_isUnit
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β))
    (hunit' : IsUnit (g'.comp (β.comp e.toContinuousLinearMap))) :
    (β.comp e.toContinuousLinearMap).comp
        (inverseGramComp (β.comp e.toContinuousLinearMap) g') =
      β.comp (inverseGramComp β g) := by
  rw [inverseGramComp_comp_equiv_of_isAdjointPair_of_isUnit
    β g e g' hβ hβe hunit hunit']
  ext a
  exact congrArg β (e.apply_symm_apply (inverseGramComp β g a))

private theorem isUnit_gram_comp_equiv_of_finiteDimensional
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace K F]
    [FiniteDimensional K F]
    (β : F →L[K] A) (g : A →L[K] F)
    (e : G ≃L[K] F) (g' : A →L[K] G)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    IsUnit (g'.comp (β.comp e.toContinuousLinearMap)) := by
  let T : G →L[K] G := g'.comp (β.comp e.toContinuousLinearMap)
  have hzero (x : G) (hx : T x = 0) : x = 0 := by
    have hinner : inner K (β (e x)) (β (e x)) = 0 := by
      calc
        inner K (β (e x)) (β (e x)) = inner K x (T x) :=
          hβe.apply x (β (e x))
        _ = 0 := by rw [hx, inner_zero_right]
    have hnorm : ‖β (e x)‖ = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 2)
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := K) (β (e x)), hinner,
        map_zero]
    have hT0 : (g.comp β) (e x) = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · calc
          ‖g (β (e x))‖ ≤ ‖g‖ * ‖β (e x)‖ := g.le_opNorm _
          _ = 0 := by rw [hnorm, mul_zero]
      · exact norm_nonneg _
    have hex : e x = 0 := by
      rcases hunit with ⟨u, hu⟩
      have hinv := congrArg (fun f : F →L[K] F => f (e x)) u.inv_val
      change (↑(u⁻¹) : F →L[K] F) ((u : F →L[K] F) (e x)) = e x at hinv
      rw [hu, hT0, map_zero] at hinv
      exact hinv.symm
    apply e.injective
    simpa only [map_zero] using hex
  have hT : Function.Injective T := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  -- Conjugate on the original normed finite-dimensional space, not on G.
  let D : F →L[K] F := e.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearMap)
  have hD : Function.Injective D := by
    intro x y hxy
    apply e.symm.injective
    apply hT
    apply e.injective
    exact hxy
  have hDbij : Function.Bijective D :=
    ⟨hD, (LinearMap.injective_iff_surjective).mp hD⟩
  let d : F ≃L[K] F :=
    (LinearEquiv.ofBijective D.toLinearMap hDbij).toContinuousLinearEquiv
  have hDunit : IsUnit D := by
    refine ⟨{
      val := D
      inv := d.symm.toContinuousLinearMap
      val_inv := ?_
      inv_val := ?_ }, rfl⟩
    · ext x
      change d (d.symm x) = x
      exact d.apply_symm_apply x
    · ext x
      change d.symm (d x) = x
      exact d.symm_apply_apply x
  exact (isUnit_comp_comp_equiv_iff T e.symm e).mp hDunit

/-- In finite dimension, the old Gram unit and two supplied adjoint identities
suffice for contravariance of the constructed normalization. The new Gram unit
is a consequence, not a hypothesis. -/
theorem inverseGramComp_comp_equiv_of_isAdjointPair_of_finiteDimensional
    [FiniteDimensional K E]
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    inverseGramComp (β.comp e.toContinuousLinearMap) g' =
      e.symm.toContinuousLinearMap.comp (inverseGramComp β g) := by
  exact inverseGramComp_comp_equiv_of_isAdjointPair_of_isUnit
    β g e g' hβ hβe hunit
    (isUnit_gram_comp_equiv_of_finiteDimensional β g e g' hβe hunit)

/-- With finite-dimensional normed coefficients, the ambient operator is
unchanged by a coefficient equivalence and two supplied adjoint partners,
assuming only the old Gram unit. The ambient space may be seminormed. -/
theorem comp_inverseGramComp_comp_equiv_of_isAdjointPair_of_finiteDimensional
    [FiniteDimensional K E]
    (β : E →L[K] A) (g : A →L[K] E)
    (e : G ≃L[K] E) (g' : A →L[K] G)
    (hβ : Function.IsAdjointPair (inner K) (inner K) β g)
    (hβe : Function.IsAdjointPair (inner K) (inner K)
      (β.comp e.toContinuousLinearMap) g')
    (hunit : IsUnit (g.comp β)) :
    (β.comp e.toContinuousLinearMap).comp
        (inverseGramComp (β.comp e.toContinuousLinearMap) g') =
      β.comp (inverseGramComp β g) := by
  rw [inverseGramComp_comp_equiv_of_isAdjointPair_of_finiteDimensional
    β g e g' hβ hβe hunit]
  ext a
  exact congrArg β (e.apply_symm_apply (inverseGramComp β g a))

end ContinuousLinearMap
