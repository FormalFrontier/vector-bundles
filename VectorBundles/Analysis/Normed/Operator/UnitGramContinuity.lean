/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Ring.UnitContinuity
public import VectorBundles.Analysis.InnerProductSpace.GramRetraction
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuity of inverse Gram normalizers within units

For given continuous linear maps, convergence of both maps and eventual invertibility
of their Gram operator imply operator-norm convergence of the inverse Gram normalizer
and its ambient projection. Neither space needs to be separated or complete.
-/

@[expose] public section

noncomputable section

open Filter Topology

universe uK uH uA uX

namespace ContinuousLinearMap

section Algebra

variable {K : Type uK} {H : Type uH} {A : Type uA} [Semiring K]
  [AddCommMonoid H] [Module K H] [TopologicalSpace H]
  [AddCommMonoid A] [Module K A] [TopologicalSpace A]

/-- The inverse Gram normalizer is composition by the ring inverse of the Gram. -/
theorem inverseGramComp_eq_inverse_comp (Γ : H →L[K] A) (S : A →L[K] H) :
    inverseGramComp Γ S = (Ring.inverse (S.comp Γ)).comp S := by
  ext a
  simpa only [comp_apply] using inverseGramComp_apply Γ S a

end Algebra

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [NontriviallyNormedField K]
  [SeminormedAddCommGroup H] [NormedSpace K H]
  [SeminormedAddCommGroup A] [NormedSpace K A]

/-- Operator-norm convergence of inverse Gram normalizers along eventually unit Grams. -/
theorem tendsto_inverseGramComp_of_eventually_isUnit {X : Type uX} {l : Filter X}
    {Γ : X → H →L[K] A} {S : X → A →L[K] H}
    {Γ₀ : H →L[K] A} {S₀ : A →L[K] H}
    (hΓ : Tendsto Γ l (𝓝 Γ₀)) (hS : Tendsto S l (𝓝 S₀))
    (h₀ : IsUnit (S₀.comp Γ₀))
    (hunit : ∀ᶠ x in l, IsUnit ((S x).comp (Γ x))) :
    Tendsto (fun x => inverseGramComp (Γ x) (S x)) l
      (𝓝 (inverseGramComp Γ₀ S₀)) := by
  have hc : Continuous (fun p : (A →L[K] H) × (H →L[K] A) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  have hgram := (hc.tendsto (S₀, Γ₀)).comp (hS.prodMk_nhds hΓ)
  have hInv := Ring.tendsto_inverse_of_eventually_isUnit hgram h₀ hunit
  have hn : Continuous (fun p : (H →L[K] H) × (A →L[K] H) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  have ht : Tendsto (fun x => (Ring.inverse ((S x).comp (Γ x))).comp (S x)) l
      (𝓝 ((Ring.inverse (S₀.comp Γ₀)).comp S₀)) :=
    (hn.tendsto (Ring.inverse (S₀.comp Γ₀), S₀)).comp (hInv.prodMk_nhds hS)
  rw [← inverseGramComp_eq_inverse_comp Γ₀ S₀] at ht
  exact ht.congr' (Filter.Eventually.of_forall fun x =>
    (inverseGramComp_eq_inverse_comp (Γ x) (S x)).symm)

/-- Operator-norm convergence of the ambient Gram projections along eventually unit Grams. -/
theorem tendsto_gramProjection_of_eventually_isUnit {X : Type uX} {l : Filter X}
    {Γ : X → H →L[K] A} {S : X → A →L[K] H}
    {Γ₀ : H →L[K] A} {S₀ : A →L[K] H}
    (hΓ : Tendsto Γ l (𝓝 Γ₀)) (hS : Tendsto S l (𝓝 S₀))
    (h₀ : IsUnit (S₀.comp Γ₀))
    (hunit : ∀ᶠ x in l, IsUnit ((S x).comp (Γ x))) :
    Tendsto (fun x => (Γ x).comp (inverseGramComp (Γ x) (S x))) l
      (𝓝 (Γ₀.comp (inverseGramComp Γ₀ S₀))) := by
  have hc : Continuous (fun p : (H →L[K] A) × (A →L[K] H) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact (hc.tendsto (Γ₀, inverseGramComp Γ₀ S₀)).comp
    (hΓ.prodMk_nhds (tendsto_inverseGramComp_of_eventually_isUnit hΓ hS h₀ hunit))

variable {X : Type uX} [TopologicalSpace X]
  {Γ : X → H →L[K] A} {S : X → A →L[K] H} {x : X}

/-- Continuity within a set only needs Grams to be units eventually within that set. -/
theorem continuousWithinAt_inverseGramComp_of_eventually_isUnit {s : Set X}
    (hΓ : ContinuousWithinAt Γ s x) (hS : ContinuousWithinAt S s x)
    (h₀ : IsUnit ((S x).comp (Γ x)))
    (hunit : ∀ᶠ y in 𝓝[s] x, IsUnit ((S y).comp (Γ y))) :
    ContinuousWithinAt (fun y => inverseGramComp (Γ y) (S y)) s x :=
  tendsto_inverseGramComp_of_eventually_isUnit hΓ hS h₀ hunit

/-- Continuity of the ambient projection within a set of eventual unit Grams. -/
theorem continuousWithinAt_gramProjection_of_eventually_isUnit {s : Set X}
    (hΓ : ContinuousWithinAt Γ s x) (hS : ContinuousWithinAt S s x)
    (h₀ : IsUnit ((S x).comp (Γ x)))
    (hunit : ∀ᶠ y in 𝓝[s] x, IsUnit ((S y).comp (Γ y))) :
    ContinuousWithinAt (fun y => (Γ y).comp (inverseGramComp (Γ y) (S y))) s x :=
  tendsto_gramProjection_of_eventually_isUnit hΓ hS h₀ hunit

/-- Local continuity of the normalizer requires units only eventually at the point. -/
theorem continuousAt_inverseGramComp_of_eventually_isUnit
    (hΓ : ContinuousAt Γ x) (hS : ContinuousAt S x)
    (h₀ : IsUnit ((S x).comp (Γ x)))
    (hunit : ∀ᶠ y in 𝓝 x, IsUnit ((S y).comp (Γ y))) :
    ContinuousAt (fun y => inverseGramComp (Γ y) (S y)) x :=
  tendsto_inverseGramComp_of_eventually_isUnit hΓ hS h₀ hunit

/-- Local continuity of the ambient projection along eventually unit Grams. -/
theorem continuousAt_gramProjection_of_eventually_isUnit
    (hΓ : ContinuousAt Γ x) (hS : ContinuousAt S x)
    (h₀ : IsUnit ((S x).comp (Γ x)))
    (hunit : ∀ᶠ y in 𝓝 x, IsUnit ((S y).comp (Γ y))) :
    ContinuousAt (fun y => (Γ y).comp (inverseGramComp (Γ y) (S y))) x :=
  tendsto_gramProjection_of_eventually_isUnit hΓ hS h₀ hunit

/-- Globally unit Grams give continuity of the existing inverse Gram normalizer. -/
theorem continuous_inverseGramComp_of_isUnit (hΓ : Continuous Γ) (hS : Continuous S)
    (hunit : ∀ x, IsUnit ((S x).comp (Γ x))) :
    Continuous (fun x => inverseGramComp (Γ x) (S x)) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_inverseGramComp_of_eventually_isUnit hΓ.continuousAt hS.continuousAt
      (hunit x) (Filter.Eventually.of_forall hunit)

/-- Globally unit Grams give continuity of the ambient projection. -/
theorem continuous_gramProjection_of_isUnit (hΓ : Continuous Γ) (hS : Continuous S)
    (hunit : ∀ x, IsUnit ((S x).comp (Γ x))) :
    Continuous (fun x => (Γ x).comp (inverseGramComp (Γ x) (S x))) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_gramProjection_of_eventually_isUnit hΓ.continuousAt hS.continuousAt
      (hunit x) (Filter.Eventually.of_forall hunit)

end ContinuousLinearMap
