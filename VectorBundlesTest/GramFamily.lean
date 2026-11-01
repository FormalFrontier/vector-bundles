/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.GramFamily

/-!
# Joint continuity of Gram-family witnesses

The retraction and orthogonal projection supplied by a continuous Gram family are
jointly continuous on the original normed spaces.
-/

@[expose] public section

universe uX uK uE uF

example (X : Type uX) (K : Type uK) (E : Type uE) (F : Type uF)
    [TopologicalSpace X] [RCLike K]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace K E] [InnerProductSpace K F]
    [CompleteSpace E] [FiniteDimensional K E]
    (f : X → (E →L[K] F))
    (hjoint : Continuous (fun p : X × E => f p.1 p.2))
    (hinj : ∀ x : X, Function.Injective (f x)) :
    ∃ r : X → (F →L[K] E),
      (∀ x : X, (r x).comp (f x) = ContinuousLinearMap.id K E) ∧
        Continuous (fun p : X × F => r p.1 p.2) := by
  obtain ⟨_, r, _, _, _, _, _, hr, _, hleft, _⟩ :=
    ContinuousLinearMap.exists_gramFamily f hjoint hinj
  refine ⟨r, hleft, ?_⟩
  exact (hr.comp continuous_fst).clm_apply continuous_snd

example (X : Type uX) (K : Type uK) (E : Type uE) (F : Type uF)
    [TopologicalSpace X] [RCLike K]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace K E] [InnerProductSpace K F]
    [CompleteSpace E] [FiniteDimensional K E]
    (f : X → (E →L[K] F))
    (hjoint : Continuous (fun p : X × E => f p.1 p.2))
    (hinj : ∀ x : X, Function.Injective (f x)) :
    ∃ P : X → (F →L[K] F),
      Continuous (fun p : X × F => P p.1 p.2) ∧
        ∀ x : X,
          (P x).comp (P x) = P x ∧
          LinearMap.range ((P x).toLinearMap) = LinearMap.range ((f x).toLinearMap) ∧
          (∀ u v : F, inner K (P x u) v = inner K u (P x v)) ∧
          LinearMap.ker ((P x).toLinearMap) =
            (LinearMap.range ((f x).toLinearMap)).orthogonal ∧
          ∀ (v : E) (w : F), inner K (f x v) (w - P x w) = 0 := by
  obtain ⟨_, _, P, _, _, _, _, _, hP, _, hprops⟩ :=
    ContinuousLinearMap.exists_gramFamily f hjoint hinj
  refine ⟨P, ?_, hprops⟩
  exact (hP.comp continuous_fst).clm_apply continuous_snd
