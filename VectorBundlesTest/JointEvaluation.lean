/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Module.JointEvaluation
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# A varying family of rational projections

The maps `P t (x, y) = (x, t * x)` on the given supremum-norm product `ℚ × ℚ` are
nonzero proper projections and vary with `t`. Joint continuity gives operator-norm
continuity through the finite-dimensional seminormed criterion, over the incomplete
field `ℚ`. The construction uses Mathlib's continuous linear projections and product.
-/

@[expose] public section

namespace ContinuousLinearMap

private def rationalProjection (t : ℚ) : (ℚ × ℚ) →L[ℚ] ℚ × ℚ :=
  (fst ℚ ℚ ℚ).prod (t • fst ℚ ℚ ℚ)

/-- On the original supremum-norm rational plane there is a nonconstant continuous family
of nonzero, nonsurjective idempotents. No scalar completeness is needed for the
operator-norm continuity obtained from joint evaluation. -/
theorem exists_continuous_rational_projections :
    ∃ P : ℚ → (ℚ × ℚ) →L[ℚ] ℚ × ℚ,
      Continuous P ∧
      (∀ t v, P t (P t v) = P t v) ∧
      (∀ t, P t ≠ 0 ∧ ¬ Function.Surjective (P t)) ∧
      P 0 ≠ P 1 := by
  refine ⟨rationalProjection, ?_, ?_, ?_, ?_⟩
  · apply (continuous_iff_continuous_uncurry_of_finiteDimensional
      (K := ℚ) (G := ℚ × ℚ) (A := ℚ × ℚ) (Z := ℚ)).2
    change Continuous (fun p : ℚ × (ℚ × ℚ) => (p.2.1, p.1 * p.2.1))
    exact continuous_snd.fst.prodMk (continuous_fst.mul continuous_snd.fst)
  · intro t v
    rfl
  · intro t
    constructor
    · intro h
      exact one_ne_zero (congrArg (fun T : (ℚ × ℚ) →L[ℚ] ℚ × ℚ => (T (1, 0)).1) h)
    · intro h
      obtain ⟨v, hv⟩ := h (0, 1)
      have hx : v.1 = 0 := congrArg Prod.fst hv
      have hy : t * v.1 = 1 := congrArg Prod.snd hv
      rw [hx, mul_zero] at hy
      exact zero_ne_one hy
  · intro h
    have h' := congrArg (fun T : (ℚ × ℚ) →L[ℚ] ℚ × ℚ => (T (1, 0)).2) h
    simp [rationalProjection] at h'

end ContinuousLinearMap
