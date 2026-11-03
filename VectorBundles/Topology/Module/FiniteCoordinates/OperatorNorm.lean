/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Continuity from finitely many evaluations

A uniform bound on the operator seminorm by finitely many evaluations makes continuity of an
operator-valued family equivalent to continuity of those evaluations. The source and target are
seminormed spaces over a nontrivially normed field; no completeness or separation is required.

## References

The forward implication uses Mathlib's bundled evaluation map `ContinuousLinearMap.apply`.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

universe u𝕜 uA uG uX

namespace ContinuousLinearMap

/-- If finitely many evaluations uniformly bound the operator seminorm, an operator-valued family
is continuous exactly when those evaluations are continuous. The bound is required for every
continuous linear map, so it also controls differences of values of the family. -/
theorem continuous_iff_apply_finset_of_opNorm_le
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {A : Type uA} [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
    {G : Type uG} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (s : Finset A) (C : ℝ≥0)
    (hbound : ∀ T : A →L[𝕜] G, ‖T‖ ≤ (C : ℝ) * ∑ v ∈ s, ‖T v‖)
    {X : Type uX} [TopologicalSpace X] (L : X → A →L[𝕜] G) :
    Continuous L ↔ ∀ v : A, v ∈ s → Continuous (fun x : X => L x v) := by
  classical
  constructor
  · intro hL v _
    exact (ContinuousLinearMap.apply 𝕜 G v).continuous.comp hL
  · intro hL
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    let r : X → ℝ := fun x => (C : ℝ) * ∑ v ∈ s, ‖L x v - L x₀ v‖
    have hr : Continuous r :=
      continuous_const.mul (continuous_finsetSum s fun v hv =>
        ((hL v hv).sub continuous_const).norm)
    have hr₀ : r x₀ = 0 := by simp [r]
    refine Metric.continuousAt_iff'.2 fun ε hε => ?_
    have hεr : ∀ᶠ x in 𝓝 x₀, dist (r x) 0 < ε := by
      simpa only [hr₀] using
        (Metric.continuousAt_iff'.1 (hr.continuousAt : ContinuousAt r x₀) ε hε)
    filter_upwards [hεr] with x hx
    have hxr : ‖L x - L x₀‖ ≤ r x := by
      simpa only [r, sub_apply] using hbound (L x - L x₀)
    calc
      dist (L x) (L x₀) = ‖L x - L x₀‖ := dist_eq_norm _ _
      _ ≤ r x := hxr
      _ ≤ |r x| := le_abs_self _
      _ = dist (r x) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε := hx

end ContinuousLinearMap
