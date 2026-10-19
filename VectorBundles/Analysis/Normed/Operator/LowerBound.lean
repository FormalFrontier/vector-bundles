/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Lower bounds for perturbations of continuous linear maps

A positive lower bound for a continuous linear map persists under sufficiently small
operator-norm perturbations. Consequently, a family continuous at one parameter has a
uniform positive lower bound on an open neighborhood of that parameter.

The perturbation estimate uses Mathlib's `AntilipschitzWith.add_sub_lipschitzWith`
and the operator-norm Lipschitz bound. Neither completeness nor finite dimensionality
is needed, and the parameter space is an arbitrary topological space.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

universe uκ uC uG uB

namespace ContinuousLinearMap

variable {κ : Type uκ} {C : Type uC} {G : Type uG}
  [NontriviallyNormedField κ]
  [SeminormedAddCommGroup C] [SeminormedAddCommGroup G]
  [NormedSpace κ C] [NormedSpace κ G]

/-- An operator-norm perturbation of size less than `c / 2` preserves the lower
bound `c / 2`, provided the original map has lower bound `c > 0`. -/
theorem half_mul_norm_le_of_norm_sub_lt {f g : C →L[κ] G} {c : ℝ}
    (hc : 0 < c) (hf : ∀ u, c * ‖u‖ ≤ ‖f u‖) (hgf : ‖g - f‖ < c / 2)
    (u : C) : c / 2 * ‖u‖ ≤ ‖g u‖ := by
  lift c to ℝ≥0 using hc.le
  have hf' : AntilipschitzWith c⁻¹ f := f.antilipschitz_of_bound fun v => by
    change ‖v‖ ≤ (c : ℝ)⁻¹ * ‖f v‖
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    simpa only [mul_comm] using hf v
  have hgf' : ‖g - f‖₊ < c := hgf.trans (half_lt_self hc)
  have hg : AntilipschitzWith (c - ‖g - f‖₊)⁻¹ g := by
    simpa only [inv_inv, ContinuousLinearMap.coe_coe] using
      hf'.add_sub_lipschitzWith (g - f).lipschitzWith
      (show ‖g - f‖₊ < (c⁻¹)⁻¹ by simpa only [inv_inv] using hgf')
  have hbound : ((c : ℝ) - ‖g - f‖) * ‖u‖ ≤ ‖g u‖ := by
    simpa only [inv_inv, NNReal.coe_sub hgf'.le, coe_nnnorm, map_zero,
      dist_zero_right] using hg.mul_le_dist u 0
  have hhalf : (c : ℝ) / 2 ≤ (c : ℝ) - ‖g - f‖ := by linarith
  exact (mul_le_mul_of_nonneg_right hhalf (norm_nonneg u)).trans hbound

/-- A family of continuous linear maps which is continuous at `b₀` and has a
positive lower bound there has a uniform positive lower bound on an open neighborhood
of `b₀`. The spaces may be seminormed, and the parameter space need not be metrizable. -/
theorem exists_isOpen_uniform_lower_bound {B : Type uB} [TopologicalSpace B]
    {A : B → C →L[κ] G} {b₀ : B} (hA : ContinuousAt A b₀) {c : ℝ}
    (hc : 0 < c) (h₀ : ∀ u, c * ‖u‖ ≤ ‖A b₀ u‖) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ U, ∀ u, δ * ‖u‖ ≤ ‖A b u‖ := by
  have hnear : ∀ᶠ b in 𝓝 b₀, ‖A b - A b₀‖ < c / 2 :=
    hA.eventually (eventually_norm_sub_lt (A b₀) (half_pos hc))
  obtain ⟨U, hU, hUopen, hb₀⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hUopen, hb₀, c / 2, half_pos hc, ?_⟩
  intro b hb u
  exact half_mul_norm_le_of_norm_sub_lt hc h₀ (hU hb) u

end ContinuousLinearMap
