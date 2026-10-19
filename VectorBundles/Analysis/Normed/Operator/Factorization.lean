/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
# Continuity of factorization coefficients

Suppose a family of linear maps `A b : F →ₗ[κ] G` is jointly continuous in the parameter
and the vector. If `j : C →ₗ[κ] F` is fixed and the compositions `A b ∘ j` have a common
positive lower norm bound, then any coefficients `T b x` satisfying
`A b (j (T b x)) = A b x` are jointly continuous.

The coefficient space and the target need only be seminormed additive groups with module
structures. The source needs only a topology and an algebraic module structure; neither
compatibility of its topology with the module operations nor continuity of `j` is required.
The coefficients need not be linear, and no continuity of them is assumed.

## Implementation notes

Fix coefficients at one parameter-vector pair and apply the lower bound to their difference
from the varying coefficients. The factorization identity bounds this difference by a
continuous residual that vanishes at the fixed pair. Norm squeeze proves continuity over
an arbitrary topological parameter space, without completeness or finite-dimensionality.

## References

The proof uses Mathlib's norm-squeeze and topological-group limit APIs, developed by
Patrick Massot, Johannes Hölzl, Mario Carneiro and Yaël Dillies.
-/

@[expose] public section

open Filter Topology

universe uκ uB uC uF uG

namespace LinearMap

variable {κ : Type uκ} [Semiring κ]
  {B : Type uB}
  {C : Type uC} [SeminormedAddCommGroup C] [Module κ C]
  {F : Type uF} [AddCommGroup F] [Module κ F]
  {G : Type uG} [SeminormedAddCommGroup G] [Module κ G]
  {A : B → F →ₗ[κ] G} {j : C →ₗ[κ] F} {T : B → F → C} {δ : ℝ}

/-- A uniform lower bound for `A b ∘ j` controls the difference of factorization
coefficients by a residual evaluated using a single member of the family. The lower-bound
constant need not be positive for this estimate. -/
theorem mul_norm_sub_le_of_factorization
    (hT : ∀ b x, A b (j (T b x)) = A b x)
    (hbound : ∀ b u, δ * ‖u‖ ≤ ‖A b (j u)‖)
    (b c : B) (x y : F) :
    δ * ‖T b x - T c y‖ ≤ ‖A b x - A b (j (T c y))‖ := by
  calc
    δ * ‖T b x - T c y‖ ≤ ‖A b (j (T b x - T c y))‖ := hbound b _
    _ = ‖A b x - A b (j (T c y))‖ := by
      rw [j.map_sub, (A b).map_sub, hT b x]

/-- Factorization coefficients are jointly continuous when `A` is jointly continuous and
`A b ∘ j` has a uniform positive lower norm bound. Neither continuity of `j` nor linearity
or continuity of the coefficients is assumed. The source and parameter space may have
arbitrary topologies. -/
theorem continuous_factorization_of_uniform_lower_bound
    [TopologicalSpace B] [TopologicalSpace F]
    (hA : Continuous (fun p : B × F ↦ A p.1 p.2))
    (hT : ∀ b x, A b (j (T b x)) = A b x)
    (hδ : 0 < δ) (hbound : ∀ b u, δ * ‖u‖ ≤ ‖A b (j u)‖) :
    Continuous (fun p : B × F ↦ T p.1 p.2) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ tendsto_sub_nhds_zero_iff.1 ?_
  have hres : Continuous (fun p : B × F ↦
      A p.1 p.2 - A p.1 (j (T p₀.1 p₀.2))) :=
    hA.sub (hA.comp (continuous_fst.prodMk continuous_const))
  have hlim : Tendsto (fun p : B × F ↦
      ‖A p.1 p.2 - A p.1 (j (T p₀.1 p₀.2))‖ / δ) (𝓝 p₀) (𝓝 0) := by
    simpa only [hT p₀.1 p₀.2, sub_self, norm_zero, zero_div] using
      (hres.norm.tendsto p₀).div_const δ
  refine squeeze_zero_norm (fun p ↦ ?_) hlim
  apply (le_div_iff₀ hδ).2
  simpa only [mul_comm] using
    mul_norm_sub_le_of_factorization hT hbound p.1 p₀.1 p.2 p₀.2

end LinearMap
