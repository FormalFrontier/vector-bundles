/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.AdjointPair

/-!
# Joint continuity of given adjoint partners

For two given inner-product adjoint pairs, input variation and operator variation
control the distance between values of their unbundled partners. Consequently,
an operator-norm-continuous family of continuous linear maps with given raw
adjoint partners has a jointly continuous evaluation map.

The spaces carry their given seminormed inner-product structures. No linearity,
continuity, uniqueness, or zero preservation of the raw partners is assumed.
Zero norm bounds give zero pseudodistances, not equality of values. These results
extend the fixed-map norm and Lipschitz estimates of
`Function.IsAdjointPair.norm_apply_le` and `Function.IsAdjointPair.lipschitzWith`;
they do not construct adjoints.
-/

@[expose] public section

open scoped Topology

universe uK uH uA uT

namespace Function.IsAdjointPair

variable {K : Type uK} {H : Type uH} {A : Type uA}
  [RCLike K] [SeminormedAddCommGroup H] [SeminormedAddCommGroup A]
  [InnerProductSpace K H] [InnerProductSpace K A]

/-- Two given adjoint pairs satisfy a mixed bound for input and operator variation. -/
theorem norm_sub_apply_le {Γ₁ Γ₂ : H →L[K] A} {S₁ S₂ : A → H}
    (h₁ : Function.IsAdjointPair (inner K) (inner K) Γ₁ S₁)
    (h₂ : Function.IsAdjointPair (inner K) (inner K) Γ₂ S₂)
    (y z : A) :
    ‖S₁ y - S₂ z‖ ≤ ‖Γ₁‖ * ‖y - z‖ + ‖Γ₁ - Γ₂‖ * ‖z‖ := by
  have h₁yz : ‖S₁ y - S₁ z‖ ≤ ‖Γ₁‖ * ‖y - z‖ := by
    simpa only [dist_eq_norm, coe_nnnorm] using
      h₁.lipschitzWith.dist_le_mul y z
  -- This is pointwise subtraction of raw functions, not linearity of either partner.
  have hΔ : Function.IsAdjointPair (inner K) (inner K)
      (Γ₁ - Γ₂) (fun w : A => S₁ w - S₂ w) :=
    h₁.inner_sub h₂
  have hΔz : ‖S₁ z - S₂ z‖ ≤ ‖Γ₁ - Γ₂‖ * ‖z‖ :=
    hΔ.inner_symm.norm_apply_le (S := Γ₁ - Γ₂) z
  calc
    ‖S₁ y - S₂ z‖ = ‖(S₁ y - S₁ z) + (S₁ z - S₂ z)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖S₁ y - S₁ z‖ + ‖S₁ z - S₂ z‖ := norm_add_le _ _
    _ ≤ ‖Γ₁‖ * ‖y - z‖ + ‖Γ₁ - Γ₂‖ * ‖z‖ := add_le_add h₁yz hΔz

/-- Given raw adjoint partners of an operator-norm-continuous family have a
jointly continuous evaluation map, in the given seminormed topologies. -/
theorem continuous_uncurry {T : Type uT} [TopologicalSpace T]
    {Γ : T → (H →L[K] A)} {S : T → A → H}
    (hΓ : Continuous Γ)
    (h : ∀ t, Function.IsAdjointPair (inner K) (inner K) (Γ t) (S t)) :
    Continuous (fun p : T × A => S p.1 p.2) := by
  have h_mixed (t s : T) (y z : A) :
      ‖S t y - S s z‖ ≤ ‖Γ t‖ * ‖y - z‖ + ‖Γ t - Γ s‖ * ‖z‖ :=
    (h t).norm_sub_apply_le (h s) y z
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let Q : T × A → ℝ := fun p =>
    ‖Γ p.1‖ * ‖p.2 - p₀.2‖ + ‖Γ p.1 - Γ p₀.1‖ * ‖p₀.2‖
  have hΓeval : Continuous (fun p : T × A => Γ p.1) :=
    hΓ.comp continuous_fst
  have hΓdiff : Continuous (fun p : T × A => Γ p.1 - Γ p₀.1) :=
    hΓeval.sub continuous_const
  have hQ : Continuous Q :=
    (hΓeval.norm.mul (continuous_snd.sub continuous_const).norm).add
      (hΓdiff.norm.mul continuous_const)
  have hQ_lim : Filter.Tendsto Q (𝓝 p₀) (𝓝 (0 : ℝ)) := by
    simpa only [Q, sub_self, norm_zero, mul_zero, zero_mul, add_zero] using
      (hQ.tendsto p₀)
  have hN_lim : Filter.Tendsto
      (fun p : T × A => ‖S p.1 p.2 - S p₀.1 p₀.2‖)
      (𝓝 p₀) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun p => norm_nonneg _) ?_ hQ_lim
    intro p
    exact h_mixed p.1 p₀.1 p.2 p₀.2
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hN_lim

end Function.IsAdjointPair
