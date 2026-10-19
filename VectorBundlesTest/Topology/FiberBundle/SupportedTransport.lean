/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.FiberBundle.SupportedTransport
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Supported rescaling in a real line bundle

Use the product-bundle chart with fiber coordinate `exp(b) * v`, restricted to
`-2 < b < 3`. The base maps are `x` and `x + max 0 (1-x²)`. They agree outside
`[-1,1]`, whose images lie in the chart. Retaining the chart coordinate therefore
rescales a fiber by `exp(-max 0 (1-x²))`. Away from the chart the same construction
fixes the original total-space point. The empty supporting subset gives a zero
step.
-/

-- These examples are private witnesses rather than an exported fixture API.
set_option linter.privateModule false

open Bundle Set

namespace Bundle.Trivialization.SupportedTransportExamples

@[reducible] private noncomputable def E := Bundle.Trivial ℝ ℝ

private theorem scaledCoordinates_left_inv :
    Function.LeftInverse (fun z : ℝ × ℝ ↦ (z.1, Real.exp (-z.1) * z.2))
      (fun z : ℝ × ℝ ↦ (z.1, Real.exp z.1 * z.2)) := by
  intro z
  ext <;> simp [← mul_assoc, ← Real.exp_add]

private theorem scaledCoordinates_right_inv :
    Function.RightInverse (fun z : ℝ × ℝ ↦ (z.1, Real.exp (-z.1) * z.2))
      (fun z : ℝ × ℝ ↦ (z.1, Real.exp z.1 * z.2)) := by
  intro z
  ext <;> simp [← mul_assoc, ← Real.exp_add]

private theorem scaledCoordinates_continuous :
    Continuous (fun z : ℝ × ℝ ↦ (z.1, Real.exp z.1 * z.2)) := by fun_prop

private theorem scaledCoordinates_symm_continuous :
    Continuous (fun z : ℝ × ℝ ↦ (z.1, Real.exp (-z.1) * z.2)) := by fun_prop

private noncomputable def scaledCoordinates : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, Real.exp z.1 * z.2)
  invFun z := (z.1, Real.exp (-z.1) * z.2)
  left_inv := scaledCoordinates_left_inv
  right_inv := scaledCoordinates_right_inv
  continuous_toFun := scaledCoordinates_continuous
  continuous_invFun := scaledCoordinates_symm_continuous

private theorem scaledChart_source_eq :
    (((Bundle.Trivial.homeomorphProd ℝ ℝ).trans scaledCoordinates).toOpenPartialHomeomorph).source =
      (π ℝ E) ⁻¹' univ := rfl

private theorem scaledChart_target_eq :
    (((Bundle.Trivial.homeomorphProd ℝ ℝ).trans scaledCoordinates).toOpenPartialHomeomorph).target =
      univ ×ˢ univ := by simp

private theorem scaledChart_proj_toFun (z : TotalSpace ℝ E) (_hz : z ∈ univ) :
    (((Bundle.Trivial.homeomorphProd ℝ ℝ).trans scaledCoordinates).toOpenPartialHomeomorph z).1 =
      z.proj := rfl

private noncomputable def scaledChart : Trivialization ℝ (π ℝ E) :=
  ({ toOpenPartialHomeomorph :=
        ((Bundle.Trivial.homeomorphProd ℝ ℝ).trans scaledCoordinates).toOpenPartialHomeomorph
     baseSet := univ
     open_baseSet := isOpen_univ
     source_eq := scaledChart_source_eq
     target_eq := scaledChart_target_eq
     proj_toFun := scaledChart_proj_toFun } : Trivialization ℝ (π ℝ E)).restrOpen
    (Ioo (-2) 3) isOpen_Ioo

private theorem scaledChart_apply (z : TotalSpace ℝ E) :
    scaledChart z = (z.proj, Real.exp z.proj * z.2) := rfl

private noncomputable def f₀ : C(ℝ, ℝ) := ContinuousMap.id ℝ

private theorem f₁_continuous : Continuous (fun x : ℝ ↦ x + max 0 (1 - x ^ 2)) := by
  fun_prop

private noncomputable def f₁ : C(ℝ, ℝ) where
  toFun x := x + max 0 (1 - x ^ 2)
  continuous_toFun := f₁_continuous

private noncomputable def K : Set ℝ := Icc (-1) 1

private theorem agree_off : EqOn (f₀ : ℝ → ℝ) f₁ Kᶜ := by
  intro x hx
  change x = x + max 0 (1 - x ^ 2)
  have hn : x ∉ Icc (-1 : ℝ) 1 := hx
  have hs : 1 ≤ x ^ 2 := by
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  rw [max_eq_left (by linarith : 1 - x ^ 2 ≤ 0), add_zero]

private theorem f₀_mapsTo : MapsTo f₀ K scaledChart.baseSet := by
  intro x hx
  change x ∈ Icc (-1 : ℝ) 1 at hx
  change x ∈ univ ∩ Ioo (-2 : ℝ) 3
  exact ⟨mem_univ _, by constructor <;> linarith [hx.1, hx.2]⟩

private theorem f₁_mapsTo : MapsTo f₁ K scaledChart.baseSet := by
  intro x hx
  change x ∈ Icc (-1 : ℝ) 1 at hx
  change x + max 0 (1 - x ^ 2) ∈ univ ∩ Ioo (-2 : ℝ) 3
  refine ⟨mem_univ _, ?_, ?_⟩
  · linarith [le_max_left (0 : ℝ) (1 - x ^ 2), hx.1]
  · have hmax : max 0 (1 - x ^ 2) ≤ 1 := max_le (by norm_num) (by nlinarith [sq_nonneg x])
    linarith [hx.2]

private noncomputable def transport :
    TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E) ≃ₜ TotalSpace ℝ ((f₁ : ℝ → ℝ) *ᵖ E) :=
  scaledChart.supportedPullbackHomeomorph f₀ f₁ K isClosed_Icc agree_off
    f₀_mapsTo f₁_mapsTo

/-- Retaining `exp(b) * v` gives a nonconstant fiber rescaling. -/
private theorem transport_apply (x v : ℝ) :
    transport (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E)) =
      ⟨x, Real.exp (-max 0 (1 - x ^ 2)) * v⟩ := by
  have hp : (transport (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))).proj = x :=
    scaledChart.supportedPullbackHomeomorph_proj f₀ f₁ K isClosed_Icc agree_off
      f₀_mapsTo f₁_mapsTo _
  let w : ℝ := (transport (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))).2
  by_cases hx : x ∈ K
  · have hc := congrArg Prod.snd
      (scaledChart.supportedPullbackHomeomorph_chart f₀ f₁ K isClosed_Icc agree_off
        f₀_mapsTo f₁_mapsTo (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))
        ⟨f₀_mapsTo hx, f₁_mapsTo hx⟩)
    simp only [scaledChart_apply, Pullback.lift] at hc
    change Real.exp (f₁ (transport ⟨x, v⟩).proj) * w =
      Real.exp (f₀ x) * v at hc
    rw [hp] at hc
    change Real.exp (x + max 0 (1 - x ^ 2)) * w = Real.exp x * v at hc
    have hv : w =
        Real.exp (-max 0 (1 - x ^ 2)) * v := by
      apply mul_left_cancel₀ (Real.exp_ne_zero (x + max 0 (1 - x ^ 2)))
      rw [hc, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    exact TotalSpace.ext hp (heq_of_eq hv)
  · have heq := agree_off hx
    change x = x + max 0 (1 - x ^ 2) at heq
    have hm : max 0 (1 - x ^ 2) = 0 := by linarith
    rw [hm]
    simp only [neg_zero, Real.exp_zero, one_mul]
    exact scaledChart.supportedPullbackHomeomorph_apply_of_notMem f₀ f₁ K isClosed_Icc
      agree_off f₀_mapsTo f₁_mapsTo (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E)) hx

private theorem scaledChart_isLinear : scaledChart.IsLinear ℝ := by
  constructor
  intro b hb
  change IsLinearMap ℝ (fun v : ℝ ↦ Real.exp b * v)
  constructor
  · intro x y
    exact mul_add _ _ _
  · intro c x
    change Real.exp b * (c * x) = c * (Real.exp b * x)
    ring

/-- The supported rescaling is linear on each fiber. -/
private theorem transport_isLinear (a : ℝ) :
    IsLinearMap ℝ (fun v : ℝ ↦
      (transport (⟨a, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))).2) := by
  let : scaledChart.IsLinear ℝ := scaledChart_isLinear
  exact scaledChart.supportedPullbackHomeomorph_isLinearMap f₀ f₁ K isClosed_Icc
    agree_off f₀_mapsTo f₁_mapsTo a

/-- At zero the fiber coordinate changes, rather than merely its presentation. -/
private theorem transport_nontrivial :
    (transport (⟨0, (1 : ℝ)⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))).2 = Real.exp (-1) ∧
      (transport (⟨0, (1 : ℝ)⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))).2 ≠ (1 : ℝ) := by
  rw [transport_apply]
  change Real.exp (-max 0 (1 - (0 : ℝ) ^ 2)) * 1 = Real.exp (-1) ∧
    Real.exp (-max 0 (1 - (0 : ℝ) ^ 2)) * 1 ≠ 1
  norm_num only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    mul_one, eq_self, true_and]
  exact ne_of_lt (Real.exp_lt_one_iff.mpr (by norm_num))

/-- The chart is not global, yet transport fixes points beyond its base set. -/
private theorem outside_chart_identity :
    (4 : ℝ) ∉ scaledChart.baseSet ∧
      Pullback.lift f₁ (transport (⟨4, (2 : ℝ)⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E))) =
        Pullback.lift f₀ (⟨4, (2 : ℝ)⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E)) := by
  constructor
  · change (4 : ℝ) ∉ univ ∩ Ioo (-2 : ℝ) 3
    norm_num
  · exact scaledChart.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K isClosed_Icc
      agree_off f₀_mapsTo f₁_mapsTo _ (by change (4 : ℝ) ∉ Icc (-1 : ℝ) 1; norm_num)

private theorem empty_mapsTo : MapsTo f₀ (∅ : Set ℝ) scaledChart.baseSet := by
  exact mapsTo_empty _ _

/-- Empty support allows a base map that is not contained in the chart. -/
private theorem empty_support_apply (x v : ℝ) :
    scaledChart.supportedPullbackHomeomorph f₀ f₀ ∅ isClosed_empty
        (fun _ _ ↦ rfl) empty_mapsTo empty_mapsTo
        (⟨x, v⟩ : TotalSpace ℝ ((f₀ : ℝ → ℝ) *ᵖ E)) = ⟨x, v⟩ := by
  rw [scaledChart.supportedPullbackHomeomorph_refl]
  rfl

end Bundle.Trivialization.SupportedTransportExamples
