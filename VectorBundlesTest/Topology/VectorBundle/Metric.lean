/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Metric
public import VectorBundles.Topology.VectorBundle.MetricModel
public import VectorBundles.Topology.VectorBundle.FiniteSum
public import VectorBundles.Topology.VectorBundle.WeightedForm
public import VectorBundles.Analysis.InnerProductSpace.PositiveForm

/-!
# Clients of continuous bundle metrics

The real line over the real line, the usual sup-norm product model, and rank zero exercise
metric existence without an inner-product-space assumption on the model. Positivity is used
through the resulting metric's API, without computing the chosen metric.

The model's rank-zero formula, the trivial-bundle comparison for locally finite section sums,
and a scaled real positive form check the supporting constructions.
-/

-- These bundle clients are intentionally private and export no declarations.
set_option linter.privateModule false

@[expose] public section

noncomputable section

open Bundle Bornology

-- The ordinary real line bundle over a noncompact paracompact base.
private def trivialLineMetric : Bundle.ContinuousRiemannianMetric ℝ (Bundle.Trivial ℝ ℝ) :=
  VectorBundle.continuousRiemannianMetric ℝ (Bundle.Trivial ℝ ℝ)

-- This product retains its usual sup norm, not an inner-product norm.
private def trivialSupPlaneMetric :
    Bundle.ContinuousRiemannianMetric (ℝ × ℝ) (Bundle.Trivial ℝ (ℝ × ℝ)) :=
  VectorBundle.continuousRiemannianMetric (ℝ × ℝ) (Bundle.Trivial ℝ (ℝ × ℝ))

-- Rank zero is permitted.
private def trivialZeroMetric :
    Bundle.ContinuousRiemannianMetric (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) :=
  VectorBundle.continuousRiemannianMetric (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ))

-- The metric evaluates positively on a specified nonzero vector in every line fiber.
private theorem trivialLineMetric_pos_one (b : ℝ) :
    0 < (VectorBundle.continuousRiemannianMetric ℝ (Bundle.Trivial ℝ ℝ)).inner b 1 1 :=
  (VectorBundle.continuousRiemannianMetric ℝ (Bundle.Trivial ℝ ℝ)).pos b 1 one_ne_zero

-- In rank zero, the compatible model metric is the zero bilinear form.
private theorem ofFiniteDimensional_zero_inner (v w : Fin 0 → ℝ) :
    (Bundle.RiemannianMetric.ofFiniteDimensional (Fin 0 → ℝ)).inner () v w = 0 := by
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero, zero_apply]

section TrivialBundle

universe u𝕜 uB uF uι

variable (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type uι} {s : ι → B → F}

-- Projection to the model fiber recovers Mathlib's `continuous_finsum`.
include 𝕜 in
private theorem continuous_finsum_trivial_section (hs : ∀ i, Continuous (s i))
    (hlf : LocallyFinite fun i ↦ Function.support (s i)) :
    Continuous (fun b ↦ ∑ᶠ i, s i b) := by
  have hs' (i : ι) :
      Continuous (fun b ↦ (⟨b, s i b⟩ : TotalSpace F (Bundle.Trivial B F))) :=
    (Bundle.Trivial.homeomorphProd B F).symm.continuous.comp
      (continuous_id.prodMk (hs i))
  have hsum := VectorBundle.continuous_finsum_section 𝕜 hs' hlf
  exact continuous_snd.comp ((Bundle.Trivial.homeomorphProd B F).continuous.comp hsum)

end TrivialBundle

-- The ambient norm on `ℝ` is not the norm induced by this scaled form.
private theorem isVonNBounded_scaled_real_unit_sublevel :
    IsVonNBounded ℝ {x : ℝ | 2 * x * x < 1} := by
  let q : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    2 • ContinuousLinearMap.toSpanSingleton ℝ (ContinuousLinearMap.id ℝ ℝ)
  have hq (v w : ℝ) : q v w = 2 * v * w := by
    simp only [q, smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  have hsymm : ∀ v w, q v w = q w v := by
    intro v w
    simp only [hq]
    ring
  have hpos : ∀ v, v ≠ 0 → 0 < q v v := by
    intro v hv
    rw [hq, mul_assoc]
    exact mul_pos (by norm_num) (mul_self_pos.mpr hv)
  simpa only [hq] using q.isVonNBounded_unit_sublevel_of_posDef hsymm hpos
