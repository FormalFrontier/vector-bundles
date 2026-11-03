/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SumRange
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Sum coordinates for a moving complementary line

Over the real base, the source fibers are the range of the identity on `ℝ`, with
`VectorBundle.rangeTotalSpaceTopology` on their total space from the outset. The
encoder is `β b e = (e, 0)` and the retraction is `ρ b (x, y) = x + b * y`.
The residual range is the nonzero proper line spanned by `(-b, 1)`.

The examples use `Bundle.TotalSpace.sumRangeHomeomorph` with both phantom parameters
`ℝ` and the canonical fiberwise-product topology. They compute its forward and inverse
coordinates through the public evaluation lemmas. In particular the first summand retains
its given total-space topology; no separate topology on a kernel is supplied.
-/

open Bundle Topology

namespace MovingLine

noncomputable section

private abbrev E (_ : ℝ) := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).range

local instance sourceTopology : TopologicalSpace (TotalSpace ℝ (fun b => E b)) :=
  VectorBundle.rangeTotalSpaceTopology (F := ℝ)
    (fun _ : ℝ => (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

private def β (b : ℝ) : E b →ₗ[ℝ] ℝ × ℝ :=
  (LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.id : ℝ →ₗ[ℝ] ℝ).range.subtype

private def ρ (b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] E b :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).rangeRestrict.comp
    (LinearMap.fst ℝ ℝ ℝ + b • LinearMap.snd ℝ ℝ ℝ)

private theorem ρ_β (b : ℝ) (e : E b) : ρ b (β b e) = e := by
  apply Subtype.ext
  change (e : ℝ) + b * 0 = (e : ℝ)
  simp

private theorem continuous_source_graph :
    Continuous (fun z : TotalSpace ℝ (fun b => E b) => (z.proj, (z.snd : ℝ))) :=
  continuous_induced_dom

private theorem continuous_β_total :
    Continuous (fun z : TotalSpace ℝ (fun b => E b) => (z.proj, β z.proj z.snd)) :=
  continuous_source_graph.fst.prodMk
    (continuous_source_graph.snd.prodMk continuous_const)

private theorem continuous_ρ_total :
    Continuous (fun z : ℝ × (ℝ × ℝ) =>
      (TotalSpace.mk' ℝ z.1 (ρ z.1 z.2) : TotalSpace ℝ (fun b => E b))) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 + z.1 * z.2.2))
  exact continuous_fst.prodMk
    (continuous_snd.fst.add (continuous_fst.mul continuous_snd.snd))

private abbrev Q (b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  LinearMap.id - (β b).comp (ρ b)

private theorem Q_apply (b x y : ℝ) : Q b (x, y) = (-(b * y), y) := by
  apply Prod.ext
  · change x - (x + b * y) = -(b * y)
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
  · change y - 0 = y
    exact sub_zero y

private abbrev S (b : ℝ) := (Q b).range

private abbrev residualTopology : TopologicalSpace (TotalSpace ℝ (fun b => S b)) :=
  VectorBundle.rangeTotalSpaceTopology (F := ℝ) Q

private abbrev sumTopology :
    TopologicalSpace (TotalSpace (ℝ × ℝ) (fun b => E b × S b)) :=
  @FiberBundle.Prod.topologicalSpace ℝ ℝ (fun b => E b) ℝ (fun b => S b)
    sourceTopology residualTopology

attribute [local instance] residualTopology sumTopology

private def sourceValue (b v : ℝ) : E b := ⟨v, ⟨v, rfl⟩⟩

private def residualValue (b t : ℝ) : S b :=
  ⟨Q b (0, t), ⟨(0, t), rfl⟩⟩

private def coordinates :
    TotalSpace (ℝ × ℝ) (fun b => E b × S b) ≃ₜ ℝ × (ℝ × ℝ) :=
  Bundle.TotalSpace.sumRangeHomeomorph (F := ℝ) (G := ℝ)
    β ρ ρ_β continuous_β_total continuous_ρ_total

-- The source vector v plus the residual vector (-b * t, t) gives the expected sum.
example (b v t : ℝ) :
    coordinates (TotalSpace.mk' (ℝ × ℝ) b (sourceValue b v, residualValue b t)) =
      (b, (v - b * t, t)) := by
  rw [coordinates, Bundle.TotalSpace.sumRangeHomeomorph_apply_mk]
  change (b, (v, 0) + Q b (0, t)) = (b, (v - b * t, t))
  rw [Q_apply]
  simp only [Prod.mk_add_mk, zero_add, sub_eq_add_neg]

-- The inverse recovers the original source value and the prescribed residual ambient value.
example (b x y : ℝ) :
    let c := coordinates.symm (b, (x, y))
    ((c.snd.1 : ℝ), (c.snd.2 : ℝ × ℝ)) = (x + b * y, (-(b * y), y)) := by
  dsimp only
  rw [coordinates, Bundle.TotalSpace.sumRangeHomeomorph_symm_apply_mk]
  change (x + b * y, Q b (x, y)) = (x + b * y, (-(b * y), y))
  rw [Q_apply]

/-- A complementary line can be nonzero and proper, vary with the base, and differ from
its complementary endomorphism's kernel. -/
public theorem exists_moving_complementary_line :
    ∃ (q : ℝ → (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) (r : ℝ → (ℝ × ℝ) →ₗ[ℝ] ℝ),
      ∀ b : ℝ, (-b, 1) ∈ (q b).range ∧ (1, 0) ∉ (q b).range ∧
        q b (1, 0) = 0 ∧ r b (1, 0) = 1 ∧ (q 0).range ≠ (q 1).range := by
  refine ⟨Q, fun b => (LinearMap.id : ℝ →ₗ[ℝ] ℝ).range.subtype.comp (ρ b), ?_⟩
  intro b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(0, 1), ?_⟩
    simpa only [mul_one] using Q_apply b 0 1
  · rintro ⟨⟨x, y⟩, h⟩
    have hy : y = 0 := by
      simpa only [Q_apply] using congrArg Prod.snd h
    have hx : (0 : ℝ) = 1 := by
      simpa only [Q_apply, hy, mul_zero, neg_zero] using congrArg Prod.fst h
    exact zero_ne_one hx
  · rw [Q_apply]
    simp
  · change 1 + b * 0 = 1
    simp
  · intro h
    have hz : ((0 : ℝ), 1) ∈ (Q 0).range := by
      refine ⟨(0, 1), ?_⟩
      simpa only [zero_mul, neg_zero] using Q_apply 0 0 1
    rw [h] at hz
    rcases hz with ⟨⟨x, y⟩, hxy⟩
    have hy : y = 1 := by
      simpa only [Q_apply] using congrArg Prod.snd hxy
    have hx : (-1 : ℝ) = 0 := by
      simpa only [Q_apply, one_mul, hy] using congrArg Prod.fst hxy
    exact one_ne_zero (neg_eq_zero.mp hx)

end

end MovingLine
