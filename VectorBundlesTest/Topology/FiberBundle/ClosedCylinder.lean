/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinder
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Mismatched charts on a trivial real line bundle

Over `ℝ × [0,1]` use the coordinate `v` on the left piece and `(2+x²)v` on the
right. The original charts disagree at the seam, while the normalized right
chart and the glued trivialization have coordinate `v`. The seam change depends
on `x`, and the same construction also allows the cut at the left endpoint.

The chart families, their projection laws, and the global glued trivialization
form a public example of closed-cylinder gluing. Nonvanishing, continuity, and
concrete seam and endpoint checks remain private implementation details.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
* Mathlib's trivial real bundle and its restricted trivializations.
-/

open Bundle Set
open Bundle.Trivialization

namespace Bundle.Trivialization.ClosedCylinderExamples

/-- The closed unit interval of time parameters. -/
public abbrev Time := Set.Icc (0 : ℝ) 1

/-- The cylinder with real spatial coordinate and time in the closed unit interval. -/
public abbrev Base := ℝ × Time

/-- The trivial real line bundle over the cylinder. -/
public abbrev E := Bundle.Trivial Base ℝ

/-- The projection from the total space of the trivial real line bundle to the cylinder. -/
public abbrev proj : TotalSpace ℝ E → Base := π ℝ E

/-- The left restricted chart, with fiber coordinate `v` at times at most `c`. -/
public noncomputable def leftChart (c : Time) :
    (proj ⁻¹' {b : Base | b.2 ≤ c}) ≃ₜ {b : Base | b.2 ≤ c} × ℝ :=
  (Bundle.Trivial.trivialization Base ℝ).preimageHomeomorph
    (subset_univ {b : Base | b.2 ≤ c})

private theorem factor_ne_zero (x : ℝ) : 2 + x ^ 2 ≠ 0 :=
  ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg x))

/-- The right restricted chart, with fiber coordinate `(2 + x ^ 2) * v`
at times at least `c`. -/
public noncomputable def rightChart (c : Time) :
    (proj ⁻¹' {b : Base | c ≤ b.2}) ≃ₜ {b : Base | c ≤ b.2} × ℝ :=
  ((Bundle.Trivial.trivialization Base ℝ).preimageHomeomorph
    (subset_univ {b : Base | c ≤ b.2})).trans
    { toFun := fun w ↦ (w.1, (2 + w.1.val.1 ^ 2) * w.2)
      invFun := fun w ↦ (w.1, w.2 / (2 + w.1.val.1 ^ 2))
      left_inv := by
        intro w
        exact Prod.ext rfl (mul_div_cancel_left₀ w.2 (factor_ne_zero _))
      right_inv := by
        intro w
        refine Prod.ext (show w.1 = w.1 from rfl) ?_
        exact mul_div_cancel₀ w.2 (factor_ne_zero _)
      continuous_toFun := by
        exact continuous_fst.prodMk
          ((continuous_const.add (continuous_fst.subtype_val.fst.pow 2)).mul continuous_snd)
      continuous_invFun := by
        exact continuous_fst.prodMk
          (continuous_snd.div (continuous_const.add (continuous_fst.subtype_val.fst.pow 2))
            (fun w ↦ factor_ne_zero w.1.val.1)) }

/-- The left chart keeps the base point and the usual real fiber coordinate. -/
public theorem leftChart_apply (c : Time) (z : proj ⁻¹' {b : Base | b.2 ≤ c}) :
    leftChart c z = (⟨proj z.val, z.property⟩, z.val.2) := by
  exact (Bundle.Trivial.trivialization Base ℝ).preimageHomeomorph_apply _ z

/-- The right chart keeps the base point and scales the fiber coordinate by `2 + x ^ 2`. -/
public theorem rightChart_apply (c : Time) (z : proj ⁻¹' {b : Base | c ≤ b.2}) :
    rightChart c z = (⟨proj z.val, z.property⟩, (2 + z.val.proj.1 ^ 2) * z.val.2) := by
  exact congrArg (fun w : {b : Base | c ≤ b.2} × ℝ ↦
    (w.1, (2 + w.1.val.1 ^ 2) * w.2))
    ((Bundle.Trivial.trivialization Base ℝ).preimageHomeomorph_apply
      (subset_univ {b : Base | c ≤ b.2}) z)

/-- The left restricted chart lies over the original bundle projection. -/
public theorem leftChart_proj (c : Time)
    (z : proj ⁻¹' {b : Base | b.2 ≤ c}) : (leftChart c z).1.val = proj z.val := by
  rw [leftChart_apply]

/-- The right restricted chart lies over the original bundle projection. -/
public theorem rightChart_proj (c : Time)
    (z : proj ⁻¹' {b : Base | c ≤ b.2}) : (rightChart c z).1.val = proj z.val := by
  rw [rightChart_apply]

private theorem continuous_proj : Continuous proj := by
  exact (Bundle.Trivial.homeomorphProd Base ℝ).continuous.fst

/-- The global trivialization obtained by normalizing and gluing the two restricted charts. -/
public noncomputable def glued (c : Time) : Trivialization ℝ proj :=
  glueClosedCylinder c proj (leftChart c) (rightChart c)
    (leftChart_proj c) (rightChart_proj c) continuous_proj

/-- The glued trivialization is defined over the whole cylinder. -/
public theorem glued_baseSet (c : Time) : (glued c).baseSet = Set.univ := by
  exact glueClosedCylinder_baseSet c proj (leftChart c) (rightChart c)
    (leftChart_proj c) (rightChart_proj c) continuous_proj

private noncomputable def midpoint : Time := ⟨1 / 2, by norm_num⟩

/-- The original coordinates really disagree at a point of the common slice. -/
private theorem original_seam_mismatch :
    let z : TotalSpace ℝ E := ⟨((0 : ℝ), midpoint), 1⟩
    (leftChart midpoint ⟨z, by change midpoint ≤ midpoint; exact le_rfl⟩).2 = 1 ∧
      (rightChart midpoint ⟨z, by change midpoint ≤ midpoint; exact le_rfl⟩).2 = 2 ∧
      (leftChart midpoint ⟨z, by change midpoint ≤ midpoint; exact le_rfl⟩).2 ≠
        (rightChart midpoint ⟨z, by change midpoint ≤ midpoint; exact le_rfl⟩).2 := by
  norm_num [leftChart_apply, rightChart_apply]

/-- The seam change from right coordinates to left coordinates divides by `2 + x ^ 2`. -/
public theorem seam_change_apply (c : Time) (x v : ℝ) :
    closedCylinderCoordChange c proj (leftChart c) (rightChart c)
      (leftChart_proj c) (rightChart_proj c) x v = v / (2 + x ^ 2) := by
  let z : TotalSpace ℝ E := ⟨(x, c), v / (2 + x ^ 2)⟩
  have h := closedCylinderCoordChange_apply c proj (leftChart c) (rightChart c)
    (leftChart_proj c) (rightChart_proj c) x z rfl
  simpa only [leftChart_apply, rightChart_apply, z, mul_div_cancel₀ v (factor_ne_zero x)]
    using h

/-- Normalization corrects the right chart at all times, not just at the seam. -/
public theorem normalized_right_apply (c : Time) (z : proj ⁻¹' {b : Base | c ≤ b.2}) :
    (normalizeClosedCylinderRight c proj (leftChart c) (rightChart c)
      (leftChart_proj c) (rightChart_proj c) z).2 = z.val.2 := by
  rw [normalizeClosedCylinderRight_apply, rightChart_apply, seam_change_apply]
  exact mul_div_cancel_left₀ _ (factor_ne_zero _)

/-- The glued chart recovers the usual global coordinate on the trivial real line. -/
public theorem glued_apply (c : Time) (z : TotalSpace ℝ E) :
    glued c z = (z.proj, z.2) := by
  rcases le_total z.proj.2 c with hz | hz
  · rw [glued, glueClosedCylinder_apply_left _ _ _ _ _ _ _ _ hz, leftChart_apply]
  · rw [glued, glueClosedCylinder_apply_right _ _ _ _ _ _ _ _ hz,
      rightChart_apply, seam_change_apply, mul_div_cancel_left₀ _ (factor_ne_zero _)]

/-- The constructed global coordinate is fiberwise linear. -/
public theorem glued_isLinear (c : Time) :
    (glued c).IsLinear ℝ := by
  apply glueClosedCylinder_isLinear c (leftChart c) (rightChart c)
    (leftChart_proj c) (rightChart_proj c) continuous_proj
  · intro b hb
    simp only [leftChart_apply]
    change IsLinearMap ℝ (fun v : ℝ ↦ v)
    exact (LinearMap.id : ℝ →ₗ[ℝ] ℝ).isLinear
  · intro b hb
    simp only [rightChart_apply]
    change IsLinearMap ℝ (fun v : ℝ ↦ (2 + b.1 ^ 2) * v)
    exact ((2 + b.1 ^ 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).isLinear

/-- Cutting at zero is allowed even though the left time interval is a singleton. -/
private theorem glued_left_endpoint_apply (x v : ℝ) :
    glued ⟨0, by norm_num⟩ (⟨(x, ⟨1, by norm_num⟩), v⟩ : TotalSpace ℝ E) =
      ((x, ⟨1, by norm_num⟩), v) := by
  exact glued_apply _ _

end Bundle.Trivialization.ClosedCylinderExamples
