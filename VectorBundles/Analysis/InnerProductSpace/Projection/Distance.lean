/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import VectorBundles.Analysis.InnerProductSpace.Projection.LinearMap

/-!
# Distance to the image of an orthogonal retraction

The residual of an orthogonal retraction is orthogonal to the image of its linear
map. Its norm is the distance to that image and is a 1-Lipschitz function of the
ambient vector. The Pythagorean error identity characterizes minimum error by
zero distance between image points in a seminormed ambient space. Membership in
the closure of the image is equivalent to zero residual norm. In a normed ambient
space, the image is closed and minimum error characterizes the retracted
coefficient. The coefficient module needs no topology or norm, and no
completeness assumption is required.
-/

@[expose] public section

open scoped NNReal

universe u v w

namespace LinearMap.IsOrthogonalRetraction

variable {K : Type u} [RCLike K]
variable {F : Type v} [AddCommGroup F] [Module K F]

section Seminormed

variable {A : Type w} [SeminormedAddCommGroup A] [InnerProductSpace K A]
variable {β : F →ₗ[K] A} {r : A →ₗ[K] F}

/-- The squared error splits into the squared residual and the squared image of
the coefficient difference. -/
theorem norm_sub_image_sq (h : β.IsOrthogonalRetraction r) (a : A) (v : F) :
    ‖a - β v‖ ^ 2 = ‖a - β (r a)‖ ^ 2 + ‖β (r a - v)‖ ^ 2 := by
  have hsum : a - β (r a) + β (r a - v) = a - β v := by
    rw [map_sub, sub_add_sub_cancel]
  simpa only [hsum, pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (a - β (r a)) (β (r a - v)) (h.residual_inner a (r a - v))

/-- The retracted image minimizes the distance to the image of the linear map. -/
theorem norm_sub_image_le (h : β.IsOrthogonalRetraction r) (a : A) (v : F) :
    ‖a - β (r a)‖ ≤ ‖a - β v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h.norm_sub_image_sq a v]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The residual norm is the distance to the image of the linear map. -/
theorem norm_sub_image_eq_infDist (h : β.IsOrthogonalRetraction r) (a : A) :
    ‖a - β (r a)‖ = Metric.infDist a (Set.range β) := by
  apply le_antisymm
  · apply (Metric.le_infDist (s := Set.range β) ⟨β (r a), ⟨r a, rfl⟩⟩).2
    rintro _ ⟨v, rfl⟩
    simpa only [dist_eq_norm] using h.norm_sub_image_le a v
  · simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := a) (s := Set.range β) ⟨r a, rfl⟩)

/-- A point lies in the closure of the image exactly when its residual norm vanishes. -/
theorem mem_closure_range_iff_norm_sub_image_eq_zero
    (h : β.IsOrthogonalRetraction r) (a : A) :
    a ∈ closure (Set.range β) ↔ ‖a - β (r a)‖ = 0 := by
  rw [h.norm_sub_image_eq_infDist a]
  exact Metric.mem_closure_iff_infDist_zero ⟨β 0, ⟨0, rfl⟩⟩

/-- The residual norm is a 1-Lipschitz function of the ambient vector. -/
theorem lipschitzWith_norm_sub_image (h : β.IsOrthogonalRetraction r) :
    LipschitzWith (1 : ℝ≥0) (fun a : A => ‖a - β (r a)‖) := by
  simpa only [h.norm_sub_image_eq_infDist] using
    (Metric.lipschitz_infDist_pt (Set.range β))

/-- A coefficient attains the minimum error exactly when its image is at zero
distance from the retracted image. -/
theorem norm_sub_image_eq_iff_dist_eq_zero (h : β.IsOrthogonalRetraction r) (a : A) (v : F) :
    ‖a - β v‖ = ‖a - β (r a)‖ ↔ dist (β v) (β (r a)) = 0 := by
  constructor
  · intro heq
    rw [dist_comm, dist_eq_norm, ← map_sub]
    apply sq_eq_zero_iff.mp
    have hsq := h.norm_sub_image_sq a v
    rw [heq] at hsq
    exact add_eq_left.mp hsq.symm
  · intro hdist
    have himage : ‖β (r a - v)‖ = 0 := by
      rw [map_sub, ← dist_eq_norm, dist_comm]
      exact hdist
    apply le_antisymm
    · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [h.norm_sub_image_sq a v, himage]
      simp
    · exact h.norm_sub_image_le a v

end Seminormed

section Normed

variable {A : Type w} [NormedAddCommGroup A] [InnerProductSpace K A]
variable {β : F →ₗ[K] A} {r : A →ₗ[K] F}

/-- The image of an orthogonal retraction is closed in a normed ambient space. -/
theorem isClosed_range (h : β.IsOrthogonalRetraction r) : IsClosed (Set.range β) := by
  apply isClosed_of_closure_subset
  intro a ha
  have hzero := (h.mem_closure_range_iff_norm_sub_image_eq_zero a).1 ha
  exact ⟨r a, (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm⟩

/-- In a normed ambient space, a coefficient attains the minimum error exactly
when it is the retracted coefficient. -/
theorem norm_sub_image_eq_iff (h : β.IsOrthogonalRetraction r) (a : A) (v : F) :
    ‖a - β v‖ = ‖a - β (r a)‖ ↔ v = r a := by
  rw [h.norm_sub_image_eq_iff_dist_eq_zero a v, dist_eq_zero]
  constructor
  · intro himage
    simpa only [h.left_inv] using congrArg r himage
  · rintro rfl
    rfl

end Normed

end LinearMap.IsOrthogonalRetraction
