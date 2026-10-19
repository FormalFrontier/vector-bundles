/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalProjection
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalAddition

/-!
# Orthogonal projections in the trivial plane bundle

For the nonzero proper first coordinate line over an arbitrary topological base,
the two total-space projections send the sum of the coordinate unit vectors to
its respective components. The intrinsic line and the ambient-induced complement
keep the topologies used by orthogonal addition. The coordinate-unit choices and their
nonvanishing follow from the orthogonal-addition example.
The projections are continuous by the inverse addition homeomorphism and the
canonical product topology.
-/

@[expose] public section

open Bundle

namespace CoordinateLineBundle

variable (𝕜 : Type*) [RCLike 𝕜] (B : Type*) [TopologicalSpace B]

/-- The two orthogonal total-space projections recover the nonzero coordinate units
from their sum in the trivial plane bundle. -/
theorem orthogonalProjectionsTotal_coordinate_units (b : B) :
    ∃ (s : line 𝕜)
      (c : (line 𝕜).orthogonalBilin
        ((ContinuousHermitianMetric.trivial 𝕜 B (EuclideanSpace 𝕜 (Fin 2))).inner b).toLinearMap₁₂),
      (s : EuclideanSpace 𝕜 (Fin 2)) = EuclideanSpace.single 0 1 ∧
      (c : EuclideanSpace 𝕜 (Fin 2)) = EuclideanSpace.single 1 1 ∧
      s ≠ 0 ∧ c ≠ 0 ∧
      (ContinuousHermitianMetric.trivial 𝕜 B
        (EuclideanSpace 𝕜 (Fin 2))).orthogonalProjectionTotal
        (G := line 𝕜) (fun _ : B ↦ line 𝕜) (isEmbedding_inclusion 𝕜 B)
        (TotalSpace.mk' (EuclideanSpace 𝕜 (Fin 2)) b
          (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)) =
          TotalSpace.mk' (line 𝕜) b s ∧
      (ContinuousHermitianMetric.trivial 𝕜 B
        (EuclideanSpace 𝕜 (Fin 2))).orthogonalComplementProjectionTotal
        (G := line 𝕜) (fun _ : B ↦ line 𝕜) (isEmbedding_inclusion 𝕜 B)
        (TotalSpace.mk' (EuclideanSpace 𝕜 (Fin 2)) b
          (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)) =
          TotalSpace.mk' (EuclideanSpace 𝕜
            (Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin 2)) -
              Module.finrank 𝕜 (line 𝕜)))) b c := by
  have h := orthogonalAdditionHomeomorph_coordinate_units 𝕜 B b
  obtain ⟨s, c, hs, hc, hns, hnc, _⟩ := h
  refine ⟨s, c, hs, hc, hns, hnc, ?_, ?_⟩
  · rw [ContinuousHermitianMetric.orthogonalProjectionTotal_apply, ← hs, ← hc]
    simp only [map_add, Submodule.projectionOnto_apply_left,
      Submodule.projectionOnto_apply_right, add_zero]
  · simpa only [hs, hc] using
      ContinuousHermitianMetric.orthogonalComplementProjectionTotal_apply_add
        (ContinuousHermitianMetric.trivial 𝕜 B (EuclideanSpace 𝕜 (Fin 2)))
        (G := line 𝕜) (fun _ : B ↦ line 𝕜) (isEmbedding_inclusion 𝕜 B) b s c

end CoordinateLineBundle
