/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalAddition
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalComplement

/-!
# Orthogonal addition in the trivial plane bundle

The coordinate-line bundle is nonzero and proper, with its intrinsic trivial
bundle topology and embedding into the trivial Euclidean plane bundle.
Using its standard Hermitian metric, the addition homeomorphism sends the pair
of coordinate unit vectors, both nonzero, to their sum. This example uses the
prescribed forward formula. No separation condition on the base is used.
-/

@[expose] public section

open Bundle

namespace CoordinateLineBundle

variable (𝕜 : Type*) [RCLike 𝕜] (B : Type*) [TopologicalSpace B]

/-- On the proper coordinate line and its standard metric complement, total addition
sends two nonzero coordinate components to their sum. -/
theorem orthogonalAdditionHomeomorph_coordinate_units (b : B) :
    ∃ (s : line 𝕜)
      (c : (line 𝕜).orthogonalBilin
        ((ContinuousHermitianMetric.trivial 𝕜 B (EuclideanSpace 𝕜 (Fin 2))).inner b).toLinearMap₁₂),
      (s : EuclideanSpace 𝕜 (Fin 2)) = EuclideanSpace.single 0 1 ∧
      (c : EuclideanSpace 𝕜 (Fin 2)) = EuclideanSpace.single 1 1 ∧
      s ≠ 0 ∧ c ≠ 0 ∧
      (ContinuousHermitianMetric.trivial 𝕜 B
        (EuclideanSpace 𝕜 (Fin 2))).orthogonalAdditionHomeomorph
        (G := line 𝕜) (fun _ : B ↦ line 𝕜) (isEmbedding_inclusion 𝕜 B) ⟨b, s, c⟩ =
        TotalSpace.mk' (EuclideanSpace 𝕜 (Fin 2)) b
          (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) := by
  let s : line 𝕜 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hc : EuclideanSpace.single (1 : Fin 2) (1 : 𝕜) ∈
      (line 𝕜).orthogonalBilin
        ((ContinuousHermitianMetric.trivial 𝕜 B
          (EuclideanSpace 𝕜 (Fin 2))).inner b).toLinearMap₁₂ := by
    rw [standard_orthogonal 𝕜 B b]
    intro u hu
    simp only [EuclideanSpace.inner_single_right, one_mul, (mem_line 𝕜 u).mp hu, map_zero]
  let c := Subtype.mk (EuclideanSpace.single (1 : Fin 2) (1 : 𝕜)) hc
  refine ⟨s, c, rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun v : line 𝕜 ↦ (v : EuclideanSpace 𝕜 (Fin 2))) h
    simp [s] at h'
  · intro h
    have h' := congrArg Subtype.val h
    simp [c] at h'
  · exact ContinuousHermitianMetric.orthogonalAdditionHomeomorph_apply _ _ _ _

end CoordinateLineBundle
