/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalComplement
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A coordinate line in the trivial plane bundle

The first coordinate line has the inherited norm and subtype topology. Its
trivial bundle over an arbitrary topological base embeds in the trivial plane
bundle. The standard Hermitian metric requires no separation condition on the
base.
-/

@[expose] public section

open Bundle

namespace CoordinateLineBundle

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The first coordinate line in the Euclidean plane. -/
def line : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin 2)) :=
  (EuclideanSpace.projₗ (1 : Fin 2)).ker

@[simp]
theorem mem_line (v : EuclideanSpace 𝕜 (Fin 2)) : v ∈ line 𝕜 ↔ v 1 = 0 := Iff.rfl

/-- The first coordinate line is nonzero. -/
theorem line_ne_bot : line 𝕜 ≠ ⊥ := by
  intro h
  have hm : EuclideanSpace.single (0 : Fin 2) (1 : 𝕜) ∈ line 𝕜 := by simp
  simp [h] at hm

/-- The first coordinate line is proper. -/
theorem line_ne_top : line 𝕜 ≠ ⊤ := by
  intro h
  have hm : EuclideanSpace.single (1 : Fin 2) (1 : 𝕜) ∈ line 𝕜 := by rw [h]; trivial
  simp at hm

/-- The coordinate submodule has dimension one. -/
theorem finrank_line : Module.finrank 𝕜 (line 𝕜) = 1 := by
  have : Nontrivial (line 𝕜) := Submodule.nontrivial_iff_ne_bot.mpr (line_ne_bot 𝕜)
  have hpos : 0 < Module.finrank 𝕜 (line 𝕜) := Module.finrank_pos
  have hlt := Submodule.finrank_lt (line_ne_top 𝕜)
  simp only [finrank_euclideanSpace_fin] at hlt
  omega

variable (B : Type*) [TopologicalSpace B]

/-- The total inclusion of the trivial coordinate-line bundle is an embedding
for the product bundle topologies. -/
theorem isEmbedding_inclusion : Topology.IsEmbedding
    (fun p : TotalSpace (line 𝕜) (fun _ : B ↦ line 𝕜) ↦
      TotalSpace.mk' (EuclideanSpace 𝕜 (Fin 2))
        (E := Bundle.Trivial B (EuclideanSpace 𝕜 (Fin 2))) p.proj
        (p.2 : EuclideanSpace 𝕜 (Fin 2))) := by
  exact (Bundle.Trivial.homeomorphProd B (EuclideanSpace 𝕜 (Fin 2))).symm.isEmbedding.comp
    ((Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal).comp
      (Bundle.Trivial.homeomorphProd B (line 𝕜)).isEmbedding)

/-- The standard metric's sesquilinear complement agrees with the usual
pointwise orthogonal complement of the coordinate line. -/
theorem standard_orthogonal (b : B) :
    (line 𝕜).orthogonalBilin
      ((ContinuousHermitianMetric.trivial 𝕜 B (EuclideanSpace 𝕜 (Fin 2))).inner b).toLinearMap₁₂ =
      (line 𝕜).orthogonal :=
  Submodule.orthogonalBilin_innerSL (line 𝕜)

/-- The coordinate-line complement has rank one, as computed using the fiber
and vector bundle components of the orthogonal-bundle construction. -/
theorem finrank_orthogonal_line (b : B) : Module.finrank 𝕜 (line 𝕜).orthogonal = 1 := by
  let g := ContinuousHermitianMetric.trivial 𝕜 B (EuclideanSpace 𝕜 (Fin 2))
  let C := fun b ↦ (line 𝕜).orthogonalBilin (g.inner b).toLinearMap₁₂
  let H := EuclideanSpace 𝕜
    (Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin 2)) - Module.finrank 𝕜 (line 𝕜)))
  let : TopologicalSpace (TotalSpace H (fun b ↦ C b)) := TopologicalSpace.induced
    (fun p : TotalSpace H (fun b ↦ C b) ↦
      TotalSpace.mk' (EuclideanSpace 𝕜 (Fin 2))
        (E := Bundle.Trivial B (EuclideanSpace 𝕜 (Fin 2))) p.proj
        (p.2 : EuclideanSpace 𝕜 (Fin 2))) inferInstance
  let data := g.orthogonalBundle (G := line 𝕜) (fun _ ↦ line 𝕜) (isEmbedding_inclusion 𝕜 B)
  let : FiberBundle H (fun b ↦ C b) := data.1
  let : VectorBundle 𝕜 H (fun b ↦ C b) := data.2
  have h := VectorBundle.finrank_eq 𝕜 H (fun b ↦ C b) b
  change Module.finrank 𝕜
    ((line 𝕜).orthogonalBilin (g.inner b).toLinearMap₁₂) = Module.finrank 𝕜 H at h
  rw [show (line 𝕜).orthogonalBilin (g.inner b).toLinearMap₁₂ = (line 𝕜).orthogonal from
    standard_orthogonal 𝕜 B b] at h
  simpa [H, finrank_line] using h

end CoordinateLineBundle
