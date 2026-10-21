/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteEmbedding
public import Mathlib.Topology.UnitInterval

/-!
# Clients of finite trivial-bundle embeddings

The trivial real line bundle on the unit interval has a chosen embedding whose image
of one in each fiber is nonzero. The proof uses the base, fiber-application, and
injectivity APIs of the same chosen embedding, without computing its coordinates.
The zero-model and empty-base clients check the two elementary boundary cases.

The nonvanishing statement is public and refers to the chosen embedding itself.
The zero-model and empty-base statements remain private.
-/

noncomputable section

open Bundle

/-- The chosen finite trivial-bundle embedding of the real line over the unit interval
preserves each base point and sends the fiber vector one to a nonzero vector. -/
public theorem VectorBundle.finiteTrivialEmbeddingMap_unitInterval_one (b : unitInterval) :
    (VectorBundle.finiteTrivialEmbeddingMap ℝ ℝ (Bundle.Trivial unitInterval ℝ)
      (TotalSpace.mk' ℝ b 1)).1 = b ∧
      (VectorBundle.finiteTrivialEmbeddingMap ℝ ℝ (Bundle.Trivial unitInterval ℝ)
        (TotalSpace.mk' ℝ b 1)).2 ≠ 0 := by
  constructor
  · exact VectorBundle.finiteTrivialEmbeddingMap_fst ℝ ℝ
      (Bundle.Trivial unitInterval ℝ) (TotalSpace.mk' ℝ b 1)
  · have hinj := VectorBundle.finiteTrivialEmbeddingLinearMap_injective ℝ ℝ
      (Bundle.Trivial unitInterval ℝ) b
    have hne : VectorBundle.finiteTrivialEmbeddingLinearMap ℝ ℝ
        (Bundle.Trivial unitInterval ℝ) b 1 ≠ 0 := by
      intro h
      have h10 : (1 : ℝ) = 0 := hinj (by simpa only [map_zero] using h)
      exact one_ne_zero h10
    simpa only [VectorBundle.finiteTrivialEmbeddingMap_apply] using hne

private theorem zeroModel_map (b : unitInterval) (v : Fin 0 → ℝ) :
    VectorBundle.finiteTrivialEmbeddingMap ℝ (Fin 0 → ℝ)
      (Bundle.Trivial unitInterval (Fin 0 → ℝ))
      (TotalSpace.mk' (Fin 0 → ℝ) b v) = (b, 0) := by
  rw [VectorBundle.finiteTrivialEmbeddingMap_apply]
  have hv : v = 0 := Subsingleton.elim _ _
  simp only [hv, map_zero]

private theorem emptyBase_range :
    Set.range (VectorBundle.finiteTrivialEmbeddingMap ℝ ℝ
      (Bundle.Trivial Empty ℝ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨p, _⟩
  exact p.proj.elim
