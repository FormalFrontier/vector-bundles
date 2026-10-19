/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.VectorBundle.FiniteEmbedding
import Mathlib.Topology.UnitInterval

/-!
# Clients of finite trivial-bundle embeddings

The trivial real line bundle on the unit interval has a chosen embedding whose image
of one in each fiber is nonzero. The proof uses the base, fiber-application, and
injectivity APIs of the same chosen embedding, without computing its coordinates.
The zero-model and empty-base clients check the two elementary boundary cases.

The declarations in this module are private clients rather than an exported API;
accordingly it does not open an exposed public section.
-/

-- These clients intentionally export no declarations or reducible definitions.
set_option linter.privateModule false

noncomputable section

open Bundle

private def intervalLineMap :
    C(TotalSpace ℝ (Bundle.Trivial unitInterval ℝ),
      unitInterval ×
        (Fin (VectorBundle.finiteTrivialEmbeddingCopies ℝ ℝ
          (Bundle.Trivial unitInterval ℝ)) → ℝ)) :=
  VectorBundle.finiteTrivialEmbeddingMap ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private theorem intervalLineMap_one (b : unitInterval) :
    (intervalLineMap (TotalSpace.mk' ℝ b 1)).1 = b ∧
      (intervalLineMap (TotalSpace.mk' ℝ b 1)).2 ≠ 0 := by
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
    simpa only [intervalLineMap, VectorBundle.finiteTrivialEmbeddingMap_apply] using hne

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
