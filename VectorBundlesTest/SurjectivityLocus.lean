/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Algebra.Module.OpenMap
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Surjectivity of the scaled identity

The scaled identity on the real line is surjective exactly at nonzero parameters. Its proper,
nonempty surjectivity locus is open, and surjectivity persists near the identity parameter.
Zero-dimensional targets give the full locus; the zero family with nontrivial target gives the
empty locus.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace LinearMap.SurjectivityLocus

example : {b : ℝ | Function.Surjective
    ((b • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) : ℝ → ℝ)} = {0}ᶜ := by
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h hb
    subst b
    obtain ⟨v, hv⟩ := h 1
    simp at hv
  · intro hb y
    refine ⟨b⁻¹ * y, ?_⟩
    simp [smul_eq_mul, hb]

example : IsOpen {b : ℝ | Function.Surjective
    ((b • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) : ℝ → ℝ)} := by
  apply LinearMap.isOpen_setOf_surjective
  intro v
  have hmul : Continuous (fun b : ℝ ↦ b * v) := continuous_id.mul_const v
  simpa [smul_eq_mul] using hmul

example : ∀ᶠ b in 𝓝 (1 : ℝ),
    Function.Surjective
      ((b • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) : ℝ → ℝ) := by
  apply LinearMap.eventually_surjective_of_continuousAt
  · intro v
    have hmul : Continuous (fun b : ℝ ↦ b * v) := continuous_id.mul_const v
    simpa [smul_eq_mul] using hmul.continuousAt
  · intro y
    exact ⟨y, by simp⟩

example : {_b : ℝ | Function.Surjective (0 : ℝ →ₗ[ℝ] (Fin 0 → ℝ))} = Set.univ := by
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro y
  refine ⟨0, ?_⟩
  ext i
  exact Fin.elim0 i

example : {_b : ℝ | Function.Surjective (0 : ℝ →ₗ[ℝ] ℝ)} = ∅ := by
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨v, hv⟩ := h 1
  simp at hv

end LinearMap.SurjectivityLocus
