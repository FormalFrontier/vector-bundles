/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.VectorBundle.FiniteComplement
import Mathlib.Topology.UnitInterval

/-!
# Clients of finite complementary bundles

The positive-rank trivial real line over the unit interval uses the chosen complement's
bundle structures and global linear trivialization. Its complement has a continuous zero
section. The vector `(1, 0)` has nonzero image,
its base point is preserved, and its image recovers the original vector under the inverse
fiberwise linear equivalence. The rank-zero case has zero complementary fibers.

These declarations are intentionally private: this module tests the public API without
adding another public API. The complement is constructed from finite model powers.
-/

set_option linter.privateModule false

noncomputable section

open Bundle

local notation "C" => VectorBundle.finiteComplement.fiber ℝ ℝ (Bundle.Trivial unitInterval ℝ)
local notation "G" => VectorBundle.finiteComplement.model ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private instance realLineComplementTopology : TopologicalSpace (TotalSpace G C) :=
  VectorBundle.finiteComplement.totalSpaceTopology ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private instance realLineComplementFiberBundle : FiberBundle G C :=
  VectorBundle.finiteComplement.fiberBundle ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private instance realLineComplementVectorBundle : VectorBundle ℝ G C :=
  VectorBundle.finiteComplement.vectorBundle ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private theorem realLineComplement_zeroSection_continuous : Continuous (zeroSection G C) :=
  Bundle.Trivialization.continuous_zeroSection ℝ

private def realLineTrivialization :
    Trivialization (ℝ × G) (π (ℝ × G) (Bundle.Trivial unitInterval ℝ ×ᵇ C)) :=
  VectorBundle.finiteComplement.trivialization ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private instance realLineTrivializationIsLinear : realLineTrivialization.IsLinear ℝ :=
  VectorBundle.finiteComplement.trivialization_isLinear ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private theorem realLineTrivialization_fullBase : realLineTrivialization.baseSet = Set.univ :=
  VectorBundle.finiteComplement.trivialization_baseSet ℝ ℝ (Bundle.Trivial unitInterval ℝ)

private theorem realLine_image_ne_zero (b : unitInterval) :
    (realLineTrivialization ⟨b, (1, 0)⟩).2 ≠ 0 := by
  let e := realLineTrivialization.linearEquivAt ℝ b
    (by simp only [realLineTrivialization_fullBase, Set.mem_univ])
  intro h
  have hz : e (1, 0) = e 0 := by
    simpa only [e, map_zero, Trivialization.linearEquivAt_apply] using h
  have hv := congrArg Prod.fst (e.injective hz)
  exact one_ne_zero hv

private theorem realLine_image_base (b : unitInterval) :
    (realLineTrivialization ⟨b, (1, 0)⟩).1 = b :=
  realLineTrivialization.coe_fst' (by simp only [realLineTrivialization_fullBase, Set.mem_univ])

private theorem realLine_image_inverse (b : unitInterval) :
    (realLineTrivialization.linearEquivAt ℝ b
      (by simp only [realLineTrivialization_fullBase, Set.mem_univ])).symm
      (realLineTrivialization ⟨b, (1, 0)⟩).2 = (1, 0) := by
  exact (realLineTrivialization.linearEquivAt ℝ b
    (by simp only [realLineTrivialization_fullBase, Set.mem_univ])).symm_apply_apply (1, 0)

private def rankZeroComplement (b : unitInterval) :
    Submodule ℝ (Fin (VectorBundle.finiteComplement.count ℝ (Fin 0 → ℝ)
      (Bundle.Trivial unitInterval (Fin 0 → ℝ))) → (Fin 0 → ℝ)) :=
  VectorBundle.finiteComplement.submodule ℝ (Fin 0 → ℝ)
    (Bundle.Trivial unitInterval (Fin 0 → ℝ)) b

private theorem rankZeroComplement_eq_bot (b : unitInterval) : rankZeroComplement b = ⊥ :=
  Subsingleton.elim _ _
