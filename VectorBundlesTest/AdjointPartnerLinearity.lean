/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Analysis.InnerProductSpace.AdjointPair
import VectorBundlesTest.CompleteDomainAdjoint

/-! # Bundling the real-linear adjoint partner on the complex line -/

public section

open CompleteDomainAdjoint

/-- The given partner on the complex line bundles compatibly and is nonzero at `1 + I`. -/
example :
    Function.IsAdjointPair (inner ℝ) (inner ℝ)
      (complexLine 1) (complexLinePartner 1) ∧
    ∃ (L : ℂ →ₗ[ℝ] ℝ) (T : ℂ →L[ℝ] ℝ),
      T.toLinearMap = L ∧ (L : ℂ → ℝ) = (complexLinePartner 1 : ℂ → ℝ) ∧
      Function.IsAdjointPair (inner ℝ) (inner ℝ) (complexLine 1) T ∧
      T (1 + Complex.I) = 2 := by
  let h := complexLine_isAdjointPair 1
  refine ⟨h, h.toLinearMap, h.toContinuousLinearMap,
    h.toContinuousLinearMap_toLinearMap, h.coe_toLinearMap,
    h.isAdjointPair_toContinuousLinearMap, ?_⟩
  rw [h.toContinuousLinearMap_apply, complexLinePartner_apply]
  norm_num
