/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier contributors
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Adjoint
public import VectorBundlesTest.CompleteDomainAdjoint
import Mathlib.Tactic.NormNum

/-!
# Composition of real-to-complex adjoints

Precomposing the real-to-complex line with multiplication by two composes
its adjoint with multiplication by two on the left.
-/

@[expose] public section

namespace CompleteDomainAdjoint

/-- Doubling before the line of slope one gives adjoint value four at `1 + I`. -/
theorem adjointMap_complexLine_comp_two_one_add_I :
    ContinuousLinearMap.adjointMap
      ((complexLine 1).comp ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
      (1 + Complex.I) = 4 := by
  rw [ContinuousLinearMap.adjointMap_comp_of_isAdjointPair
    (complexLine 1) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (complexLinePartner 1) (complexLine_isAdjointPair 1)]
  norm_num [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjointMap_id, complexLinePartner]

end CompleteDomainAdjoint
