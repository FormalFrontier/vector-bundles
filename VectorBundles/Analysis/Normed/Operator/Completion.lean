/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Operator norms and completion

A continuous linear map between seminormed spaces has the same operator norm as its map
between their completions, with the scalar field unchanged. The proof uses Mathlib's
Lipschitz completion map and operator-norm bounds.
-/

@[expose] public section

universe uK uA uG

namespace ContinuousLinearMap

variable {K : Type uK} [kK : NontriviallyNormedField K]
  {A : Type uA} [sA : SeminormedAddCommGroup A]
  {G : Type uG} [sG : SeminormedAddCommGroup G]
  [nA : @NormedSpace K A kK.toNormedField sA]
  [nG : @NormedSpace K G kK.toNormedField sG]

/-- Completing a continuous linear map preserves its operator norm over the same scalar field.
The domain and target may be nonseparated seminormed spaces. -/
@[simp]
theorem norm_completion
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    ‖T.completion‖ = ‖T‖ := by
  apply le_antisymm
  · have hT : LipschitzWith ⟨‖T‖, T.opNorm_nonneg⟩ T :=
      opNorm_le_iff_lipschitz.mp le_rfl
    have hTc : LipschitzWith ⟨‖T‖, T.opNorm_nonneg⟩ T.completion := by
      simpa only [coe_completion] using hT.completion_map
    exact opNorm_le_iff_lipschitz.mpr hTc
  · apply T.opNorm_le_bound (norm_nonneg T.completion)
    intro a
    simpa only [completion_apply_coe, UniformSpace.Completion.norm_coe] using
      T.completion.le_opNorm (a : UniformSpace.Completion A)

end ContinuousLinearMap
