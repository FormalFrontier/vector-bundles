/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Section.Lift

/-!
# Prescribed values in the real trivial line bundle

The usual real trivial line over the real line has a constant section with value three,
constructed through the trivial-bundle equivalence. Its value at two is computed
independently of the section lift. The lift, its evaluation identity and evaluation
surjectivity are then used on the same bundle and prescribed value. Only values at the
chosen point are compared; no global equality with the constant section is asserted.

The empty base and the zero-dimensional model give two boundary cases.
-/

@[expose] public section

open VectorBundle

namespace ContinuousSectionLiftTest

noncomputable section

/-- The constant section of value three, obtained from the trivial-bundle equivalence. -/
def s0 : continuousSectionSubmodule ℝ ℝ (Bundle.Trivial ℝ ℝ) :=
  (LinearEquiv.symm (continuousSectionTrivialEquiv ℝ ℝ ℝ))
    (ContinuousMap.const ℝ (3 : ℝ))

/-- The independently constructed constant section has value three at two. -/
theorem realTrivialSection_value :
    continuousSectionEval (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) (2 : ℝ) s0 =
      (3 : ℝ) := by
  simp only [s0, continuousSectionEval_apply, continuousSectionTrivialEquiv_symm_apply,
    ContinuousMap.const_apply]

/-- Lifting three at two gives the prescribed value in the real trivial line. -/
theorem realTrivialLift_value :
    (continuousSectionLift (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ)
      (2 : ℝ) (3 : ℝ)).1 (2 : ℝ) = (3 : ℝ) :=
  continuousSectionLift_apply_self (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) 2 3

/-- The evaluation identity agrees with the constant section at the prescribed point. -/
theorem realTrivialEval_comp_lift_value :
    ((continuousSectionEval (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) (2 : ℝ)).comp
      (continuousSectionLift (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) (2 : ℝ)))
        (3 : ℝ) =
      continuousSectionEval (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) (2 : ℝ) s0 := by
  rw [continuousSectionEval_comp_lift, LinearMap.id_apply, realTrivialSection_value]

/-- Evaluation surjectivity supplies a section with the same nonzero prescribed value. -/
theorem realTrivialEval_surjective_value :
    ∃ s : continuousSectionSubmodule ℝ ℝ (Bundle.Trivial ℝ ℝ),
      continuousSectionEval (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) (2 : ℝ) s =
        (3 : ℝ) :=
  continuousSectionEval_surjective (𝕜 := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ) 2 3

/-- Every section of the real trivial line over an empty base is zero. -/
theorem emptyBase_section_eq_zero
    (s : continuousSectionSubmodule ℝ ℝ (Bundle.Trivial Empty ℝ)) : s = 0 := by
  apply Subtype.ext
  funext x
  exact Empty.elim x

/-- The lift of the unique value in a zero-dimensional fiber is the zero section. -/
theorem rankZeroLift_eq_zero :
    continuousSectionLift (𝕜 := ℝ) (F := Fin 0 → ℝ)
      (E := Bundle.Trivial ℝ (Fin 0 → ℝ)) (2 : ℝ) (0 : Fin 0 → ℝ) = 0 :=
  map_zero _

end
end ContinuousSectionLiftTest
