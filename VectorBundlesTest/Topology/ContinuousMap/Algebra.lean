/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Ring.PUnit

/-!
# Tests for continuous-map linear product coordinates

Evaluation extensionality, varying scalar functions on a discrete two-point base,
and empty-base, empty-index and zero-ring boundaries.
-/

@[expose] public section

universe uX uI uR uM

namespace ContinuousMap

variable {I : Type uI} (R : Type uR) (X : Type uX) (M : I → Type uM)
  [TopologicalSpace X] [TopologicalSpace R] [Semiring R] [IsTopologicalSemiring R]
  [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, ContinuousAdd (M i)] [∀ i, ContinuousSMul R (M i)]

example (g h : ∀ i, C(X, M i))
    (hgh : ∀ x i, piLinearEquiv R X M g x i = piLinearEquiv R X M h x i) : g = h := by
  funext i
  ext x
  simpa only [piLinearEquiv_apply] using hgh x i

end ContinuousMap

noncomputable section

namespace CoordinateFunctions

/-- The discrete topology on the two-point base. -/
local instance boolTopologicalSpace : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩

/-- A continuous scalar function taking distinct values at the two base points. -/
def boolScalar : C(Bool, ℝ) :=
  ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

/-- Constant coordinate functions of a standard coordinate vector. -/
def coordinateFamily (j : Fin 2) : Fin 2 → C(Bool, ℝ) :=
  fun i => ContinuousMap.const Bool (if i = j then 1 else 0)

/-- A standard coordinate vector, constant as a function of the base. -/
def constantCoordinate (j : Fin 2) : C(Bool, Fin 2 → ℝ) :=
  ContinuousMap.const Bool (fun i => if i = j then 1 else 0)

@[simp]
theorem boolScalar_false : boolScalar false = 0 := rfl

@[simp]
theorem boolScalar_true : boolScalar true = 1 := rfl

theorem piLinearEquiv_coordinateFamily (j : Fin 2) :
    ContinuousMap.piLinearEquiv ℝ Bool (fun _ : Fin 2 => ℝ) (coordinateFamily j) =
      constantCoordinate j := by
  ext b i
  rfl

theorem boolScalar_smul_false (j : Fin 2) :
    (boolScalar • constantCoordinate j) false = 0 := by
  simp

theorem boolScalar_smul_true (j : Fin 2) :
    (boolScalar • constantCoordinate j) true = constantCoordinate j true := by
  simp

theorem constantCoordinate_self (j : Fin 2) : constantCoordinate j true j = 1 := by
  simp [constantCoordinate]

example (j : Fin 2) (b : Bool) (i : Fin 2) :
    ContinuousMap.piLinearEquiv ℝ Bool (fun _ : Fin 2 => ℝ)
        (boolScalar • coordinateFamily j) b i =
      boolScalar b * (if i = j then 1 else 0) := rfl

example (j : Fin 2) :
    ContinuousMap.piLinearEquiv ℝ Bool (fun _ : Fin 2 => ℝ)
        (boolScalar • coordinateFamily j) false = 0 := by
  rw [map_smul, piLinearEquiv_coordinateFamily]
  exact boolScalar_smul_false j

example (j : Fin 2) :
    ContinuousMap.piLinearEquiv ℝ Bool (fun _ : Fin 2 => ℝ)
        (boolScalar • coordinateFamily j) true = constantCoordinate j true := by
  rw [map_smul, piLinearEquiv_coordinateFamily]
  exact boolScalar_smul_true j

example : (Fin 0 → C(Bool, ℝ)) ≃ₗ[C(Bool, ℝ)] C(Bool, Fin 0 → ℝ) :=
  ContinuousMap.piLinearEquiv ℝ Bool (fun _ : Fin 0 => ℝ)

example : Subsingleton (Fin 0 → C(Bool, ℝ)) := inferInstance
example : Subsingleton C(Bool, Fin 0 → ℝ) := inferInstance

section

/-- The discrete topology on the empty base. -/
local instance emptyTopologicalSpace : TopologicalSpace Empty := ⊥

example : (Fin 2 → C(Empty, ℝ)) ≃ₗ[C(Empty, ℝ)] C(Empty, Fin 2 → ℝ) :=
  ContinuousMap.piLinearEquiv ℝ Empty (fun _ : Fin 2 => ℝ)

example : Subsingleton (Fin 2 → C(Empty, ℝ)) := inferInstance
example : Subsingleton C(Empty, Fin 2 → ℝ) := inferInstance

end

section

/-- The discrete topology on the zero-ring scalar model. -/
local instance punitTopologicalSpace : TopologicalSpace PUnit := ⊥
local instance : DiscreteTopology PUnit := ⟨rfl⟩

example : (0 : PUnit) = 1 := rfl

example : (Fin 2 → C(Bool, PUnit)) ≃ₗ[C(Bool, PUnit)] C(Bool, Fin 2 → PUnit) :=
  ContinuousMap.piLinearEquiv PUnit Bool (fun _ : Fin 2 => PUnit)

example : Subsingleton (Fin 2 → C(Bool, PUnit)) := inferInstance
example : Subsingleton C(Bool, Fin 2 → PUnit) := inferInstance

end

end CoordinateFunctions
