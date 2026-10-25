/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.ContinuousMap.Algebra
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Coordinate bases for continuous functions

These data examples test reuse of the function basis through
`ContinuousMap.piLinearEquiv`, over the original pointwise module of continuous
functions. The coefficient example uses a nonconstant coordinate. Empty index
and base spaces are included without nontriviality assumptions.
-/

@[expose] public section

universe uX uI uR

noncomputable section

variable {I : Type uI} (R : Type uR) (X : Type uX)
  [TopologicalSpace X] [TopologicalSpace R] [Semiring R] [IsTopologicalSemiring R]

/- Finite coordinate bases use the existing pointwise module structure. -/
example [Finite I] : Module.Basis I C(X, R) C(X, I → R) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact (Pi.basisFun C(X, R) I).map
    (ContinuousMap.piLinearEquiv R X (fun _ : I => R))

/- A coefficient of a family with an identity coordinate is a continuous function. -/
example : C(ℝ, ℝ) :=
  ((Pi.basisFun C(ℝ, ℝ) (Fin 2)).map
    (ContinuousMap.piLinearEquiv ℝ ℝ (fun _ : Fin 2 => ℝ))).repr
      (ContinuousMap.piLinearEquiv ℝ ℝ (fun _ : Fin 2 => ℝ)
        (fun i => if i = 0 then ContinuousMap.id ℝ else ContinuousMap.const ℝ 1)) 0

/- No coordinates give an empty basis. -/
example : Module.Basis (Fin 0) C(X, R) C(X, Fin 0 → R) :=
  (Pi.basisFun C(X, R) (Fin 0)).map
    (ContinuousMap.piLinearEquiv R X (fun _ : Fin 0 => R))

/- An empty base permits the zero scalar semiring without changing its module. -/
example [TopologicalSpace Empty] [Finite I] :
    Module.Basis I C(Empty, R) C(Empty, I → R) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact (Pi.basisFun C(Empty, R) I).map
    (ContinuousMap.piLinearEquiv R Empty (fun _ : I => R))
