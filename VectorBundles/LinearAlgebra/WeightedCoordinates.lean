/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Supported weighted coordinates

Given modules `F x`, model modules `G i`, and linear equivalences from `G i` to `F x`
where `x ∈ U i`, `LinearMap.weightedCoordinates` multiplies the inverse coordinates
by a scalar weight and sets coordinates outside the chart to zero. Its target is
the full dependent product of the given models. Neither the index type nor any
module is required to be finite or nontrivial.

The membership, nonmembership, zero-weight, and chart-evaluation rules describe the
map without unfolding its definition. Equality in the target uses function
extensionality; preservation of zero, addition, and scalar multiplication uses the
usual linear-map API. One valid coordinate with a unit weight makes the map injective.
Mere nonzeroness of the weight would not suffice over a general commutative semiring.

## Implementation notes

The construction uses `LinearMap.pi` and scalar multiplication on linear maps. The
fibre modules, their operations, and the chart equivalences are given data. No
replacement fibres, topologies, atlas, or weights are constructed here.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2: motivation for the finite
  weighted local-coordinate construction.
-/

@[expose] public section

universe uK uX uI uF uG

namespace LinearMap

variable {K : Type uK} [CommSemiring K]
  {X : Type uX} {I : Type uI} {F : X → Type uF} {G : I → Type uG}
  [∀ x, AddCommMonoid (F x)] [∀ x, Module K (F x)]
  [∀ i, AddCommMonoid (G i)] [∀ i, Module K (G i)]

variable (U : I → Set X) (w : I → X → K)
  (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[K] F x)

/-- The linear map into all model coordinates, weighted on each chart and zero off it. -/
noncomputable def weightedCoordinates (x : X) : F x →ₗ[K] ∀ i, G i := by
  classical
  exact LinearMap.pi fun i ↦
    if hx : x ∈ U i then w i x • (c i x hx).symm.toLinearMap else 0

/-- On a chart, the coordinate is its weighted inverse linear equivalence. -/
@[simp]
theorem weightedCoordinates_apply_of_mem {x : X} {i : I} (hx : x ∈ U i) (v : F x) :
    weightedCoordinates U w c x v i = w i x • (c i x hx).symm v := by
  classical
  simp [weightedCoordinates, hx]

/-- Outside a chart, its coordinate vanishes. -/
@[simp]
theorem weightedCoordinates_apply_of_notMem {x : X} {i : I} (hx : x ∉ U i) (v : F x) :
    weightedCoordinates U w c x v i = 0 := by
  classical
  simp [weightedCoordinates, hx]

/-- A zero weight makes its coordinate vanish, whether or not the chart is defined. -/
@[simp]
theorem weightedCoordinates_apply_of_eq_zero {x : X} {i : I}
    (hw : w i x = 0) (v : F x) : weightedCoordinates U w c x v i = 0 := by
  classical
  by_cases hx : x ∈ U i
  · rw [weightedCoordinates_apply_of_mem U w c hx v, hw, zero_smul]
  · exact weightedCoordinates_apply_of_notMem U w c hx v

/-- Coordinates of a vector supplied by another chart use the same exact chart inverses. -/
theorem weightedCoordinates_apply_chart {x : X} {i j : I}
    (hi : x ∈ U i) (hj : x ∈ U j) (v : G j) :
    weightedCoordinates U w c x (c j x hj v) i =
      w i x • (c i x hi).symm (c j x hj v) :=
  weightedCoordinates_apply_of_mem U w c hi _

/-- On the chart that supplies the vector, its coordinate is scalar multiplication
by the weight. -/
theorem weightedCoordinates_apply_chart_self {x : X} {i : I}
    (hx : x ∈ U i) (v : G i) :
    weightedCoordinates U w c x (c i x hx v) i = w i x • v := by
  rw [weightedCoordinates_apply_of_mem U w c hx, (c i x hx).symm_apply_apply]

/-- One chart coordinate with a unit weight suffices for injectivity.

No nontriviality or field assumption is needed: unit scalar cancellation works for the
same given module action, followed by injectivity of the exact inverse chart.
-/
theorem weightedCoordinates_injective_of_isUnit {x : X} {i : I}
    (hx : x ∈ U i) (hw : IsUnit (w i x)) :
    Function.Injective (weightedCoordinates U w c x) := by
  intro v v' h
  apply (c i x hx).symm.injective
  apply hw.smul_left_cancel.mp
  simpa only [weightedCoordinates_apply_of_mem U w c hx] using
    congrArg (fun f : ∀ j, G j ↦ f i) h

end LinearMap
