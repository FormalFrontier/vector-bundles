/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Linear product coordinates for continuous maps

`ContinuousMap.piLinearEquiv` rebundles `ContinuousMap.piEquiv` as a linear equivalence
between families of continuous maps and continuous maps into a product. Scalars are
continuous functions on the base, acting pointwise, and need not be constant.

The equivalence uses the existing pointwise module structures. It is an algebraic
linear equivalence over `C(X, R)`, not a continuous linear equivalence between function spaces.
-/

@[expose] public section

universe uX uI uR uM

namespace ContinuousMap

variable {I : Type uI} (R : Type uR) (X : Type uX) (M : I → Type uM)
  [TopologicalSpace X] [TopologicalSpace R] [Semiring R] [IsTopologicalSemiring R]
  [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, ContinuousAdd (M i)] [∀ i, ContinuousSMul R (M i)]

/-- The product equivalence for continuous maps, linear over the semiring of continuous
scalar functions. Its underlying equivalence is `ContinuousMap.piEquiv`; the module
structures are the existing pointwise ones. -/
def piLinearEquiv : (∀ i, C(X, M i)) ≃ₗ[C(X, R)] C(X, ∀ i, M i) :=
  { piEquiv X M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem piLinearEquiv_toEquiv :
    (piLinearEquiv R X M).toEquiv = piEquiv X M := rfl

@[simp]
theorem piLinearEquiv_apply (g : ∀ i, C(X, M i)) (x : X) (i : I) :
    piLinearEquiv R X M g x i = g i x := rfl

@[simp]
theorem piLinearEquiv_symm_apply (f : C(X, ∀ i, M i)) (i : I) (x : X) :
    (piLinearEquiv R X M).symm f i x = f x i := rfl

end ContinuousMap
