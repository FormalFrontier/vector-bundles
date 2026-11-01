/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic

/-!
# Fibre dimension from local linear models

A family of algebraic modules has locally constant finrank if it is pointwise linearly equivalent
to fixed models on a neighbourhood cover. The covering family can be infinite and the dimensions
of the models need not be bounded. No topology on the modules is needed.

## References

* Allen Hatcher, *Vector Bundles & K-Theory*, §1.1, for local constancy of fibre dimension.
-/

@[expose] public section

universe uK uX uI uF uG

namespace Module

/-- Algebraic form of local constancy of fibre dimension: pointwise linear equivalences to fixed
models on a neighbourhood cover make the fibre finrank locally constant.

The index set and models may vary arbitrarily. In contrast to the finite-dimensional setting of
Hatcher's *Vector Bundles & K-Theory*, §1.1, no finite-dimensionality or module topology is assumed.
Here `Module.finrank` is zero on infinite-dimensional fibres; no assertion about their cardinal
dimension is made. -/
theorem isLocallyConstant_finrank_of_linearEquiv_cover
    {K : Type uK} [DivisionRing K]
    {X : Type uX} [TopologicalSpace X]
    {I : Type uI}
    (F : X → Type uF) (G : I → Type uG)
    [∀ x, AddCommMonoid (F x)] [∀ x, Module K (F x)]
    [∀ i, AddCommMonoid (G i)] [∀ i, Module K (G i)]
    (U : I → Set X)
    (hU : ∀ x : X, ∃ i : I, x ∈ interior (U i))
    (hF : ∀ i, ∀ x ∈ U i, Nonempty (F x ≃ₗ[K] G i)) :
    IsLocallyConstant (fun x : X => Module.finrank K (F x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨i, hi⟩ := hU x
  obtain ⟨ex⟩ := hF i x (interior_subset hi)
  filter_upwards [isOpen_interior.mem_nhds hi] with y hy
  obtain ⟨ey⟩ := hF i y (interior_subset hy)
  exact ey.finrank_eq.trans ex.finrank_eq.symm

end Module
