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

A family of algebraic modules has locally constant cardinal rank if it is pointwise linearly
equivalent to fixed models on a neighbourhood cover. Its natural-number-valued finrank is then
locally constant as well. The covering family can be infinite, and no common finite dimension bound
is required. No finite-dimensionality or topology on the modules is needed.

Cardinal rank retains infinite dimensions, whereas `Module.finrank` is zero on infinite-dimensional
fibres. These results express the algebraic local-constancy argument for fibre dimension, not the
full vector-bundle theorem.

## References

* Allen Hatcher, *Vector Bundles & K-Theory*, §1.1, for local constancy of fibre dimension.
-/

@[expose] public section

universe uK uX uI uF uG

namespace Module

/-- Pointwise linear equivalences to fixed models on a neighbourhood cover make the cardinal-valued
fibre rank locally constant.

The index set and models may vary arbitrarily. In contrast to the finite-dimensional setting of
Hatcher's *Vector Bundles & K-Theory*, §1.1, no finite-dimensionality or module topology is assumed.
The conclusion retains the cardinal dimension of infinite-dimensional fibres. -/
theorem isLocallyConstant_rank_of_linearEquiv_cover
    {K : Type uK} [DivisionRing K]
    {X : Type uX} [TopologicalSpace X]
    {I : Type uI}
    (F : X → Type uF) (G : I → Type uG)
    [∀ x, AddCommMonoid (F x)] [∀ x, Module K (F x)]
    [∀ i, AddCommMonoid (G i)] [∀ i, Module K (G i)]
    (U : I → Set X)
    (hU : ∀ x : X, ∃ i : I, x ∈ interior (U i))
    (hF : ∀ i, ∀ x ∈ U i, Nonempty (F x ≃ₗ[K] G i)) :
    IsLocallyConstant (fun x : X => Module.rank K (F x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨i, hi⟩ := hU x
  obtain ⟨ex⟩ := hF i x (interior_subset hi)
  filter_upwards [isOpen_interior.mem_nhds hi] with y hy
  obtain ⟨ey⟩ := hF i y (interior_subset hy)
  exact (ey.trans ex.symm).rank_eq

/-- Pointwise linear equivalences to fixed models on a neighbourhood cover make the
natural-number-valued fibre finrank locally constant.

This follows from `isLocallyConstant_rank_of_linearEquiv_cover` by applying `Cardinal.toNat`.
Unlike cardinal rank, `Module.finrank` is zero on infinite-dimensional fibres, so local constancy
of finrank alone cannot distinguish such fibres from zero-dimensional ones. -/
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
  have h := isLocallyConstant_rank_of_linearEquiv_cover F G U hU hF
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro x
  filter_upwards [h x] with y hy
  exact congrArg Cardinal.toNat hy

end Module
