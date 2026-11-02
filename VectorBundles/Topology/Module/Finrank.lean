/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic

/-!
# Fibre rank from local linear models

A family of modules over a semiring has locally constant cardinal and numerical rank if it is
pointwise linearly equivalent to fixed models on a neighbourhood cover. The index set and models
may be arbitrary, including infinite ones. No common finite rank bound,
finite-generation hypothesis, or topology on the modules is required.

The numerical rank `Module.finrank K M` is `Cardinal.toNat (Module.rank K M)`, so infinite cardinal
ranks are sent to zero. It remains invariant under linear equivalence, but need not recover cardinal
rank or certify finite generation. Interpreting it as the size of a chosen finite basis requires
appropriate rank conditions. Over a division ring, cardinal rank retains infinite vector-space
dimensions, whereas `Module.finrank` is zero on infinite-dimensional fibres. These results isolate
the algebraic local-model argument; they do not construct a vector bundle.

## References

* Allen Hatcher, *Vector Bundles & K-Theory*, §1.1, for the fixed-dimensional vector-bundle setting.
-/

@[expose] public section

universe uK uX uI uF uG

namespace Module

/-- Pointwise linear equivalences to fixed models on a neighbourhood cover make the cardinal-valued
fibre rank over a semiring locally constant.

The index set and models may be arbitrary, including infinite ones. In contrast to the fixed
finite-dimensional real or complex setting of Hatcher's *Vector Bundles & K-Theory*, §1.1,
the scalars need not be a division ring. No finite-generation hypothesis or module topology is
assumed. Over a division ring, the conclusion retains the cardinal dimension of
infinite-dimensional fibres. -/
theorem isLocallyConstant_rank_of_linearEquiv_cover
    {K : Type uK} [Semiring K]
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
natural-number-valued fibre finrank over a semiring locally constant.

The index set and models may be arbitrary, including infinite ones. This follows from
`isLocallyConstant_rank_of_linearEquiv_cover` by applying `Cardinal.toNat`, since
`Module.finrank K M = Cardinal.toNat (Module.rank K M)`. Numerical finrank remains invariant under
linear equivalence, but sends infinite cardinal ranks to zero. Thus it need not recover cardinal
rank or certify finite generation, and interpreting it as the size of a chosen finite basis requires
appropriate rank conditions. -/
theorem isLocallyConstant_finrank_of_linearEquiv_cover
    {K : Type uK} [Semiring K]
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
