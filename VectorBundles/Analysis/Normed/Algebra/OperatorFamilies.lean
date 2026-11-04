module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
public import Mathlib.Analysis.Normed.Field.Basic
public import VectorBundles.Analysis.Normed.Algebra.Units
public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic

/-!
# Invertibility in pointwise-continuous operator families

For a family of continuous endomorphisms of a finite-dimensional normed space,
continuity on each fixed vector suffices for openness of the invertible locus.
The scalar field and space need not be complete. The zero space and an empty
parameter space are allowed.

The endomorphism algebra is finite dimensional because forgetting continuity
is a linear injection into the algebraic endomorphisms. This does not assert
that every algebraic endomorphism is continuous over an incomplete field.

## References

The continuity step uses the existing
`ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional` theorem.
-/

@[expose] public section

universe uK uE uP

namespace ContinuousLinearMap

/-- A pointwise-continuous family of continuous endomorphisms of a
finite-dimensional normed space has an open invertible locus. Thus unit
values persist locally, even over an incomplete scalar field. Finite
dimensionality of the continuous endomorphism algebra is derived internally
by its linear injection into the algebraic endomorphisms. -/
theorem isOpen_setOf_isUnit_of_continuous_apply
    {K : Type uK} [NontriviallyNormedField K]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace K E]
    [FiniteDimensional K E] {P : Type uP} [TopologicalSpace P]
    (F : P → E →L[K] E) (hF : ∀ v : E, Continuous (fun p => F p v)) :
    IsOpen {p : P | IsUnit (F p)} := by
  let forget : (E →L[K] E) →ₗ[K] (E →ₗ[K] E) :=
    { toFun := fun f => f.toLinearMap
      map_add' := by
        intro f g
        rfl
      map_smul' := by
        intro c f
        rfl }
  have hforget : Function.Injective forget := by
    intro f g h
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun T : E →ₗ[K] E => T x) h
  have : FiniteDimensional K (E →L[K] E) :=
    FiniteDimensional.of_injective forget hforget
  have hopen : IsOpen {T : E →L[K] E | IsUnit T} :=
    FiniteDimensional.isOpen_setOf_isUnit K
  exact hopen.preimage
    ((ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional F).mpr hF)

end ContinuousLinearMap
