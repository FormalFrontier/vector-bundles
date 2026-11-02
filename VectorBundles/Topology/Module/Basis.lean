/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous coordinates of a finite basis

A finite basis of a module with the module topology gives a continuous linear equivalence
with the standard finite product of the scalar semiring. Its underlying linear equivalence
is `Module.Basis.equivFun`; the module and the scalar product retain their given topologies.

The construction uses Mathlib's automatic continuity for linear maps out of a module with
the module topology and its algebraic basis-coordinate equivalence.

## Main definitions

* `Module.Basis.equivFunLOfIsModuleTopology`: continuous linear coordinates associated to a
  supplied finite basis over a topological semiring.
-/

@[expose] public section

open scoped BigOperators

universe uR uM uι

namespace Module.Basis

variable {R : Type uR} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M] [TopologicalSpace M]
variable [hMT : IsModuleTopology R M]
variable {ι : Type uι}

section Finite

variable [Finite ι]

/-- The continuous linear coordinate equivalence of a finite basis of a module with the
module topology. Its underlying linear equivalence is `Module.Basis.equivFun`. -/
noncomputable def equivFunLOfIsModuleTopology (b : Module.Basis ι R M) :
    M ≃L[R] (ι → R) := by
  let : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  exact ContinuousLinearEquiv.mk b.equivFun
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)

/-- Forgetting continuity gives the algebraic coordinate equivalence of the supplied basis. -/
@[simp]
theorem equivFunLOfIsModuleTopology_toLinearEquiv (b : Module.Basis ι R M) :
    b.equivFunLOfIsModuleTopology.toLinearEquiv = b.equivFun :=
  rfl

/-- The coordinates are the coefficients in the supplied basis. -/
@[simp]
theorem equivFunLOfIsModuleTopology_apply (b : Module.Basis ι R M) (m : M) :
    b.equivFunLOfIsModuleTopology m = b.repr m :=
  rfl

/-- The inverse is the algebraic reconstruction map of the supplied basis. -/
@[simp]
theorem equivFunLOfIsModuleTopology_symm_apply (b : Module.Basis ι R M) (v : ι → R) :
    b.equivFunLOfIsModuleTopology.symm v = b.equivFun.symm v :=
  rfl

end Finite

/-- Reconstruction is the finite linear combination with the prescribed coefficients. -/
theorem equivFunLOfIsModuleTopology_symm_apply_eq_sum [Fintype ι]
    (b : Module.Basis ι R M) (v : ι → R) :
    b.equivFunLOfIsModuleTopology.symm v = ∑ i, v i • b i := by
  rw [equivFunLOfIsModuleTopology_symm_apply, b.equivFun_symm_apply]

end Module.Basis

@[expose] public section

namespace Module.Basis

/-- The inverse coordinate equivalence sends a standard coordinate vector to its basis vector. -/
theorem equivFunLOfIsModuleTopology_symm_single
    {R : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [IsModuleTopology R M] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (i : ι) :
    b.equivFunLOfIsModuleTopology.symm (Pi.single i (1 : R)) = b i := by
  simp

end Module.Basis
