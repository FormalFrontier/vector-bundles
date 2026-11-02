/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Comparison of finite-basis continuous coordinates

Over a complete nontrivially normed field, Mathlib's `Module.Basis.equivFunL` agrees with
`Module.Basis.equivFunLOfIsModuleTopology`. The topology of the source is unchanged and no
norm on the source is required. The module-topology witness is transported from the standard
finite scalar product by Mathlib's continuous linear equivalence.
-/

@[expose] public section

universe uK uM uι

namespace Module.Basis

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
variable {M : Type uM} [AddCommGroup M] [Module K M] [TopologicalSpace M]
variable [IsTopologicalAddGroup M] [ContinuousSMul K M] [T2Space M]
variable {ι : Type uι} [Finite ι]

/-- Over a complete nontrivially normed field, the module-topology coordinate equivalence
is Mathlib's continuous coordinate equivalence. No module-topology hypothesis or source
norm is added to the hypotheses of `Module.Basis.equivFunL`. -/
theorem equivFunLOfIsModuleTopology_eq_equivFunL (b : Module.Basis ι K M) :
    b.equivFunLOfIsModuleTopology (hMT := IsModuleTopology.iso b.equivFunL.symm) =
      b.equivFunL := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rfl

end Module.Basis
