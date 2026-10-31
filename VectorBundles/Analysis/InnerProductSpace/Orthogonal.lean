/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Algebraic and inner-product orthogonal complements

The algebraic orthogonal complement for the sesquilinear form `innerₛₗ K`
agrees with the orthogonal complement in a normed inner product space.

This extends Mathlib's real-inner-product comparison
`Submodule.orthogonalBilin_innerₗ` to `RCLike` scalars. Since `innerₗ` is defined
as the real specialization of `innerₛₗ`, that comparison is the real
specialization of `Submodule.orthogonalBilin_innerₛₗ`.
-/

@[expose] public section

universe uK uA

namespace Submodule

variable {K : Type uK} [RCLike K]
variable {A : Type uA} [NormedAddCommGroup A] [InnerProductSpace K A]

/-- The algebraic orthogonal complement for the given inner product agrees with
the orthogonal complement. -/
@[simp]
theorem orthogonalBilin_innerₛₗ (S : Submodule K A) :
    S.orthogonalBilin (innerₛₗ K) = Sᗮ := by
  ext a
  simp only [Submodule.mem_orthogonalBilin, innerₛₗ_apply_apply,
    Submodule.mem_orthogonal]

end Submodule
