/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Trivializations precomposed with homeomorphisms

Characteristic equations for precomposition of a bundle trivialization with a homeomorphism:
evaluation, the base set, and the inverse of the underlying open partial homeomorphism.
-/

@[expose] public section

namespace Bundle.Trivialization

universe uB uF uZ uZ'

variable {B : Type uB} {F : Type uF} {Z : Type uZ} {Z' : Type uZ'}
variable [TopologicalSpace B] [TopologicalSpace F]
variable [TopologicalSpace Z] [TopologicalSpace Z']
variable {proj : Z → B} (e : Trivialization F proj) (h : Z' ≃ₜ Z)

/-- Precomposing a trivialization with a homeomorphism composes their evaluations. -/
@[simp] theorem compHomeomorph_apply (z : Z') :
    (e.compHomeomorph h) z = e (h z) := rfl

/-- Precomposing a trivialization with a homeomorphism preserves its base set. -/
@[simp] theorem compHomeomorph_baseSet :
    (e.compHomeomorph h).baseSet = e.baseSet := rfl

/-- The inverse of the underlying open partial homeomorphism is postcomposed with the inverse
homeomorphism. -/
@[simp] theorem toOpenPartialHomeomorph_compHomeomorph_symm_apply (w : B × F) :
    (e.compHomeomorph h).toOpenPartialHomeomorph.symm w =
      h.symm (e.toOpenPartialHomeomorph.symm w) := rfl

end Bundle.Trivialization
