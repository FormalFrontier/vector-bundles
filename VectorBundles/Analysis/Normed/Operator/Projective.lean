/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.SeparationQuotient.Section

/-!
# Projective sections of linear isometries

A surjective linear isometry onto a projective module has a linear-isometric right
inverse. The source and target retain their given seminorms and scalar actions;
neither need be separated or complete, and the scalar semiring needs no topology.
The section is chosen noncanonically. Its norm and continuity properties are those
of every `LinearIsometry`.

Applied to the separation quotient, this gives a linear-isometric section whenever
the quotient module is projective. The quotient action uses the given continuous
constant scalar multiplications. Over a division ring, projectivity is automatic;
Mathlib's existing `SeparationQuotient.outCLM` is already a continuous-linear section,
and `SeparationQuotient.norm_mk` shows that this same map preserves norms.

## Nonseparated example

Give the algebraic module `ℝ × ℝ` the seminorm `‖(x, y)‖ = |x|` and its induced
pseudometric `dist (x, y) (x', y') = |x - x'|`, not the standard product topology.
The first-coordinate projection is a surjective linear isometry but is not
injective. Each map `x ↦ (x, a * x)` is a linear-isometric section, so sections need
not be unique and need not be left inverses. The seminormed structure can be
constructed with `SeminormedAddCommGroup.induced` along the projection.

## References

The construction uses Mathlib's `LinearMap.exists_rightInverse_of_surjective`,
from its projective-module lifting theory, together with `Isometry.right_inv` and
`LinearMap.toLinearIsometry`. The quotient application uses Mathlib's
`SeparationQuotient.mkCLM` and `SeparationQuotient.norm_mk`. Mathlib also provides
the division-ring section `SeparationQuotient.outCLM`.
-/

@[expose] public section

universe uR uE uF

namespace LinearIsometry

section Seminormed

variable {R : Type uR} [Semiring R]
  {E : Type uE} {F : Type uF}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- A noncanonical linear-isometric section of a surjective linear isometry onto a
projective module. Algebraic projectivity supplies a linear right inverse, which
is an isometry by Mathlib's `Isometry.right_inv`. -/
noncomputable def sectionOfSurjective [Module.Projective R F]
    (f : E →ₗᵢ[R] F) (hf : Function.Surjective f) : F →ₗᵢ[R] E := by
  let hs := f.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  exact hs.choose.toLinearIsometry
    (f.isometry.right_inv fun y => DFunLike.congr_fun hs.choose_spec y)

/-- The chosen projective section is a right inverse of the given linear isometry. -/
@[simp]
theorem apply_sectionOfSurjective [Module.Projective R F]
    (f : E →ₗᵢ[R] F) (hf : Function.Surjective f) (y : F) :
    f (f.sectionOfSurjective hf y) = y := by
  exact DFunLike.congr_fun
    (f.toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hf)).choose_spec y

/-- The chosen projective section is a uniform embedding, even when neither module
is separated. Injectivity comes from its right-inverse law. -/
theorem isUniformEmbedding_sectionOfSurjective [Module.Projective R F]
    (f : E →ₗᵢ[R] F) (hf : Function.Surjective f) :
    IsUniformEmbedding (f.sectionOfSurjective hf) := by
  refine
    { toIsUniformInducing := (f.sectionOfSurjective hf).isometry.isUniformInducing
      injective := ?_ }
  intro x y h
  simpa only [apply_sectionOfSurjective] using congrArg f h

end Seminormed

section NormedSource

variable {R : Type uR} [Semiring R]
  {E : Type uE} {F : Type uF}
  [NormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- For a separated source, the projective section agrees with the inverse of
Mathlib's `LinearIsometryEquiv.ofSurjective`: injectivity makes the section unique. -/
theorem sectionOfSurjective_eq_symm_ofSurjective [Module.Projective R F]
    (f : E →ₗᵢ[R] F) (hf : Function.Surjective f) :
    f.sectionOfSurjective hf =
      (LinearIsometryEquiv.ofSurjective f hf).symm.toLinearIsometry := by
  ext y
  apply f.injective
  exact (f.apply_sectionOfSurjective hf y).trans
    ((LinearIsometryEquiv.ofSurjective f hf).apply_symm_apply y).symm

end NormedSource

end LinearIsometry

namespace SeparationQuotient

/-- The separation quotient of a seminormed module has a linear-isometric section
when the quotient module is projective. This applies the projective isometry
section to Mathlib's `mkCLM`, bundled locally using `norm_mk`. -/
theorem exists_linearIsometry_rightInverse
    (R : Type uR) [Semiring R] (E : Type uE) [SeminormedAddCommGroup E]
    [Module R E] [ContinuousConstSMul R E]
    [Module.Projective R (SeparationQuotient E)] :
    ∃ s : SeparationQuotient E →ₗᵢ[R] E,
      Function.RightInverse s (mk : E → SeparationQuotient E) := by
  let q : E →ₗᵢ[R] SeparationQuotient E :=
    { (mkCLM R E).toLinearMap with
      norm_map' x := norm_mk x }
  refine ⟨q.sectionOfSurjective surjective_mk, ?_⟩
  intro x
  exact q.apply_sectionOfSurjective surjective_mk x

end SeparationQuotient
