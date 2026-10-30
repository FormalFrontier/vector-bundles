/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.Projection.Fiberwise
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The real line inside the complex plane

The usual real part retracts the proper real-linear subspace of real complex
numbers. The residual is purely imaginary, orthogonal to every real vector in
the given real inner product on `ℂ`. This is a positive-rank, proper-range example.
The product projection `Bool × ℝ → Bool` also illustrates the total-space
construction on fixed fibre module structures, with the real axis as each image.
The fibre operations are fixed once using Mathlib's algebraic structure-transport
API; the retraction uses these same modules and the given product projection.
-/

@[expose] public section

namespace Complex

/-- The real-linear inclusion of the real axis into the complex plane. -/
def realAxis : ℝ →ₗ[ℝ] ℂ where
  toFun x := (x : ℂ)
  map_add' x y := by simp
  map_smul' c x := by apply Complex.ext <;> simp

/-- Real part as a real-linear map, with the usual complex structures unchanged. -/
def realPart : ℂ →ₗ[ℝ] ℝ where
  toFun := re
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Evaluation of the real-axis embedding. -/
@[simp] theorem realAxis_apply (x : ℝ) : realAxis x = (x : ℂ) := rfl

/-- Evaluation of the real-part map. -/
@[simp] theorem realPart_apply (z : ℂ) : realPart z = z.re := rfl

/-- Real part is an orthogonal retraction, measured in the given real inner product. -/
theorem realPart_isOrthogonalRetraction : realAxis.IsOrthogonalRetraction realPart := by
  constructor
  · intro x
    simp
  · intro z x
    change Complex.re ((x : ℂ) * star (z - (z.re : ℂ))) = 0
    simp [Complex.mul_re]

/-- The inclusion is injective, so the projection/preimage construction applies. -/
theorem realAxis_injective : Function.Injective realAxis := by
  intro x y h
  simpa using congrArg Complex.re h

/-- The real-axis range is proper: it does not contain the imaginary unit. -/
theorem I_not_mem_realAxis_range : I ∉ realAxis.range := by
  rintro ⟨x, hx⟩
  simpa using congrArg Complex.im hx

/-- The finite-dimensional construction retracts the real axis in this proper-range example. -/
theorem orthogonalRetraction_realAxis (x : ℝ) :
    realAxis.orthogonalRetractionOfFiniteDimensional realAxis_injective (x : ℂ) = x :=
  realAxis.orthogonalRetractionOfFiniteDimensional_apply_image realAxis_injective x

end Complex

namespace RealAxisProduct

/-- The real-coordinate equivalence of a product fibre, used to fix its operations. -/
@[simps] def fiberEquiv (x : Bool) : {t : Bool × ℝ // t.1 = x} ≃ ℝ where
  toFun t := t.val.2
  invFun r := ⟨(x, r), rfl⟩
  left_inv t := Subtype.ext (Prod.ext t.property.symm rfl)
  right_inv _ := rfl

/-- The fixed additive operations on a product fibre, acting on its real coordinate. -/
instance fiberAddCommGroup (x : Bool) : AddCommGroup {t : Bool × ℝ // t.1 = x} :=
  (fiberEquiv x).addCommGroup

/-- The fixed real scalar action on a product fibre. -/
instance fiberModule (x : Bool) : Module ℝ {t : Bool × ℝ // t.1 = x} :=
  (fiberEquiv x).addEquiv.module ℝ

/-- Real coordinates are linear for the fixed fibre operations. -/
@[simps!] def fiberLinearEquiv (x : Bool) : {t : Bool × ℝ // t.1 = x} ≃ₗ[ℝ] ℝ :=
  (fiberEquiv x).addEquiv.linearEquiv ℝ

/-- The fixed fibre module is finite-dimensional, as witnessed by its real coordinate. -/
instance fiberFiniteDimensional (x : Bool) :
    FiniteDimensional ℝ {t : Bool × ℝ // t.1 = x} :=
  (fiberLinearEquiv x).symm.finiteDimensional

/-- Embed each product fibre by its second coordinate into the real axis. -/
noncomputable def fiberEmbedding (x : Bool) : {t : Bool × ℝ // t.1 = x} →ₗ[ℝ] ℂ :=
  Complex.realAxis.comp (fiberLinearEquiv x).toLinearMap

/-- Evaluation of the embedding uses the original product's second coordinate. -/
@[simp] theorem fiberEmbedding_apply (x : Bool) (t : {t : Bool × ℝ // t.1 = x}) :
    fiberEmbedding x t = (t.val.2 : ℂ) := rfl

/-- Each fibre embedding is injective. -/
theorem fiberEmbedding_injective (x : Bool) : Function.Injective (fiberEmbedding x) :=
  Complex.realAxis_injective.comp (fiberLinearEquiv x).injective

/-- The finite-dimensional total-space retraction recovers every real-axis product point. -/
theorem retraction_on_real_axis (x : Bool) (r : ℝ) :
    (Prod.fst : Bool × ℝ → Bool).fiberwiseOrthogonalRetractionOfFiniteDimensional
      fiberEmbedding fiberEmbedding_injective (x, (r : ℂ)) = (x, r) :=
  (Prod.fst : Bool × ℝ → Bool).fiberwiseOrthogonalRetractionOfFiniteDimensional_apply_image
    fiberEmbedding fiberEmbedding_injective (x, r)

/-- The product model has nonzero fibre images, each excluding the imaginary unit. -/
theorem fiberEmbedding_nonzero_proper (x : Bool) :
    fiberEmbedding x ≠ 0 ∧ Complex.I ∉ (fiberEmbedding x).range := by
  constructor
  · intro h
    have := congrArg (fun f : {t : Bool × ℝ // t.1 = x} →ₗ[ℝ] ℂ =>
      f ⟨(x, 1), rfl⟩) h
    simp at this
  · rintro ⟨t, ht⟩
    exact Complex.I_not_mem_realAxis_range ⟨t.val.2, ht⟩

end RealAxisProduct
