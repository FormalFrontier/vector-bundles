/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import ProjectiveModules.Topology.Splitting

/-!
# Kernel-product splittings over semirings

A continuous linear map with a continuous linear right inverse splits its domain into the
product of its codomain and its kernel. The kernel coordinate of `x` is the residual
`x - s (f x)`, and the inverse sends `(y, k)` to `s y + k`.

The scalar semiring needs no topology. Only the domain is assumed to be a topological
additive group; the codomain and the kernel factor use their additive commutative monoids.

## References

The splitting and its Ring comparison reuse
`ContinuousLinearMap.equivProdKerOfRightInverse` from
`ProjectiveModules.Topology.Splitting`. This module extracts its continuous kernel
projection and retains the kernel-product API for compatibility. The canonical
construction generalizes Mathlib's `ContinuousLinearEquiv.equivOfRightInverse`; the
projection agrees with Mathlib's `ContinuousLinearMap.projKerOfRightInverse` over rings.
-/

@[expose] public section

universe uR uE uF

namespace ContinuousLinearMap

section Semiring

variable {R : Type uR} [Semiring R]
  {E : Type uE} [AddCommGroup E] [TopologicalSpace E] [Module R E]
  {F : Type uF} [AddCommMonoid F] [TopologicalSpace F] [Module R F]

/-- The continuous linear projection onto the kernel of `f` along the range of a right
inverse `s`, sending `x` to `x - s (f x)`. This is the second projection of
`equivProdKerOfRightInverse`. -/
def kerProjectionOfRightInverse [hE : IsTopologicalAddGroup E] (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) : E →L[R] f.ker :=
  (ContinuousLinearMap.snd R F f.ker).comp
    (f.equivProdKerOfRightInverse s h).toContinuousLinearMap

variable [IsTopologicalAddGroup E]

/-- The kernel projection is the residual after applying the section. -/
@[simp]
theorem coe_kerProjectionOfRightInverse_apply (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) (x : E) :
    (kerProjectionOfRightInverse f s h x : E) = x - s (f x) := by
  rfl

end Semiring

section Ring

variable {R : Type uR} [Ring R]
  {E : Type uE} [AddCommGroup E] [TopologicalSpace E] [Module R E]
  [IsTopologicalAddGroup E]
  {F : Type uF} [AddCommGroup F] [TopologicalSpace F] [Module R F]

/-- Over a ring, the kernel projection agrees with `projKerOfRightInverse`. -/
theorem kerProjectionOfRightInverse_eq_projKerOfRightInverse
    (f : E →L[R] F) (s : F →L[R] E) (h : Function.RightInverse s f) :
    kerProjectionOfRightInverse f s h = f.projKerOfRightInverse s h := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [coe_kerProjectionOfRightInverse_apply, coe_projKerOfRightInverse_apply]

end Ring

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section Semiring

variable {R : Type uR} [Semiring R]
  {E : Type uE} [AddCommGroup E] [TopologicalSpace E] [Module R E]
  {F : Type uF} [AddCommMonoid F] [TopologicalSpace F] [Module R F]

/-- The continuous linear equivalence splitting the domain of `f` into its codomain and
kernel using a right inverse `s`. Its coordinates are `f x` and `x - s (f x)`.
This compatibility definition is `ContinuousLinearMap.equivProdKerOfRightInverse`. -/
def prodKerOfRightInverse [hE : IsTopologicalAddGroup E] (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) : E ≃L[R] (F × f.ker) :=
  f.equivProdKerOfRightInverse s h

variable [IsTopologicalAddGroup E]

/-- The first coordinate of the splitting is the given map. -/
@[simp]
theorem fst_prodKerOfRightInverse (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) (x : E) :
    (prodKerOfRightInverse f s h x).1 = f x := by
  rfl

/-- The second coordinate of the splitting is the residual after applying the section. -/
@[simp]
theorem snd_prodKerOfRightInverse (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) (x : E) :
    ((prodKerOfRightInverse f s h x).2 : E) = x - s (f x) := by
  exact ContinuousLinearMap.coe_kerProjectionOfRightInverse_apply f s h x

/-- The inverse splitting adds the section value and the kernel coordinate. -/
@[simp]
theorem prodKerOfRightInverse_symm_apply (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) (y : F × f.ker) :
    (prodKerOfRightInverse f s h).symm y = s y.1 + (y.2 : E) := by
  exact (ContinuousLinearMap.equivProdKerOfRightInverse_symm_apply f s h y).trans
    (add_comm _ _)

end Semiring

section Ring

variable {R : Type uR} [Ring R]
  {E : Type uE} [AddCommGroup E] [TopologicalSpace E] [Module R E]
  [IsTopologicalAddGroup E]
  {F : Type uF} [AddCommGroup F] [TopologicalSpace F] [Module R F]

/-- Over a ring, the kernel-product splitting agrees with `equivOfRightInverse`. -/
theorem prodKerOfRightInverse_eq_equivOfRightInverse
    (f : E →L[R] F) (s : F →L[R] E) (h : Function.RightInverse s f) :
    prodKerOfRightInverse f s h = equivOfRightInverse f s h := by
  exact ContinuousLinearMap.equivProdKerOfRightInverse_eq_equivOfRightInverse f s h

end Ring

attribute [deprecated ContinuousLinearMap.equivProdKerOfRightInverse (since := "2026-11-04")]
  prodKerOfRightInverse
attribute [deprecated ContinuousLinearMap.fst_equivProdKerOfRightInverse (since := "2026-11-04")]
  fst_prodKerOfRightInverse
attribute [deprecated ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse
  (since := "2026-11-04")] snd_prodKerOfRightInverse
attribute [deprecated ContinuousLinearMap.equivProdKerOfRightInverse_symm_apply
  (since := "2026-11-04")] prodKerOfRightInverse_symm_apply
attribute [deprecated ContinuousLinearMap.equivProdKerOfRightInverse_eq_equivOfRightInverse
  (since := "2026-11-04")] prodKerOfRightInverse_eq_equivOfRightInverse

end ContinuousLinearEquiv
