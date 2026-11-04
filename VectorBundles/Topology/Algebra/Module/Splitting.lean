/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Kernel-product splittings over semirings

A continuous linear map with a continuous linear right inverse splits its domain into the
product of its codomain and its kernel. The kernel coordinate of `x` is the residual
`x - s (f x)`, and the inverse sends `(y, k)` to `s y + k`.

The scalar semiring needs no topology. Only the domain is assumed to be a topological
additive group; the codomain and the kernel factor use their additive commutative monoids.

## References

The constructions generalize Mathlib's `ContinuousLinearMap.projKerOfRightInverse` and
`ContinuousLinearEquiv.equivOfRightInverse` from rings to semirings.
-/

@[expose] public section

universe uR uE uF

namespace ContinuousLinearMap

section Semiring

variable {R : Type uR} [Semiring R]
  {E : Type uE} [AddCommGroup E] [TopologicalSpace E] [Module R E]
  {F : Type uF} [AddCommMonoid F] [TopologicalSpace F] [Module R F]

/-- The continuous linear projection onto the kernel of `f` along the range of a right
inverse `s`, sending `x` to `x - s (f x)`. -/
def kerProjectionOfRightInverse [hE : IsTopologicalAddGroup E] (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) : E →L[R] f.ker := by
  let p : E →L[R] E :=
    { toLinearMap := LinearMap.id - s.toLinearMap.comp f.toLinearMap
      cont := continuous_id.sub (s.cont.comp f.cont) }
  exact p.codRestrict f.ker fun x => by
    change f (p x) = 0
    apply h.injective
    calc
      s (f (p x)) = (s.toLinearMap.comp f.toLinearMap) (x - s (f x)) := rfl
      _ = s (f x) - s (f (s (f x))) :=
        (s.toLinearMap.comp f.toLinearMap).map_sub _ _
      _ = s 0 := by rw [h (f x), sub_self, map_zero]

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
kernel using a right inverse `s`. Its coordinates are `f x` and `x - s (f x)`. -/
def prodKerOfRightInverse [hE : IsTopologicalAddGroup E] (f : E →L[R] F) (s : F →L[R] E)
    (h : Function.RightInverse s f) : E ≃L[R] (F × f.ker) := by
  refine equivOfInverse (f.prod (f.kerProjectionOfRightInverse s h))
    (s.coprod f.ker.subtypeL) ?_ ?_
  · intro x
    simp
  · rintro ⟨y, k⟩
    have hk : f (k : E) = 0 := k.property
    have hf : f (s y + (k : E)) = y := by rw [f.map_add, h y, hk, add_zero]
    apply Prod.ext
    · simpa only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply,
        Submodule.subtypeL_apply] using hf
    · apply Subtype.ext
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply,
        Submodule.subtypeL_apply, ContinuousLinearMap.coe_kerProjectionOfRightInverse_apply, hf]
      simp

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
  rfl

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
  apply ContinuousLinearEquiv.ext
  funext x
  apply Prod.ext
  · rw [fst_prodKerOfRightInverse, fst_equivOfRightInverse]
  · apply Subtype.ext
    rw [snd_prodKerOfRightInverse, snd_equivOfRightInverse]

end Ring

end ContinuousLinearEquiv
