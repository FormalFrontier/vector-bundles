module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Unit reflection through nil kernels

Surjective homomorphisms from rings to semirings reflect units if every kernel
element is nilpotent. Neither commutativity nor a common nilpotence exponent is
required.
-/

@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {F : Type w}
  [Ring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]

/-- A surjective homomorphism from a ring to a semiring is local if every element
mapped to zero is nilpotent. -/
theorem IsLocalHom.of_surjective_of_isNilpotent_ker
    (q : F) (hsurj : Function.Surjective q)
    (hker : ∀ a : R, q a = 0 → IsNilpotent a) : IsLocalHom q := by
  have hfiber (t : R) (ht : q t = 1) : IsUnit t := by
    have hzero : q (1 - t) = 0 := by
      rw [sub_eq_add_neg, map_add, map_one, ← ht, ← map_add,
        add_neg_cancel, map_zero]
    simpa only [sub_sub_cancel] using (hker (1 - t) hzero).isUnit_one_sub
  have hreflect (a : R) (ha : IsUnit (q a)) : IsUnit a := by
    obtain ⟨u, hu⟩ := ha
    obtain ⟨b, hb⟩ := hsurj (↑(u⁻¹) : S)
    obtain ⟨v, hv⟩ := hfiber (a * b) (by simp [map_mul, ← hu, hb])
    obtain ⟨w, hw⟩ := hfiber (b * a) (by simp [map_mul, ← hu, hb])
    have hr : a * (b * ↑(v⁻¹)) = 1 := by
      rw [← mul_assoc, ← hv]
      exact v.val_inv
    have hl : (↑(w⁻¹) * b) * a = 1 := by
      rw [mul_assoc, ← hw]
      exact w.inv_val
    apply isUnit_iff_exists_and_exists.mpr
    constructor <;> first | exact ⟨_, hl⟩ | exact ⟨_, hr⟩
  constructor
  exact hreflect
