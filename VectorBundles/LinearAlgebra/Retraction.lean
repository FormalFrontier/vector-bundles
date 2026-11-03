/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Complements from linear retractions

A linear left inverse `ρ` of `β` makes `LinearMap.range β` and `LinearMap.ker ρ`
complementary in the ambient module. The domain of `β` needs only an additive
commutative monoid; additive inverses are used only in the ambient module.
-/

@[expose] public section

universe uR uM uN

namespace LinearMap

variable {R : Type uR} {M : Type uM} {N : Type uN}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- The range of a linear map with a linear left inverse complements the kernel of that left
inverse. Only the ambient module needs additive inverses. -/
theorem isCompl_range_ker_of_leftInverse
    (β : M →ₗ[R] N) (ρ : N →ₗ[R] M)
    (h : Function.LeftInverse ρ β) :
    IsCompl (LinearMap.range β) (LinearMap.ker ρ) := by
  have hβ : Function.Injective β := h.injective
  let p : N →ₗ[R] N := β.comp ρ
  have hp (a : N) : p (p a) = p a := by
    change β (ρ (β (ρ a))) = β (ρ a)
    rw [h (ρ a)]
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨m, rfl⟩ hm
    have hm0 : m = 0 := (h m).symm.trans (LinearMap.mem_ker.mp hm)
    rw [hm0, map_zero]
  · rw [codisjoint_iff_le_sup]
    intro a _
    have hres : a - p a ∈ LinearMap.ker ρ := by
      rw [LinearMap.mem_ker]
      apply hβ
      change p (a - p a) = β 0
      rw [map_sub, hp a, sub_self, map_zero]
    have hsum := Submodule.add_mem_sup
      (show p a ∈ LinearMap.range β from ⟨ρ a, rfl⟩) hres
    rw [add_comm (p a), sub_add_cancel] at hsum
    exact hsum

end LinearMap
