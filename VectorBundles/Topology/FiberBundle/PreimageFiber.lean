/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Set.Restrict
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Fibres of a restricted projection

Restricting a map `p : Z → B` to the preimage of `S : Set B` does not change its fibres.
The same holds after reindexing the restricted base by an arbitrary equivalence `k : S ≃ C`.
Both directions of the resulting equivalence preserve the underlying element of `Z`.

* `Equiv.restrictPreimageFiber` is the equivalence of fibres.
* `Homeomorph.restrictPreimageFiber` uses the existing subspace topologies and requires only
  a topology on `Z`, not on either base.
* `Set.restrictPreimageFiberAddCommMonoid` and `Set.restrictPreimageFiberModule` transport
  the given algebra on the original fibres to the auxiliary restricted fibres.
* `LinearEquiv.restrictPreimageFiber` is the resulting linear equivalence.

The algebraic structures are reducible non-instances. A caller can install their entire
families using `letI := Set.restrictPreimageFiberAddCommMonoid p k` and then
`letI := Set.restrictPreimageFiberModule R p k`. No structure on an original fibre, and
no topology, is transported or replaced.
-/

@[expose] public section

universe uB uZ uC uR uF

variable {B : Type uB} {Z : Type uZ} {C : Type uC}
variable (R : Type uR)
variable (p : Z → B) {S : Set B} (k : S ≃ C)

namespace Equiv

/-- The equation defining a fibre after restriction and reindexing is equivalent to the
corresponding original fibre equation. -/
theorem restrictPreimage_eq_iff (z : p ⁻¹' S) (c : C) :
    k (S.restrictPreimage p z) = c ↔ p z.val = (k.symm c).val := by
  constructor
  · intro h
    have hs : S.restrictPreimage p z = k.symm c :=
      k.injective (h.trans (k.apply_symm_apply c).symm)
    exact congrArg Subtype.val hs
  · intro h
    have hs : S.restrictPreimage p z = k.symm c := Subtype.ext h
    exact (congrArg k hs).trans (k.apply_symm_apply c)

/-- The fibre of a restricted and reindexed projection is equivalent to the original fibre.
Both directions preserve the underlying element of the original total space. -/
def restrictPreimageFiber (c : C) :
    {z : p ⁻¹' S // k (S.restrictPreimage p z) = c} ≃
      {z : Z // p z = (k.symm c).val} :=
  (Equiv.subtypeEquivRight (fun z => restrictPreimage_eq_iff p k z c)).trans
    (Equiv.subtypeSubtypeEquivSubtype
      (p := fun z : Z => p z ∈ S)
      (q := fun z : Z => p z = (k.symm c).val)
      (fun {_} h => h.symm ▸ (k.symm c).property))

@[simp]
theorem restrictPreimageFiber_apply_val (c : C)
    (z : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    (restrictPreimageFiber p k c z).val = z.val.val := rfl

@[simp]
theorem restrictPreimageFiber_symm_apply_val_val (c : C)
    (z : {z : Z // p z = (k.symm c).val}) :
    ((restrictPreimageFiber p k c).symm z).val.val = z.val := rfl

end Equiv

namespace Homeomorph

variable [TopologicalSpace Z]

/-- The fibres of a restricted and reindexed projection are homeomorphic to the original
fibres with their existing nested-subspace and subspace topologies. No topology on either
base or continuity of the base equivalence is required. -/
def restrictPreimageFiber (c : C) :
    {z : p ⁻¹' S // k (S.restrictPreimage p z) = c} ≃ₜ
      {z : Z // p z = (k.symm c).val} where
  toEquiv := Equiv.restrictPreimageFiber p k c
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem restrictPreimageFiber_toEquiv (c : C) :
    (restrictPreimageFiber p k c).toEquiv = Equiv.restrictPreimageFiber p k c := rfl

@[simp]
theorem restrictPreimageFiber_apply_val (c : C)
    (z : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    (restrictPreimageFiber p k c z).val = z.val.val := rfl

@[simp]
theorem restrictPreimageFiber_symm_apply_val_val (c : C)
    (z : {z : Z // p z = (k.symm c).val}) :
    ((restrictPreimageFiber p k c).symm z).val.val = z.val := rfl

end Homeomorph

section Algebra

variable [∀ b : B, AddCommMonoid {z : Z // p z = b}]

namespace Set

/-- Transfer the given additive monoids on the original fibres only to the auxiliary
fibres of the restricted and reindexed projection. This is not a global instance. -/
abbrev restrictPreimageFiberAddCommMonoid :
    ∀ c : C, AddCommMonoid {z : p ⁻¹' S // k (S.restrictPreimage p z) = c} :=
  fun c => (Equiv.restrictPreimageFiber p k c).addCommMonoid

end Set

attribute [local instance] Set.restrictPreimageFiberAddCommMonoid

namespace Set

/-- Zero in an auxiliary fibre is transported from zero in the given original fibre. -/
theorem restrictPreimageFiber_zero_def (c : C) :
    (0 : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) =
      (Equiv.restrictPreimageFiber p k c).symm 0 := rfl

/-- Addition in an auxiliary fibre is transported from addition in the given original fibre. -/
theorem restrictPreimageFiber_add_def (c : C)
    (z w : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    z + w = (Equiv.restrictPreimageFiber p k c).symm
      (Equiv.restrictPreimageFiber p k c z + Equiv.restrictPreimageFiber p k c w) := rfl

end Set

namespace Equiv

@[simp]
theorem restrictPreimageFiber_zero (c : C) :
    restrictPreimageFiber p k c (0 : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) = 0 :=
  (restrictPreimageFiber p k c).addEquiv.map_zero

@[simp]
theorem restrictPreimageFiber_add (c : C)
    (z w : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    restrictPreimageFiber p k c (z + w) =
      restrictPreimageFiber p k c z + restrictPreimageFiber p k c w :=
  (restrictPreimageFiber p k c).addEquiv.map_add z w

end Equiv

variable [Semiring R]
variable [∀ b : B, Module R {z : Z // p z = b}]

namespace Set

/-- Transfer the given modules on original fibres to the auxiliary restricted fibres,
using `AddEquiv.module` and the canonical transferred additive monoids. This is not a
global instance, and it makes no change to the given original fibre modules. -/
abbrev restrictPreimageFiberModule :
    ∀ c : C, Module R {z : p ⁻¹' S // k (S.restrictPreimage p z) = c} :=
  fun c => (Equiv.restrictPreimageFiber p k c).addEquiv.module R

end Set

attribute [local instance] Set.restrictPreimageFiberModule

namespace Set

/-- Scalar multiplication in an auxiliary fibre is transported from scalar multiplication
in the given original fibre. -/
theorem restrictPreimageFiber_smul_def (c : C) (r : R)
    (z : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    r • z = (Equiv.restrictPreimageFiber p k c).symm
      (r • Equiv.restrictPreimageFiber p k c z) := rfl

end Set

namespace LinearEquiv

/-- The canonical linear equivalence from an auxiliary restricted fibre to the given
original fibre, for the auxiliary structures provided by
`Set.restrictPreimageFiberAddCommMonoid` and `Set.restrictPreimageFiberModule`. -/
def restrictPreimageFiber (c : C) :
    {z : p ⁻¹' S // k (S.restrictPreimage p z) = c} ≃ₗ[R]
      {z : Z // p z = (k.symm c).val} :=
  (Equiv.restrictPreimageFiber p k c).addEquiv.linearEquiv R

@[simp]
theorem restrictPreimageFiber_toEquiv (c : C) :
    (restrictPreimageFiber R p k c).toEquiv = Equiv.restrictPreimageFiber p k c := rfl

@[simp]
theorem restrictPreimageFiber_apply_val (c : C)
    (z : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    (restrictPreimageFiber R p k c z).val = z.val.val := rfl

@[simp]
theorem restrictPreimageFiber_symm_apply_val_val (c : C)
    (z : {z : Z // p z = (k.symm c).val}) :
    ((restrictPreimageFiber R p k c).symm z).val.val = z.val := rfl

/-- Composing with a given linear model of the original fibre uses that original model
without altering its module structure. -/
theorem restrictPreimageFiber_trans_apply {F : Type uF} [AddCommMonoid F] [Module R F]
    (c : C) (K : {z : Z // p z = (k.symm c).val} ≃ₗ[R] F)
    (z : {z : p ⁻¹' S // k (S.restrictPreimage p z) = c}) :
    ((restrictPreimageFiber R p k c).trans K) z = K (Equiv.restrictPreimageFiber p k c z) :=
  rfl

/-- Pulling a model vector back to the auxiliary fibre preserves the original total-space
value supplied by the inverse of the given original-fibre model. -/
@[simp]
theorem restrictPreimageFiber_trans_symm_apply_val_val
    {F : Type uF} [AddCommMonoid F] [Module R F]
    (c : C) (K : {z : Z // p z = (k.symm c).val} ≃ₗ[R] F) (v : F) :
    (((restrictPreimageFiber R p k c).trans K).symm v).val.val = (K.symm v).val := rfl

end LinearEquiv

end Algebra
