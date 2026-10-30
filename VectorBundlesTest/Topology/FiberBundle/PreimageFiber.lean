/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.PreimageFiber
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restricting original-fibre linear models to a closed cylinder

The example constructs the auxiliary fibre models over `U × Icc a b` by composing the
canonical restriction bridge with the given models of the original fibres. The inverse
still returns exactly the original total-space value supplied by the given model.
-/

@[expose] public section

section

universe uX uT uZ uR uF

variable {X : Type uX} {T : Type uT} {Z : Type uZ} {R : Type uR} {F : Type uF}
variable [TopologicalSpace X] [TopologicalSpace T] [Preorder T]
variable [Semiring R] [AddCommMonoid F] [Module R F]
variable (p : Z → X × T) (U : Set X) (a b : T)
variable [∀ x : X × T, AddCommMonoid {z : Z // p z = x}]
variable [∀ x : X × T, Module R {z : Z // p z = x}]

attribute [local instance] Set.restrictPreimageFiberAddCommMonoid
  Set.restrictPreimageFiberModule

/-- The given original-fibre models induce models of the restricted fibres without
changing the underlying original total-space values of inverse images. -/
theorem VectorBundlesTest.restrictPreimageFiber_closedInterval_models
    (K : ∀ x : X × T, {z : Z // p z = x} ≃ₗ[R] F) :
    ∃ Kaux : ∀ c : U × Set.Icc a b,
        {z : p ⁻¹' (U ×ˢ Set.Icc a b) //
          (Homeomorph.Set.prod U (Set.Icc a b)).toEquiv
            ((U ×ˢ Set.Icc a b).restrictPreimage p z) = c} ≃ₗ[R] F,
      ∀ (c : U × Set.Icc a b) (v : F),
        ((Kaux c).symm v).val.val = ((K (c.1.val, c.2.val)).symm v).val := by
  refine ⟨fun c =>
    (LinearEquiv.restrictPreimageFiber R p (Homeomorph.Set.prod U (Set.Icc a b)).toEquiv c).trans
      (K (c.1.val, c.2.val)), ?_⟩
  intro c v
  exact LinearEquiv.restrictPreimageFiber_trans_symm_apply_val_val R p
    (Homeomorph.Set.prod U (Set.Icc a b)).toEquiv c (K (c.1.val, c.2.val)) v

end
