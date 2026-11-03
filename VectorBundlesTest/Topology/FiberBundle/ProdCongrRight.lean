/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.FiberBundle.Prod
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A base-dependent translation of the right factor

On constant real fibers over the real line, translating the right fiber by the base preserves
the original first total-space point, but is not the identity on the product total space.
-/

open Bundle

noncomputable section

namespace FiberBundle.Prod

/-- Subtracting the base reverses addition of the base in the right coordinate. -/
public theorem translation_leftInverse :
    Function.LeftInverse
      (fun p : ℝ × ℝ ↦ (p.1, p.2 - p.1))
      (fun p : ℝ × ℝ ↦ (p.1, p.2 + p.1)) := by
  intro p
  simp

private def shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p ↦ (p.1, p.2 + p.1)
      invFun := fun p ↦ (p.1, p.2 - p.1)
      left_inv := translation_leftInverse
      right_inv := by intro p; simp }
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add continuous_fst)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst)

private def shearTotal :
    TotalSpace ℝ (Trivial ℝ ℝ) ≃ₜ TotalSpace ℝ (Trivial ℝ ℝ) :=
  (Trivial.homeomorphProd ℝ ℝ).trans
    (shear.trans (Trivial.homeomorphProd ℝ ℝ).symm)

private theorem shearTotal_apply (p : TotalSpace ℝ (Trivial ℝ ℝ)) :
    shearTotal p = TotalSpace.mk' ℝ p.proj (p.snd + p.proj) := rfl

private theorem shearTotal_proj (p : TotalSpace ℝ (Trivial ℝ ℝ)) :
    (shearTotal p).proj = p.proj := rfl

local notation "J" =>
  homeomorphCongrRight ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ)
    shearTotal shearTotal_proj

/-- A base-dependent translation fixes the first total factor in both directions and moves
the zero pair over the base point `1` to a nonzero right coordinate. -/
private theorem homeomorphCongrRight_translation :
    totalSpaceFst ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ)
      (J (TotalSpace.mk' (ℝ × ℝ) 1 (0, 0))) = TotalSpace.mk' ℝ 1 0 ∧
    totalSpaceFst ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ)
      (@Homeomorph.symm _ _ _ _ J (TotalSpace.mk' (ℝ × ℝ) 1 (0, 1))) =
        TotalSpace.mk' ℝ 1 0 ∧
    J (TotalSpace.mk' (ℝ × ℝ) 1 (0, 0)) =
      (TotalSpace.mk' (ℝ × ℝ) 1 (0, 1) :
        TotalSpace (ℝ × ℝ) (fun _ : ℝ => ℝ × ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact totalSpaceFst_homeomorphCongrRight
      ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) shearTotal shearTotal_proj _
  · exact totalSpaceFst_homeomorphCongrRight_symm
      ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) shearTotal shearTotal_proj _
  · apply totalSpace_ext ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ)
    · exact totalSpaceFst_homeomorphCongrRight
        ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) shearTotal shearTotal_proj _
    · simpa only [totalSpaceSnd_mk, shearTotal_apply, zero_add] using
        (totalSpaceSnd_homeomorphCongrRight
          ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ) shearTotal shearTotal_proj
          (TotalSpace.mk' (ℝ × ℝ) 1 (0, 0)))

end FiberBundle.Prod
