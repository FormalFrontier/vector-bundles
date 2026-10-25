/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.ScalarEnd
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum

/-!
# Scalar multiplication on real and complex lines

The homothety family sends `3` to `6` for the scalar `2` on a trivial real line and sends
`I` to `-1` for the scalar `I` on a trivial complex line. The latter is complex-linear
scalar multiplication, not a Hermitian pairing.

The endomorphism-bundle projection and chart laws use only the bundle structures obtained
from the original line bundle. The empty base requires no selected point or vector.
-/

@[expose] public section

universe uκ uB uL

noncomputable section

open Bundle

namespace VectorBundle

/-- Scalar two acts on three as six on a trivial real line. -/
theorem realLine_homothety_two (b : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ
      (ContinuousLinearMap.id ℝ (Trivial ℝ ℝ b)) 2 3 = 6 := by
  norm_num [ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Scalar `I` sends `I` to `-1` on a trivial complex line. -/
theorem complexLine_homothety_I (b : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℂ
      (ContinuousLinearMap.id ℂ (Trivial ℝ ℂ b)) Complex.I Complex.I = -1 := by
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] using Complex.I_mul_I

section OriginalLine

variable (κ : Type uκ) [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B] (L : B → Type uL)
  [∀ b, AddCommGroup (L b)] [∀ b, Module κ (L b)]
  [∀ b, TopologicalSpace (L b)] [TopologicalSpace (TotalSpace κ L)]
  [FiberBundle κ L] [VectorBundle κ κ L]

-- These notations expand to stock dictionaries on the original fibers and total space.
local notation "hadd" b =>
  ContinuousAddEquiv.isTopologicalAddGroup
    (ContinuousLinearEquiv.toContinuousAddEquiv (continuousLinearEquivAt κ κ L b))
local notation "hsmul" b => ContinuousLinearEquiv.continuousSMul (continuousLinearEquivAt κ κ L b)
local notation "tEnd" => @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  κ _ κ _ (RingHom.id κ) B κ _ _ L _ _ _ κ _ _ L _ _ _ _ _ _ _ _ _ _
  (fun b ↦ hadd b) (fun b ↦ hsmul b) _
local notation "tH" b => @ContinuousLinearMap.topologicalSpace κ κ _ _
  (RingHom.id κ) (L b) (L b) _ _ _ _ _ _ (hadd b)
local notation "cadd" b => @IsTopologicalAddGroup.toContinuousAdd (L b) _ _ (hadd b)
local notation "hconst" b => @ContinuousSMul.continuousConstSMul κ (L b) _ _ _ (hsmul b)
local notation "aH" b => @ContinuousLinearMap.addCommMonoid κ κ _ _
  (RingHom.id κ) (L b) _ _ (L b) _ _ _ _ (cadd b)
local notation "mH" b => @ContinuousLinearMap.module κ κ κ _ _ _
  (L b) _ _ _ (L b) _ _ _ _ _ (hconst b) (RingHom.id κ) (cadd b)

local notation "fbEnd" => @Bundle.ContinuousLinearMap.fiberBundle
  κ _ κ _ (RingHom.id κ) B κ _ _ L _ _ _ κ _ _ L _ _ _ _ _ _ _ _ _ _
  (fun b ↦ hadd b) (fun b ↦ hsmul b) _
local notation "vbEnd" => @Bundle.ContinuousLinearMap.vectorBundle
  κ _ κ _ (RingHom.id κ) B κ _ _ L _ _ _ κ _ _ L _ _ _ _ _ _ _ _ _ _
  (fun b ↦ hadd b) (fun b ↦ hsmul b) _
local notation "endChart" b => @continuousLinearEquivAt κ B (κ →L[κ] κ)
  (fun b ↦ L b →L[κ] L b) _ (fun b ↦ aH b) (fun b ↦ mH b) _ _ _
  tEnd (fun b ↦ tH b) fbEnd vbEnd b

/-- The endomorphism bundle has continuous projection with its bundle topology. -/
theorem continuous_lineEnd_proj :
    @Continuous (TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)) B tEnd _
      (fun p ↦ p.proj) := by
  let : ∀ b, IsTopologicalAddGroup (L b) := fun b ↦ hadd b
  let : ∀ b, ContinuousSMul κ (L b) := fun b ↦ hsmul b
  exact FiberBundle.continuous_proj (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)

/-- The endomorphism-bundle chart and its inverse cancel on the original fiber. -/
theorem lineEnd_chart_symm_apply (b : B) (A : L b →L[κ] L b) :
    (@ContinuousLinearEquiv.symm κ κ _ _ (RingHom.id κ) (RingHom.id κ) _ _
      (L b →L[κ] L b) (tH b) (aH b) (κ →L[κ] κ) _ _ (mH b) _
      (endChart b)) ((endChart b) A) = A := by
  let : ∀ b, IsTopologicalAddGroup (L b) := fun b ↦ hadd b
  let : ∀ b, ContinuousSMul κ (L b) := fun b ↦ hsmul b
  exact (endChart b).symm_apply_apply A

/-- Reading a scalar from a fiber endomorphism reproduces its action on every vector. -/
theorem scalarEndHomeomorph_symm_smul (b : B) (A : L b →L[κ] L b) (v : L b) :
    ((@Homeomorph.symm (B × κ)
      (TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)) _ tEnd
      (scalarEndHomeomorph κ L)) (TotalSpace.mk' (κ →L[κ] κ) b A)).2 • v = A v := by
  let : ∀ b, IsModuleTopology κ (L b) := isModuleTopology_line κ L
  let : ∀ b, IsTopologicalAddGroup (L b) := fun b ↦ hadd b
  let : ∀ b, ContinuousSMul κ (L b) := fun b ↦ hsmul b
  let : ∀ b, T2Space (L b) := t2Space_line κ L
  let : ∀ b, Module.Invertible κ (L b) := invertible_line κ L
  rw [scalarEndHomeomorph_symm_apply]
  exact ContinuousLinearMap.scalarEndEquiv_symm_smul κ (L b) A v

end OriginalLine

/-- The endomorphism bundle of the trivial line over the empty base is empty. -/
theorem isEmpty_emptyLineEnd :
    IsEmpty (TotalSpace (ℝ →L[ℝ] ℝ) (fun b : Empty ↦ Trivial Empty ℝ b →L[ℝ] Trivial Empty ℝ b)) :=
  ⟨fun p ↦ nomatch p.proj⟩

/-- The product over the empty base is empty as well. -/
theorem isEmpty_emptyScalarProduct : IsEmpty (Empty × ℝ) :=
  ⟨fun p ↦ nomatch p.1⟩

/-- The total-space scalar endomorphism homeomorphism sends two to an endomorphism
that takes three to six on the trivial real line. -/
theorem realLine_scalarEndHomeomorph_two (b : ℝ) :
    ((scalarEndHomeomorph ℝ (Trivial ℝ ℝ)) (b, 2)).snd 3 = 6 := by
  rw [scalarEndHomeomorph_apply]
  exact realLine_homothety_two b

/-- The total-space scalar endomorphism homeomorphism sends `I` to an endomorphism
that takes `I` to `-1` on the trivial complex line. -/
theorem complexLine_scalarEndHomeomorph_I (b : ℝ) :
    ((scalarEndHomeomorph ℂ (Trivial ℝ ℂ)) (b, Complex.I)).snd Complex.I = -1 := by
  rw [scalarEndHomeomorph_apply]
  exact complexLine_homothety_I b

/-- The inverse total-space homeomorphism reads the base and scalar two from the
stock homothety on a trivial real line. -/
theorem realLine_scalarEndHomeomorph_symm_two (b : ℝ) :
    (scalarEndHomeomorph ℝ (Trivial ℝ ℝ)).symm
      (TotalSpace.mk' (ℝ →L[ℝ] ℝ) b
        (ContinuousLinearMap.toSpanSingleton ℝ
          (ContinuousLinearMap.id ℝ (Trivial ℝ ℝ b)) 2)) = (b, 2) := by
  rw [scalarEndHomeomorph_symm_apply, ContinuousLinearMap.scalarEndEquiv_self]
  simp [ContinuousLinearMap.toSpanSingletonCLE_symm_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The inverse total-space homeomorphism reads the base and scalar `I` from the
stock homothety on a trivial complex line. -/
theorem complexLine_scalarEndHomeomorph_symm_I (b : ℝ) :
    (scalarEndHomeomorph ℂ (Trivial ℝ ℂ)).symm
      (TotalSpace.mk' (ℂ →L[ℂ] ℂ) b
        (ContinuousLinearMap.toSpanSingleton ℂ
          (ContinuousLinearMap.id ℂ (Trivial ℝ ℂ b)) Complex.I)) = (b, Complex.I) := by
  rw [scalarEndHomeomorph_symm_apply, ContinuousLinearMap.scalarEndEquiv_self]
  simp [ContinuousLinearMap.toSpanSingletonCLE_symm_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

end VectorBundle
