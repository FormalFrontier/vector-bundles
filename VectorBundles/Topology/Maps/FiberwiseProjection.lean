/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Maps.FiberwiseSplitting
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous families of prescribed fibre projections

Let `p : T → B` have given module structures on its equality fibres, and let
`β b` and `ρ b` be linear maps between those fibres and a finite-dimensional
normed space `A`, with `ρ b (β b u) = u`. Continuity of the two total maps gives
`ContinuousMap.fiberwiseProjection`, an operator-norm-continuous family of
idempotents acting by `β b (ρ b a)`.

The complementary family is the existing continuous-map expression
`1 - (ContinuousMap.subtypeVal _).comp P`. Its characteristic action, kernel
relation and decomposition laws use the prescribed maps on the original
carriers. Extensionality is inherited from continuous maps, subtypes and
continuous linear maps.

## Implementation notes

The inverse of `Homeomorph.fiberwiseSumKer` supplies joint continuity of the
residual. Fixed-vector evaluations and Mathlib's `continuous_clm_apply` then
give continuity in the original operator norm. The fibres retain their given
module structures and subspace topologies; no fibre norm or continuity of fibre
operations is required. The scalar field is complete, but no completeness or
nontriviality assumption on `A` is added. No orthogonality or commutation at
different base points is asserted. The standard finite-Pi norm is the sup norm,
not a Euclidean norm.

## References

* `Homeomorph.fiberwiseSumKer` provides sum–kernel coordinates on the original
  total-space subspace, using ProjectiveModules' right-inverse splitting.
* Mathlib's finite-dimensional `continuous_clm_apply` provides continuity of
  operator families from continuity of their evaluations.
* Mathlib's `IsIdempotentElem` and `ContinuousMap` interfaces provide the
  idempotence tag, complementary algebra and pointwise continuous-map operations.
-/

@[expose] public section

universe uK uA uB uT

namespace ContinuousMap

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
  {B : Type uB} [TopologicalSpace B] {T : Type uT} [TopologicalSpace T]
  (p : T → B) [∀ b, AddCommMonoid {t : T // p t = b}]
  [∀ b, Module K {t : T // p t = b}]
  (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
  (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
  (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
  (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
  (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val))

/-- The prescribed projections `β b ∘ ρ b`, as an operator-norm-continuous
family of idempotent continuous linear endomorphisms.

The ambient finite-dimensional space keeps its original norm and topology.
The equality fibres keep their original module structures and subspace
topologies, without norms or continuity of their module operations. -/
def fiberwiseProjection : ContinuousMap B {P : A →L[K] A // IsIdempotentElem P} := by
  let e := Homeomorph.fiberwiseSumKer p
    (fun b ↦ (β b).toAddMonoidHom) (fun b ↦ (ρ b).toAddMonoidHom)
    hρβ hβTotal hρTotal
  have hQ : Continuous (fun y : B × A ↦ y.2 - β y.1 (ρ y.1 y.2)) := by
    have h : Continuous (fun y : B × A ↦ (e.symm y).val.2) :=
      continuous_snd.comp (continuous_subtype_val.comp e.continuous_symm)
    exact h.congr (fun y ↦ congrArg Prod.snd
      (Homeomorph.fiberwiseSumKer_symm_apply_val p
        (fun b ↦ (β b).toAddMonoidHom) (fun b ↦ (ρ b).toAddMonoidHom)
        hρβ hβTotal hρTotal y))
  have hP : Continuous (fun y : B × A ↦ β y.1 (ρ y.1 y.2)) := by
    exact (continuous_snd.sub hQ).congr
      (fun y ↦ sub_sub_cancel y.2 (β y.1 (ρ y.1 y.2)))
  let P (b : B) : A →L[K] A :=
    { toLinearMap := (β b).comp (ρ b)
      cont := hP.comp ((continuous_const : Continuous (fun _ : A ↦ b)).prodMk
        continuous_id) }
  have hIdem (b : B) : IsIdempotentElem (P b) := by
    change P b * P b = P b
    ext a
    exact congrArg (β b) (hρβ b (ρ b a))
  have hPc : Continuous P := continuous_clm_apply.mpr (fun a ↦
    hP.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : B ↦ a))))
  exact ⟨fun b ↦ ⟨P b, hIdem b⟩, hPc.subtype_mk (fun b ↦ hIdem b)⟩

/-- The prescribed projection acts by the original linear composition. -/
@[simp]
theorem fiberwiseProjection_apply (b : B) (a : A) :
    (fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val a = β b (ρ b a) := rfl

/-- The prescribed projection has the same kernel as the prescribed retraction. -/
@[simp]
theorem fiberwiseProjection_ker (b : B) :
    LinearMap.ker
      ((fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val.toLinearMap) =
        LinearMap.ker (ρ b) := by
  have hP :
      (fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val.toLinearMap =
        (β b).comp (ρ b) := by
    ext a
    exact fiberwiseProjection_apply p β ρ hρβ hβTotal hρTotal b a
  rw [hP]
  exact LinearMap.ker_comp_of_ker_eq_bot (ρ b)
    (LinearMap.ker_eq_bot_of_injective (hρβ b).injective)

local notation "P" => fiberwiseProjection p β ρ hρβ hβTotal hρTotal
local notation "Q" =>
  (1 : ContinuousMap B (A →L[K] A)) -
    ContinuousMap.comp (ContinuousMap.subtypeVal (fun R : A →L[K] A ↦ IsIdempotentElem R)) P

/-- The existing complementary continuous-map expression acts by the residual. -/
theorem fiberwiseProjection_complement_apply (b : B) (a : A) :
    Q b a = a - β b (ρ b a) := rfl

/-- The complementary component lies in the kernel of the prescribed retraction.
This follows from membership in the sum–kernel homeomorphism's inverse subspace. -/
theorem fiberwiseProjection_rho_complement (b : B) (a : A) :
    ρ b (Q b a) = 0 := by
  rw [fiberwiseProjection_complement_apply]
  let e := Homeomorph.fiberwiseSumKer p
    (fun b ↦ (β b).toAddMonoidHom) (fun b ↦ (ρ b).toAddMonoidHom)
    hρβ hβTotal hρTotal
  have hval : (e.symm (b, a)).val = ((ρ b a).val, a - β b (ρ b a)) :=
    Homeomorph.fiberwiseSumKer_symm_apply_val p
      (fun b ↦ (β b).toAddMonoidHom) (fun b ↦ (ρ b).toAddMonoidHom)
      hρβ hβTotal hρTotal (b, a)
  have h := (e.symm (b, a)).property
  change ρ (p (e.symm (b, a)).val.1) (e.symm (b, a)).val.2 = 0 at h
  rw [hval] at h
  rw [(ρ b a).property] at h
  exact h

/-- The complementary family vanishes on the image of the prescribed encoder. -/
theorem fiberwiseProjection_complement_beta (b : B) (u : {t : T // p t = b}) :
    Q b (β b u) = 0 := by
  rw [fiberwiseProjection_complement_apply, hρβ b u, sub_self]

/-- Each ambient vector is the sum of its prescribed image and kernel components. -/
theorem fiberwiseProjection_add_complement_apply (b : B) (a : A) :
    (P b).val a + Q b a = a := by
  rw [fiberwiseProjection_apply, fiberwiseProjection_complement_apply, add_comm, sub_add_cancel]

end ContinuousMap
