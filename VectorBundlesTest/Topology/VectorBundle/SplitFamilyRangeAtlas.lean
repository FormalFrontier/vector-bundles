/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Data.Bundle
public import VectorBundles.Topology.Maps.FiberwiseProjection
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas.FiniteAmbient
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Complementary ranges of a split indexed family

This example composes equality-fibre packing, the projection-family construction,
and the finite-ambient range-atlas construction. The two given total maps use the
original family topology. The resulting ranges carry their inherited fibre
structures and the total topology induced by their base-and-ambient value map.
All subtraction takes place in the ambient endomorphism ring.

## References

The construction follows the original-fibre packing, projection-family and
projector-atlas APIs of VectorBundles, and Mathlib's finite-dimensional module
topology theorem.
-/

@[expose] public section

attribute [local instance] VectorBundle.rangeTotalSpaceTopology

universe uK uA uB uP uE

noncomputable section

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
  {B : Type uB} [TopologicalSpace B]
  (P : Type uP) {E : B → Type uE}
  [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
  (β : ∀ b, E b →ₗ[K] A) (ρ : ∀ b, A →ₗ[K] E b)
  (hρβ : ∀ (b : B) (v : E b), ρ b (β b v) = v)
  [TopologicalSpace (Bundle.TotalSpace P E)]
  (hβTotal : Continuous (fun z : Bundle.TotalSpace P E =>
    (z.proj, β z.proj z.snd)))
  (hρTotal : Continuous (fun y : B × A =>
    (Bundle.TotalSpace.mk y.1 (ρ y.1 y.2) : Bundle.TotalSpace P E)))

include hρβ hβTotal hρTotal in
example :
    Bundle.FiniteRankAtlas K P
      (fun b => LinearMap.range
        ((LinearMap.id : A →ₗ[K] A) - (β b).comp (ρ b))) := by
  classical
  let Q : B → A →ₗ[K] A := fun b =>
    (LinearMap.id : A →ₗ[K] A) - (β b).comp (ρ b)
  let S : B → Type uA := fun b => ↥(LinearMap.range (Q b))
  let τP : TopologicalSpace (Bundle.TotalSpace P S) :=
    VectorBundle.rangeTotalSpaceTopology (F := P) Q
  letI := Bundle.TotalSpace.fiberAddCommMonoid (E := E) P
  letI := Bundle.TotalSpace.fiberModule (E := E) K P
  let p : Bundle.TotalSpace P E → B := fun z => z.proj
  let ePack (b : B) : E b ≃ₗ[K] {z : Bundle.TotalSpace P E // p z = b} :=
    Bundle.TotalSpace.fiberLinearEquiv (E := E) K P b
  let βraw (b : B) : {z : Bundle.TotalSpace P E // p z = b} →ₗ[K] A :=
    (β b).comp (ePack b).symm.toLinearMap
  let ρraw (b : B) : A →ₗ[K] {z : Bundle.TotalSpace P E // p z = b} :=
    (ePack b).toLinearMap.comp (ρ b)
  have hρβraw : ∀ b, Function.RightInverse (βraw b) (ρraw b) := by
    intro b u
    calc
      ρraw b (βraw b u) = ePack b ((ePack b).symm u) :=
        congrArg (ePack b) (hρβ b ((ePack b).symm u))
      _ = u := (ePack b).apply_symm_apply u
  have hβrawValue (z : Bundle.TotalSpace P E) :
      βraw (p z) ⟨z, rfl⟩ = β z.proj z.snd :=
    Bundle.TotalSpace.comp_fiberLinearEquiv_symm_apply_self (E := E) K P β z
  have hρrawValue (b : B) (a : A) :
      (ρraw b a).val = (Bundle.TotalSpace.mk b (ρ b a) : Bundle.TotalSpace P E) :=
    Bundle.TotalSpace.fiberLinearEquiv_comp_apply_val (E := E) K P b (ρ b) a
  have hβrawTotal : Continuous (fun z : Bundle.TotalSpace P E =>
      (p z, βraw (p z) ⟨z, rfl⟩)) :=
    hβTotal.congr (fun z =>
      (congrArg (fun a : A => (z.proj, a)) (hβrawValue z)).symm)
  have hρrawTotal : Continuous (fun y : B × A => (ρraw y.1 y.2).val) :=
    hρTotal.congr (fun y => (hρrawValue y.1 y.2).symm)
  let projectionFamily : C(B, {R : A →L[K] A // IsIdempotentElem R}) :=
    ContinuousMap.fiberwiseProjection p βraw ρraw hρβraw hβrawTotal hρrawTotal
  have hProjection (b : B) (a : A) : (projectionFamily b).val a = β b (ρ b a) := by
    calc
      (projectionFamily b).val a = βraw b (ρraw b a) :=
        ContinuousMap.fiberwiseProjection_apply p βraw ρraw
          hρβraw hβrawTotal hρrawTotal b a
      _ = β b (ρ b a) :=
        congrArg (β b) ((ePack b).symm_apply_apply (ρ b a))
  have hresidualContinuous (b : B) :
      Continuous (fun a : A => a - β b (ρ b a)) :=
    (ContinuousLinearMap.id K A - (projectionFamily b).val).continuous.congr
      (fun a => congrArg (fun v : A => a - v) (hProjection b a))
  let Qop (b : B) : A →L[K] A :=
    { toLinearMap := Q b
      cont := hresidualContinuous b }
  have hQop (b : B) : Qop b = ContinuousLinearMap.id K A - (projectionFamily b).val := by
    ext a
    exact congrArg (fun v : A => a - v) (hProjection b a).symm
  have hProjectionContinuous : Continuous (fun b => (projectionFamily b).val) :=
    continuous_subtype_val.comp projectionFamily.continuous
  have hcomplementContinuous :
      Continuous (fun b => ContinuousLinearMap.id K A - (projectionFamily b).val) :=
    continuous_const.sub hProjectionContinuous
  let Qc : C(B, A →L[K] A) :=
    ⟨Qop, hcomplementContinuous.congr (fun b => (hQop b).symm)⟩
  let R (b : B) : A →ₗ[K] A := (β b).comp (ρ b)
  have hR (b : B) : R b * R b = R b := by
    ext a
    exact congrArg (β b) (hρβ b (ρ b a))
  have hQ (b : B) : Q b * Q b = Q b := by
    change (1 - R b) * (1 - R b) = 1 - R b
    simp only [sub_mul, mul_sub, one_mul, mul_one, hR b, sub_self, sub_zero]
  have hid (b : B) : IsIdempotentElem (Qc b) := by
    change Qc b * Qc b = Qc b
    ext a
    change Q b (Q b a) = Q b a
    exact congrArg (fun L : A →ₗ[K] A => L a) (hQ b)
  letI : IsModuleTopology K A :=
    isModuleTopologyOfFiniteDimensional (𝕜 := K) (E := A)
  letI : TopologicalSpace (Bundle.TotalSpace P S) := τP
  -- This change normalizes both the range family and its total-space topology.
  change
    letI : TopologicalSpace
        (Bundle.TotalSpace P (fun b => LinearMap.range (Qc b).toLinearMap)) :=
      VectorBundle.rangeTotalSpaceTopology (F := P) (fun b => (Qc b).toLinearMap)
    Bundle.FiniteRankAtlas K P (fun b => LinearMap.range (Qc b).toLinearMap)
  exact ContinuousLinearMap.finiteRankRangeAtlasOfFiniteDimensional
    (K := K) (A := A) P (fun b => Qc b) Qc.continuous hid

end
