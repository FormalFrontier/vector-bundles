/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.SemilinearEvaluation
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Examples of semilinear bundle evaluation

Scalar multiplication in the trivial line bundle gives the identity-homomorphism specialization,
with both the semilinear and linear evaluation lemmas. Complex conjugation gives a genuinely
semilinear evaluation, and a scalar Hermitian pairing illustrates two-argument evaluation.
-/

@[expose] public section

noncomputable section

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]

private lemma continuousWithinAt_trivial_hom
    {𝕜₁ 𝕜₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂]
    {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
    {b : M → B} {f : M → F₁ →SL[σ] F₂} {s : Set M} {x : M}
    (hb : ContinuousWithinAt b s x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' (F₁ →SL[σ] F₂)
      (E := fun y ↦ Trivial B F₁ y →SL[σ] Trivial B F₂ y) (b m) (f m)) s x := by
  rw [continuousWithinAt_hom_bundle]
  simpa [inCoordinates] using And.intro hb hf

private lemma continuousWithinAt_trivial_section
    {F : Type*} [TopologicalSpace F] {b : M → B} {v : M → F} {s : Set M} {x : M}
    (hb : ContinuousWithinAt b s x) (hv : ContinuousWithinAt v s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F (E := Trivial B F) (b m) (v m)) s x :=
  (Trivial.homeomorphProd B F).symm.continuous.continuousAt.comp_continuousWithinAt (hb.prodMk hv)

-- Multiplication in the trivial line bundle, through the identity-homomorphism bridge.
private theorem continuousWithinAt_trivial_mul_id
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {b : M → B} {a v : M → 𝕜}
    {s : Set M} {x : M} (hb : ContinuousWithinAt b s x)
    (ha : ContinuousWithinAt a s x) (hv : ContinuousWithinAt v s x) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' 𝕜 (E := Trivial B 𝕜) (b m) (a m * v m)) s x := by
  have hϕ := continuousWithinAt_trivial_hom hb
    (ha.smul (continuousWithinAt_const (b := ContinuousLinearMap.id 𝕜 𝕜)))
  simpa using hϕ.clm_bundle_apply_id (continuousWithinAt_trivial_section hb hv)

-- The same identity case is an application of Mathlib's linear evaluation lemma, with no
-- conversions of the continuity hypothesis on the hom-bundle.
private theorem continuousWithinAt_trivial_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {b : M → B} {a v : M → 𝕜}
    {s : Set M} {x : M} (hb : ContinuousWithinAt b s x)
    (ha : ContinuousWithinAt a s x) (hv : ContinuousWithinAt v s x) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' 𝕜 (E := Trivial B 𝕜) (b m) (a m * v m)) s x := by
  have hϕ := continuousWithinAt_trivial_hom hb
    (ha.smul (continuousWithinAt_const (b := ContinuousLinearMap.id 𝕜 𝕜)))
  simpa using hϕ.clm_bundle_apply (continuousWithinAt_trivial_section hb hv)

/-- A continuous coefficient times conjugation gives a continuous section of the trivial
complex line bundle, using the nonidentity isometric homomorphism `starRingEnd ℂ`. -/
theorem Bundle.Trivial.continuous_weighted_conjugate {b : M → B} {a v : M → ℂ}
    (hb : Continuous b) (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ)
      (b m) (a m * star (v m))) := by
  have hϕ : Continuous (fun m ↦ TotalSpace.mk' (ℂ →L⋆[ℂ] ℂ)
      (E := fun y ↦ Trivial B ℂ y →L⋆[ℂ] Trivial B ℂ y)
      (b m) (a m • (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap)) := by
    rw [continuous_iff_continuousAt]
    intro x
    simpa only [continuousWithinAt_univ, Pi.smul_apply'] using continuousWithinAt_trivial_hom
      (s := Set.univ) (x := x) hb.continuousWithinAt
      (ha.smul (continuous_const (y :=
        (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap))).continuousWithinAt
  have hv' : Continuous (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ) (b m) (v m)) :=
    (Trivial.homeomorphProd B ℂ).symm.continuous.comp (hb.prodMk hv)
  simpa using hϕ.clm_bundle_apply_semilinear (F₂ := ℂ) (E₂ := Trivial B ℂ) hv'

-- A continuous scalar multiple of the Hermitian pairing on the trivial complex line bundle.
private theorem continuous_trivial_weighted_hermitian
    {b : M → B} {a v w : M → ℂ} (hb : Continuous b) (ha : Continuous a)
    (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ)
      (b m) (a m * (star (v m) * w m))) := by
  let P : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).comp (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap
  have hψ : Continuous (fun m ↦ TotalSpace.mk' (ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ)
      (E := fun y ↦ Trivial B ℂ y →L⋆[ℂ] Trivial B ℂ y →L[ℂ] Trivial B ℂ y)
      (b m) (a m • P)) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [continuousAt_hom_bundle]
    refine ⟨hb.continuousAt, ?_⟩
    have heq : (fun m ↦ inCoordinates ℂ (Trivial B ℂ)
        (ℂ →L[ℂ] ℂ) (fun y ↦ Trivial B ℂ y →L[ℂ] Trivial B ℂ y)
        (b x) (b m) (b x) (b m) (a m • P)) = (fun m ↦ a m • P) := by
      ext m z
      simp [inCoordinates, hom_trivializationAt, Trivialization.continuousLinearMapAt_apply,
        Trivialization.continuousLinearMap_apply]
    rw [heq]
    exact (ha.smul continuous_const).continuousAt
  have hv' : Continuous (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ) (b m) (v m)) :=
    (Trivial.homeomorphProd B ℂ).symm.continuous.comp (hb.prodMk hv)
  have hw' : Continuous (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ) (b m) (w m)) :=
    (Trivial.homeomorphProd B ℂ).symm.continuous.comp (hb.prodMk hw)
  simpa [P] using hψ.clm_bundle_apply₂_semilinear (F₃ := ℂ) (E₃ := Trivial B ℂ) hv' hw'

-- Distinct scalar fields, with the nonsurjective isometric inclusion from ℝ to ℂ.
private theorem continuousAt_trivial_mul_ofReal {b : M → B} {a : M → ℂ} {v : M → ℝ} {x : M}
    (hb : ContinuousAt b x) (ha : ContinuousAt a x) (hv : ContinuousAt v x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' ℂ (E := Trivial B ℂ)
      (b m) (a m * (v m : ℂ))) x := by
  let : RingHomIsometric (algebraMap ℝ ℂ) := ⟨by intro r; simp⟩
  let ι : ℝ →SL[algebraMap ℝ ℂ] ℂ :=
    { toFun := fun r ↦ (r : ℂ)
      map_add' := by intros; simp
      map_smul' := by intros; simp
      cont := Complex.continuous_ofReal }
  have hϕ := continuousWithinAt_trivial_hom (s := Set.univ) hb.continuousWithinAt
    (ha.smul (continuousAt_const (y := ι))).continuousWithinAt
  have hv' := continuousWithinAt_trivial_section (s := Set.univ) hb.continuousWithinAt
    hv.continuousWithinAt
  rw [continuousWithinAt_univ] at hϕ hv'
  simpa [ι] using hϕ.clm_bundle_apply_semilinear (F₂ := ℂ) (E₂ := Trivial B ℂ) hv'
