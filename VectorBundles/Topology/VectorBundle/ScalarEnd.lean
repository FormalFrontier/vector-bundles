/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import ProjectiveModules.Invertible.Topology

/-!
# Scalar endomorphisms of a line

Scalar multiplication identifies the continuous endomorphisms of a Hausdorff one-dimensional
topological vector space over a nontrivially normed field with its scalar field. The inverse
scalar acts as the given endomorphism on every vector, without selecting a nonzero vector.

For a line bundle with model fiber equal to the scalar field, these identifications give a
base-preserving homeomorphism from the product of the base and the scalar field to the
endomorphism bundle. The fibers retain their given topologies; the endomorphism fibers use
bounded convergence and the total space uses the topology of the bundle of continuous linear maps.
The base is arbitrary, including empty.

## Implementation notes

The homothety family is `ContinuousLinearMap.toSpanSingleton` applied to the identity
endomorphism. The rank-one hypothesis is Mathlib's `Module.Invertible`, which already implies
finiteness. The module topology on the original line follows from continuity of a linear
coordinate with closed zero kernel. The algebraic comparison uses
`Module.Invertible.toModuleEndRingEquiv` from ProjectiveModules. Fiberwise module topologies and
invertibility are transported along the existing bundle charts, without choosing norms on the
fibers or changing their topologies.

## References

* Mathlib, `Topology.Algebra.Module.Spaces.ContinuousLinearMap` and
  `Topology.VectorBundle.Hom`.
* ProjectiveModules, `Invertible.Topology`, for the module topology and continuous scalar
  endomorphism equivalence, and `Invertible.Endomorphism`, for the algebraic scalar
  endomorphism equivalence contributed by Prism.
-/

@[expose] public section

universe uκ uB uE

noncomputable section

open Bundle

namespace VectorBundle

variable (κ : Type uκ) [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B] (L : B → Type uE)
  [∀ b, AddCommGroup (L b)] [∀ b, Module κ (L b)]
  [∀ b, TopologicalSpace (L b)] [TopologicalSpace (TotalSpace κ L)]
  [FiberBundle κ L] [VectorBundle κ κ L]

/-- Each fiber of a line bundle has the module topology on its given topological space. -/
theorem isModuleTopology_line (b : B) : IsModuleTopology κ (L b) :=
  IsModuleTopology.iso (continuousLinearEquivAt κ κ L b).symm

/-- Each fiber of a line bundle is an invertible module over its scalar field. -/
theorem invertible_line (b : B) : Module.Invertible κ (L b) :=
  Module.Invertible.congr (continuousLinearEquivAt κ κ L b).symm.toLinearEquiv

include κ in
/-- Each fiber of a line bundle is Hausdorff in its given topology. -/
theorem t2Space_line (b : B) : T2Space (L b) :=
  (continuousLinearEquivAt κ κ L b).symm.toHomeomorph.t2Space

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

local notation "Φ" b => @ContinuousLinearMap.scalarEndEquiv κ _ (L b) _ _ _
  (hadd b) (hsmul b) (t2Space_line κ L b) (invertible_line κ L b)

-- A scalar homothety is unchanged by using the same chart in source and target.
private theorem scalarEnd_inCoordinates (b₀ b : B)
    (hb : b ∈ (trivializationAt κ L b₀).baseSet) (a : κ) :
    ContinuousLinearMap.inCoordinates κ L κ L b₀ b b₀ b ((Φ b) a) =
      ContinuousLinearMap.scalarEndEquiv κ κ a := by
  apply DFunLike.ext
  intro v
  dsimp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.scalarEndEquiv_apply, map_smul,
    Trivialization.continuousLinearMapAt_symmL _ hb,
    ContinuousLinearMap.scalarEndEquiv_apply]

/-- The endomorphism bundle of a line bundle is canonically the product of the base and
the scalar field. Both directions preserve the base coordinate. -/
@[no_expose]
noncomputable def scalarEndHomeomorph :
    @Homeomorph (B × κ) (TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b))
      _ tEnd := by
  letI : ∀ b, IsTopologicalAddGroup (L b) := fun b ↦ hadd b
  letI : ∀ b, ContinuousSMul κ (L b) := fun b ↦ hsmul b
  refine
    { toFun := fun p ↦ ⟨p.1, (Φ p.1) p.2⟩
      invFun := fun p ↦ (p.proj, (Φ p.proj).symm p.snd)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rintro ⟨b, a⟩
    exact congrArg (fun c : κ ↦ (b, c)) ((Φ b).symm_apply_apply a)
  · rintro ⟨b, A⟩
    exact congrArg (TotalSpace.mk' (κ →L[κ] κ) b) ((Φ b).apply_symm_apply A)
  · refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
    rw [continuousAt_hom_bundle]
    refine ⟨continuous_fst.continuousAt, ?_⟩
    have hm := (ContinuousLinearMap.scalarEndEquiv κ κ).continuous.continuousAt.comp
      (continuous_snd.continuousAt (x := p₀))
    apply hm.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      ((trivializationAt κ L p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt κ L p₀.1))] with p hp
    exact scalarEnd_inCoordinates κ L p₀.1 p.1 hp p.2
  · have hproj := FiberBundle.continuous_proj (κ →L[κ] κ)
      (fun b ↦ L b →L[κ] L b)
    refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
    let t := trivializationAt (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b) p₀.proj
    have ht : ContinuousAt (fun p ↦ (t p).2) p₀ :=
      (t.continuousAt (FiberBundle.mem_trivializationAt_proj_source)).snd
    have hm := (ContinuousLinearMap.scalarEndEquiv κ κ).symm.continuous.continuousAt.comp ht
    refine hproj.continuousAt.prodMk (hm.congr_of_eventuallyEq ?_)
    filter_upwards [hproj.continuousAt.preimage_mem_nhds
      ((trivializationAt κ L p₀.proj).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt κ L p₀.proj))] with p hp
    apply (ContinuousLinearMap.scalarEndEquiv κ κ).injective
    dsimp only [Function.comp_apply]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change _ = ContinuousLinearMap.inCoordinates κ L κ L p₀.proj p.proj p₀.proj p.proj p.snd
    have h := scalarEnd_inCoordinates κ L p₀.proj p.proj hp ((Φ p.proj).symm p.snd)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- The total-space homeomorphism sends a scalar to its homothety on the fiber. -/
@[simp]
theorem scalarEndHomeomorph_apply (b : B) (a : κ) :
    scalarEndHomeomorph κ L (b, a) =
      TotalSpace.mk' (κ →L[κ] κ) b
        (@ContinuousLinearMap.toSpanSingleton κ _ (L b →L[κ] L b) (tH b)
          (aH b) (mH b) _
          (@ContinuousLinearMap.continuousSMul κ κ _ _ (RingHom.id κ) (L b) (L b)
            _ _ _ _ _ _ _ _ (hadd b) (hsmul b))
          (ContinuousLinearMap.id κ (L b)) a) := by
  rfl

/-- The inverse total-space homeomorphism reads the scalar of a fiber endomorphism. -/
@[simp]
theorem scalarEndHomeomorph_symm_apply (b : B) (A : L b →L[κ] L b) :
    (@Homeomorph.symm (B × κ)
      (TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)) _ tEnd
      (scalarEndHomeomorph κ L)) (TotalSpace.mk' (κ →L[κ] κ) b A) =
      (b, (@ContinuousLinearEquiv.symm κ κ _ _ (RingHom.id κ) (RingHom.id κ) _ _
        κ _ _ (L b →L[κ] L b) (tH b) (aH b) _ (mH b)
        (@ContinuousLinearMap.scalarEndEquiv κ _ (L b) _ _ _ (hadd b) (hsmul b)
          (t2Space_line κ L b) (invertible_line κ L b)) A)) := by
  rfl

/-- The total-space homeomorphism preserves the projection to the base. -/
@[simp]
theorem scalarEndHomeomorph_proj (p : B × κ) :
    (scalarEndHomeomorph κ L p).proj = p.1 := by
  rfl

/-- The inverse total-space homeomorphism preserves the projection to the base. -/
@[simp]
theorem scalarEndHomeomorph_symm_proj
    (p : TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)) :
    ((@Homeomorph.symm (B × κ)
      (TotalSpace (κ →L[κ] κ) (fun b ↦ L b →L[κ] L b)) _ tEnd
      (scalarEndHomeomorph κ L)) p).1 = p.proj := by
  rfl

end VectorBundle
