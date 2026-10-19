/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalAddition
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Total-space orthogonal projections

The inverse of orthogonal addition, followed by the first or second total-space
projection of the fiberwise product, gives the two orthogonal projections of an
ambient vector bundle with a supplied continuous Hermitian metric. The first target
retains the intrinsic subbundle total topology; the second has the ambient-induced
total topology. The domain retains the original ambient total topology.

## Implementation notes

Only the ambient model is assumed finite-dimensional; the subbundle model is arbitrary,
and the base need not be nonempty, separated or paracompact. Continuity follows from
the inverse addition homeomorphism and the canonical fiberwise-product topology:
its inducing diagonal into the product of total spaces is continuous, as are the
two product projections. The underlying functions are fixed compositions with the
inverse addition homeomorphism. This module does not construct a metric or provide
pointwise linear projectors, isometric charts or a stable-triviality theorem.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.3, p. 12: the geometric orthogonal-splitting construction for a
  given metric. The projection maps here are derived components of that splitting,
  not a separately stated assertion of the proposition; scalars are generalized to `RCLike`.
* Mathlib's fiber-bundle constructions, by Nicolò Cavalleri, Sébastien Gouëzel,
  Heather Macbeth and Floris van Doorn; its continuous-map product projections.
-/

@[expose] public section

open Bundle

namespace Bundle.ContinuousHermitianMetric

universe u𝕜 uB uF uG uE

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
  [FiniteDimensional 𝕜 F]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
  (hS : Topology.IsEmbedding
    (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))

local notation "C" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g b)) (S b))
local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))
local notation "tC" => TopologicalSpace.induced
  (fun p : TotalSpace H C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance
local notation "tProd" => @FiberBundle.Prod.topologicalSpace B G (fun b ↦ S b) H C
  inferInstance tC
local notation "Φ" => @Homeomorph.toEquiv _ _ tProd inferInstance
  (g.orthogonalAdditionHomeomorph S hS)

/-- The continuous total-space projection onto an embedded intrinsic submodule
bundle along its metric orthogonal complement. The target has the given intrinsic
total topology. Its function is the first total projection after inverse addition. -/
noncomputable def orthogonalProjectionTotal :
    C(TotalSpace F E, TotalSpace G (fun b ↦ S b)) where
  toFun := (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
    TotalSpace.mk' G p.proj p.2.1) ∘ (Φ).symm
  continuous_toFun := by
    let : TopologicalSpace (TotalSpace H C) := tC
    exact (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous.fst.comp
      (g.orthogonalAdditionHomeomorph S hS).continuous_invFun

/-- The continuous total-space projection onto the metric orthogonal family of an
embedded intrinsic submodule bundle. The target has the ambient-induced total
topology. Its function is the second total projection after inverse addition. -/
noncomputable def orthogonalComplementProjectionTotal :
    @ContinuousMap (TotalSpace F E) (TotalSpace H C) inferInstance tC := by
  letI : TopologicalSpace (TotalSpace H C) := tC
  exact
    { toFun := (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
        TotalSpace.mk' H p.proj p.2.2) ∘ (Φ).symm
      continuous_toFun := by
        exact (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous.snd.comp
          (g.orthogonalAdditionHomeomorph S hS).continuous_invFun }

private theorem orthogonalAdditionHomeomorph_symm_proj (p : TotalSpace F E) :
    ((Φ).symm p).proj = p.proj := by
  have h := congrArg TotalSpace.proj ((Φ).apply_symm_apply p)
  exact h

/-- Projection onto the intrinsic subbundle preserves the base point. -/
@[simp]
theorem orthogonalProjectionTotal_proj (p : TotalSpace F E) :
    (g.orthogonalProjectionTotal S hS p).proj = p.proj :=
  orthogonalAdditionHomeomorph_symm_proj g S hS p

/-- Projection onto the orthogonal family preserves the base point. -/
@[simp]
theorem orthogonalComplementProjectionTotal_proj (p : TotalSpace F E) :
    (g.orthogonalComplementProjectionTotal S hS p).proj = p.proj :=
  orthogonalAdditionHomeomorph_symm_proj g S hS p

/-- On a sum of orthogonal components, the intrinsic projection returns the first
component, as a point of the intrinsic total space. -/
@[simp]
theorem orthogonalProjectionTotal_apply_add (b : B) (s : S b) (c : C b) :
    g.orthogonalProjectionTotal S hS (TotalSpace.mk' F b ((s : E b) + (c : E b))) =
      TotalSpace.mk' G b s := by
  have h := (Φ).symm_apply_apply ⟨b, s, c⟩
  exact congrArg
    (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' G (E := fun b ↦ S b) p.proj p.2.1) h

/-- On a sum of orthogonal components, the complement projection returns the second
component, as a point of the ambient-induced orthogonal total space. -/
@[simp]
theorem orthogonalComplementProjectionTotal_apply_add (b : B) (s : S b) (c : C b) :
    g.orthogonalComplementProjectionTotal S hS
        (TotalSpace.mk' F b ((s : E b) + (c : E b))) = TotalSpace.mk' H b c := by
  have h := (Φ).symm_apply_apply ⟨b, s, c⟩
  exact congrArg
    (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' H (E := C) p.proj p.2.2) h

/-- The total complement projection agrees on each fiber with the algebraic
projection onto that complement along the intrinsic submodule. -/
theorem orthogonalComplementProjectionTotal_apply (b : B) (v : E b) :
    g.orthogonalComplementProjectionTotal S hS (TotalSpace.mk' F b v) =
      TotalSpace.mk' H b
        ((C b).projectionOnto (S b) (g.orthogonal_isCompl S b).symm v) := by
  let c : C b := (C b).projectionOnto (S b) (g.orthogonal_isCompl S b).symm v
  let s : S b := ⟨v - (c : E b),
    Submodule.sub_projection_mem (g.orthogonal_isCompl S b).symm v⟩
  have hsum : (s : E b) + (c : E b) = v := sub_add_cancel _ _
  simpa only [hsum] using
    g.orthogonalComplementProjectionTotal_apply_add S hS b s c

end Bundle.ContinuousHermitianMetric
