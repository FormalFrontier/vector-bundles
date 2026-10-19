/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalProjection

/-!
# Comparing orthogonal complements for two Hermitian metrics

Two supplied continuous Hermitian metrics on the same ambient vector bundle give
orthogonal complements of one intrinsic submodule bundle. Their fibers are
canonically linearly equivalent: both are representatives of the quotient by the
same submodule. The comparison sends a vector in the first complement to its
projection onto the second complement along the submodule.

For an embedded intrinsic submodule bundle, this comparison is a homeomorphism
between the two complement total spaces with their original ambient-induced
topologies. Its forward function is ambient inclusion followed by the second
metric's complement projection; its inverse uses the first metric's projection.
The original ambient and intrinsic bundle topologies are retained. Only the
ambient model is assumed finite-dimensional; no nonempty-base or global
finite-dimensionality assumption on the intrinsic model is needed.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.3: orthogonal complements of subbundles for a supplied metric.
* Mathlib's complementary-submodule quotient equivalences and projections,
  by Yury Kudryashov, and its Hermitian and vector-bundle constructions.
-/

@[expose] public section

open Bundle

namespace Bundle.ContinuousHermitianMetric

universe u𝕜 uB uF uG uE

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g₁ g₂ g₃ : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [FiniteDimensional 𝕜 F]

local notation "C₁" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g₁ b)) (S b))
local notation "C₂" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g₂ b)) (S b))
local notation "C₃" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g₃ b)) (S b))

/-- The canonical linear equivalence between the orthogonal complements of one
submodule for two supplied metrics. It is obtained by identifying both complements
with the same quotient of the original ambient fiber by that submodule. -/
noncomputable def orthogonalComplementEquiv (b : B) : C₁ b ≃ₗ[𝕜] C₂ b :=
  ((S b).quotientEquivOfIsCompl (C₁ b) (g₁.orthogonal_isCompl S b)).symm.trans
    ((S b).quotientEquivOfIsCompl (C₂ b) (g₂.orthogonal_isCompl S b))

/-- The fiber comparison is the second metric's complement projection after
inclusion in the original ambient fiber. -/
theorem orthogonalComplementEquiv_apply (b : B) (c : C₁ b) :
    g₁.orthogonalComplementEquiv g₂ S b c =
      (C₂ b).projectionOnto (S b) (g₂.orthogonal_isCompl S b).symm (c : E b) := by
  simp only [orthogonalComplementEquiv, LinearEquiv.trans_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk]

/-- The inverse fiber comparison is the first metric's complement projection
after inclusion in the original ambient fiber. -/
theorem orthogonalComplementEquiv_symm_apply (b : B) (c : C₂ b) :
    (g₁.orthogonalComplementEquiv g₂ S b).symm c =
      (C₁ b).projectionOnto (S b) (g₁.orthogonal_isCompl S b).symm (c : E b) := by
  simp only [orthogonalComplementEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, Submodule.quotientEquivOfIsCompl_symm_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk]

/-- A vector and its comparison have the same class modulo the intrinsic
submodule of the original ambient fiber. -/
theorem orthogonalComplementEquiv_sub_mem (b : B) (c : C₁ b) :
    (c : E b) - (g₁.orthogonalComplementEquiv g₂ S b c : E b) ∈ S b := by
  apply (Submodule.Quotient.eq (S b)).mp
  simp only [orthogonalComplementEquiv, LinearEquiv.trans_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply,
    Submodule.mk_quotientEquivOfIsCompl_apply]

/-- The comparison is the unique vector in the second complement whose difference
from the original vector lies in the intrinsic submodule. -/
theorem orthogonalComplementEquiv_eq_iff_sub_mem (b : B) (c : C₁ b) (d : C₂ b) :
    g₁.orthogonalComplementEquiv g₂ S b c = d ↔
      (c : E b) - (d : E b) ∈ S b := by
  rw [orthogonalComplementEquiv, LinearEquiv.trans_apply,
    ← LinearEquiv.eq_symm_apply]
  simp only [Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.Quotient.eq]

/-- Comparing an orthogonal complement with itself gives the identity linear
equivalence. -/
@[simp]
theorem orthogonalComplementEquiv_refl (b : B) :
    g₁.orthogonalComplementEquiv g₁ S b = LinearEquiv.refl 𝕜 (C₁ b) := by
  simp only [orthogonalComplementEquiv, LinearEquiv.symm_trans_self]

/-- Changing the metric twice gives the direct comparison of orthogonal
complements of the same intrinsic submodule. -/
theorem orthogonalComplementEquiv_trans (b : B) :
    (g₁.orthogonalComplementEquiv g₂ S b).trans
        (g₂.orthogonalComplementEquiv g₃ S b) =
      g₁.orthogonalComplementEquiv g₃ S b := by
  ext c
  simp only [orthogonalComplementEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

section TotalSpace

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
  (hS : Topology.IsEmbedding
    (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))

local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))
local notation "tC₁" => TopologicalSpace.induced
  (fun p : TotalSpace H C₁ ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance
local notation "tC₂" => TopologicalSpace.induced
  (fun p : TotalSpace H C₂ ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance
local notation "tC₃" => TopologicalSpace.induced
  (fun p : TotalSpace H C₃ ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance

/-- The canonical comparison between the orthogonal complements of one embedded
intrinsic submodule bundle for two supplied metrics on the original ambient bundle.
Both total spaces have the topology induced by their original ambient inclusions.
The forward function uses the second metric's complement projection, and the inverse
uses the first metric's complement projection. -/
noncomputable def orthogonalComplementHomeomorph :
    @Homeomorph (TotalSpace H C₁) (TotalSpace H C₂) tC₁ tC₂ := by
  letI : TopologicalSpace (TotalSpace H C₁) := tC₁
  letI : TopologicalSpace (TotalSpace H C₂) := tC₂
  have hj₁ : Topology.IsInducing (fun p : TotalSpace H C₁ ↦
      TotalSpace.mk' F p.proj (p.2 : E p.proj)) := ⟨rfl⟩
  have hj₂ : Topology.IsInducing (fun p : TotalSpace H C₂ ↦
      TotalSpace.mk' F p.proj (p.2 : E p.proj)) := ⟨rfl⟩
  exact
    { toFun := (g₂.orthogonalComplementProjectionTotal S hS) ∘
        (fun p : TotalSpace H C₁ ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj))
      invFun := (g₁.orthogonalComplementProjectionTotal S hS) ∘
        (fun p : TotalSpace H C₂ ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj))
      left_inv := by
        rintro ⟨b, c⟩
        let e : C₁ b ≃ₗ[𝕜] C₂ b := g₁.orthogonalComplementEquiv g₂ S b
        have hforward :
            g₂.orthogonalComplementProjectionTotal (G := G) S hS
                (TotalSpace.mk' F (E := E) b (c : E b)) =
              TotalSpace.mk' H (E := C₂) b (e c) :=
          (g₂.orthogonalComplementProjectionTotal_apply (G := G) S hS b (c : E b)).trans
            (congrArg (TotalSpace.mk' H (E := C₂) b)
              (g₁.orthogonalComplementEquiv_apply g₂ S b c).symm)
        have hreverse :
            g₁.orthogonalComplementProjectionTotal (G := G) S hS
                (TotalSpace.mk' F (E := E) b (e c : E b)) =
              TotalSpace.mk' H (E := C₁) b c :=
          (g₁.orthogonalComplementProjectionTotal_apply (G := G) S hS b (e c : E b)).trans
            (congrArg (TotalSpace.mk' H (E := C₁) b)
              ((g₁.orthogonalComplementEquiv_symm_apply g₂ S b (e c)).symm.trans
                (e.symm_apply_apply c)))
        exact (congrArg
          (fun p : TotalSpace H C₂ ↦
            g₁.orthogonalComplementProjectionTotal (G := G) S hS
              (TotalSpace.mk' F (E := E) p.proj (p.2 : E p.proj)))
          hforward).trans hreverse
      right_inv := by
        rintro ⟨b, c⟩
        let e : C₁ b ≃ₗ[𝕜] C₂ b := g₁.orthogonalComplementEquiv g₂ S b
        have hreverse :
            g₁.orthogonalComplementProjectionTotal (G := G) S hS
                (TotalSpace.mk' F (E := E) b (c : E b)) =
              TotalSpace.mk' H (E := C₁) b (e.symm c) :=
          (g₁.orthogonalComplementProjectionTotal_apply (G := G) S hS b (c : E b)).trans
            (congrArg (TotalSpace.mk' H (E := C₁) b)
              (g₁.orthogonalComplementEquiv_symm_apply g₂ S b c).symm)
        have hforward :
            g₂.orthogonalComplementProjectionTotal (G := G) S hS
                (TotalSpace.mk' F (E := E) b (e.symm c : E b)) =
              TotalSpace.mk' H (E := C₂) b c :=
          (g₂.orthogonalComplementProjectionTotal_apply (G := G) S hS b (e.symm c : E b)).trans
            (congrArg (TotalSpace.mk' H (E := C₂) b)
              ((g₁.orthogonalComplementEquiv_apply g₂ S b (e.symm c)).symm.trans
                (e.apply_symm_apply c)))
        exact (congrArg
          (fun p : TotalSpace H C₁ ↦
            g₂.orthogonalComplementProjectionTotal (G := G) S hS
              (TotalSpace.mk' F (E := E) p.proj (p.2 : E p.proj)))
          hreverse).trans hforward
      continuous_toFun :=
        (g₂.orthogonalComplementProjectionTotal S hS).continuous.comp hj₁.continuous
      continuous_invFun :=
        (g₁.orthogonalComplementProjectionTotal S hS).continuous.comp hj₂.continuous }

/-- The total comparison is the second metric's complement projection
following the original ambient inclusion of the first complement. -/
@[simp]
theorem orthogonalComplementHomeomorph_apply (p : TotalSpace H C₁) :
    g₁.orthogonalComplementHomeomorph g₂ S hS p =
      g₂.orthogonalComplementProjectionTotal S hS
        (TotalSpace.mk' F p.proj (p.2 : E p.proj)) := rfl

/-- The inverse total comparison is the first metric's complement projection
following the original ambient inclusion of the second complement. -/
@[simp]
theorem orthogonalComplementHomeomorph_symm_apply (p : TotalSpace H C₂) :
    @Homeomorph.symm (TotalSpace H C₁) (TotalSpace H C₂) tC₁ tC₂
        (g₁.orthogonalComplementHomeomorph g₂ S hS) p =
      g₁.orthogonalComplementProjectionTotal S hS
        (TotalSpace.mk' F p.proj (p.2 : E p.proj)) := rfl

/-- The total comparison preserves the base point. -/
@[simp]
theorem orthogonalComplementHomeomorph_proj (p : TotalSpace H C₁) :
    (g₁.orthogonalComplementHomeomorph g₂ S hS p).proj = p.proj := by
  rw [orthogonalComplementHomeomorph_apply]
  exact g₂.orthogonalComplementProjectionTotal_proj S hS
    (TotalSpace.mk' F p.proj (p.2 : E p.proj))

/-- The inverse total comparison preserves the base point. -/
@[simp]
theorem orthogonalComplementHomeomorph_symm_proj (p : TotalSpace H C₂) :
    (@Homeomorph.symm (TotalSpace H C₁) (TotalSpace H C₂) tC₁ tC₂
      (g₁.orthogonalComplementHomeomorph g₂ S hS) p).proj = p.proj := by
  rw [orthogonalComplementHomeomorph_symm_apply]
  exact g₁.orthogonalComplementProjectionTotal_proj S hS
    (TotalSpace.mk' F p.proj (p.2 : E p.proj))

/-- The total comparison restricts to the quotient-derived linear equivalence
on each original fiber. -/
theorem orthogonalComplementHomeomorph_apply_mk (b : B) (c : C₁ b) :
    g₁.orthogonalComplementHomeomorph g₂ S hS (TotalSpace.mk' H b c) =
      TotalSpace.mk' H b (g₁.orthogonalComplementEquiv g₂ S b c) := by
  rw [orthogonalComplementHomeomorph_apply,
    g₂.orthogonalComplementProjectionTotal_apply S hS,
    ← g₁.orthogonalComplementEquiv_apply g₂ S b c]

/-- The inverse total comparison restricts to the inverse quotient-derived linear
equivalence on each original fiber. -/
theorem orthogonalComplementHomeomorph_symm_apply_mk (b : B) (c : C₂ b) :
    @Homeomorph.symm (TotalSpace H C₁) (TotalSpace H C₂) tC₁ tC₂
        (g₁.orthogonalComplementHomeomorph g₂ S hS) (TotalSpace.mk' H (E := C₂) b c) =
      TotalSpace.mk' H (E := C₁) b ((g₁.orthogonalComplementEquiv g₂ S b).symm c) := by
  rw [orthogonalComplementHomeomorph_symm_apply,
    g₁.orthogonalComplementProjectionTotal_apply S hS,
    ← g₁.orthogonalComplementEquiv_symm_apply g₂ S b c]

/-- Comparing an orthogonal total space with itself gives its identity
homeomorphism for the original ambient-induced topology. -/
@[simp]
theorem orthogonalComplementHomeomorph_refl :
    g₁.orthogonalComplementHomeomorph g₁ S hS =
      @Homeomorph.refl (TotalSpace H C₁) tC₁ := by
  apply @Homeomorph.ext _ _ tC₁ tC₁
  rintro ⟨b, c⟩
  change g₁.orthogonalComplementHomeomorph g₁ S hS (TotalSpace.mk' H b c) =
    TotalSpace.mk' H b c
  simp only [orthogonalComplementHomeomorph_apply_mk,
    orthogonalComplementEquiv_refl, LinearEquiv.refl_apply]

/-- Changing the metric twice gives the direct total-space comparison for the
same original ambient bundle and embedded intrinsic submodule bundle. -/
theorem orthogonalComplementHomeomorph_trans :
    @Homeomorph.trans (TotalSpace H C₁) (TotalSpace H C₂) (TotalSpace H C₃) tC₁ tC₂ tC₃
        (g₁.orthogonalComplementHomeomorph g₂ S hS)
        (g₂.orthogonalComplementHomeomorph g₃ S hS) =
      g₁.orthogonalComplementHomeomorph g₃ S hS := by
  apply @Homeomorph.ext _ _ tC₁ tC₃
  rintro ⟨b, c⟩
  have h₁₂ :
      g₁.orthogonalComplementHomeomorph (G := G) g₂ S hS
          (TotalSpace.mk' H (E := C₁) b c) =
        TotalSpace.mk' H (E := C₂) b (g₁.orthogonalComplementEquiv g₂ S b c) :=
    g₁.orthogonalComplementHomeomorph_apply_mk (G := G) g₂ S hS b c
  have h₂₃ := g₂.orthogonalComplementHomeomorph_apply_mk (G := G) g₃ S hS b
    (g₁.orthogonalComplementEquiv g₂ S b c)
  have hlinear :
      g₂.orthogonalComplementEquiv g₃ S b (g₁.orthogonalComplementEquiv g₂ S b c) =
        g₁.orthogonalComplementEquiv g₃ S b c :=
    congrArg (fun e : C₁ b ≃ₗ[𝕜] C₃ b ↦ e c)
      (g₁.orthogonalComplementEquiv_trans g₂ g₃ S b)
  exact (congrArg
    (fun p : TotalSpace H C₂ ↦ g₂.orthogonalComplementHomeomorph (G := G) g₃ S hS p)
    h₁₂).trans (h₂₃.trans
      ((congrArg (TotalSpace.mk' H (E := C₃) b) hlinear).trans
        (g₁.orthogonalComplementHomeomorph_apply_mk (G := G) g₃ S hS b c).symm))

end TotalSpace

end Bundle.ContinuousHermitianMetric
