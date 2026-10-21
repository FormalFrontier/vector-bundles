/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import VectorBundles.Topology.VectorBundle.Hom
public import VectorBundles.Topology.Bornology.Inducing

/-!
# Comaps of supplied Hermitian metrics

`Bundle.HermitianMetric.comap` pulls a supplied metric back along fiberwise continuous linear
embeddings, without choosing norms or replacing the original source topologies. Mere injectivity
of a continuous linear map is not enough: its pulled-back unit sublevel need not be bounded.

`Bundle.ContinuousHermitianMetric.comap` uses a continuous section of the Hom bundle on the same
base. Both bundles retain their original fiber and total-space topologies and their given
atlases. The Hom topology uses the operator norm on the models; pointwise or strong-operator
continuity is not substituted for this hypothesis in infinite rank.

The form and evaluation laws characterize the constructions. Equality is tested with the
existing `HermitianMetric.ext` and `ContinuousHermitianMetric.ext`. Forgetting base continuity,
identity and contravariant composition preserve the supplied pairings.

## Implementation notes

The original fibers are only topological modules. Their form data use continuous linear
precomposition and composition; normed bilinear composition is relevant only to the model
coefficients in the continuity argument. The fiber-operation proofs supplied to Mathlib's Hom
topology are transported from the given charts and are not extra hypotheses or topology data.

## References

* Mathlib's bounded-convergence precomposition of continuous linear maps.
* Heather Macbeth and Floris van Doorn, Mathlib's `Topology.VectorBundle.Hom`.
* Sébastien Gouëzel, Mathlib's `Topology.VectorBundle.Riemannian`, for the metric-data interface.
-/

@[expose] public section

noncomputable section

open Bundle

namespace Bundle

universe uκ uB uD uE uC uG uF uH

section Fiberwise

variable {κ : Type uκ} [RCLike κ] {B : Type uB}
  {D : B → Type uD} [∀ b, TopologicalSpace (D b)]
  [∀ b, AddCommGroup (D b)] [∀ b, Module κ (D b)]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]

/-- Pull a supplied Hermitian metric back along fiberwise topological linear embeddings.
The source fibers keep their original topologies. No topology on the base is required. -/
def HermitianMetric.comap (g : HermitianMetric κ E) (a : ∀ b, D b →L[κ] E b)
    (ha : ∀ b, Topology.IsEmbedding (a b)) : HermitianMetric κ D where
  inner b := ((a b).precomp κ).comp ((g.inner b).comp (a b))
  symm := by
    intro b v w
    exact g.symm b (a b v) (a b w)
  pos := by
    intro b v hv
    apply g.pos b (a b v)
    intro h
    apply hv
    exact (ha b).injective (h.trans (map_zero (a b)).symm)
  continuousAt := by
    intro b
    exact (g.continuousAt b).comp_of_eq (a b).continuous.continuousAt (map_zero _)
  isVonNBounded := by
    intro b
    exact (g.isVonNBounded b).preimage_of_isInducing (a b).toLinearMap (ha b).isInducing

/-- The curried form of a comap is precomposition in both arguments. -/
@[simp]
theorem HermitianMetric.comap_inner (g : HermitianMetric κ E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b)) (b : B) :
    (g.comap a ha).inner b = ((a b).precomp κ).comp ((g.inner b).comp (a b)) := by
  rfl

/-- The characteristic pairing of the induced metric. -/
theorem HermitianMetric.comap_inner_apply (g : HermitianMetric κ E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (b : B) (v w : D b) :
    (g.comap a ha).inner b v w = g.inner b (a b v) (a b w) := by
  rfl

/-- Comapping along the identity leaves a supplied metric unchanged. -/
@[simp]
theorem HermitianMetric.comap_id (g : HermitianMetric κ E) :
    g.comap (fun b ↦ ContinuousLinearMap.id κ (E b))
      (fun _ ↦ Topology.IsEmbedding.id) = g := by
  apply HermitianMetric.ext
  intro b v w
  rfl

variable {C : B → Type uC} [∀ b, TopologicalSpace (C b)]
  [∀ b, AddCommGroup (C b)] [∀ b, Module κ (C b)]

/-- Comap is contravariantly compatible with fiberwise composition. -/
theorem HermitianMetric.comap_comp (g : HermitianMetric κ E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (c : ∀ b, C b →L[κ] D b) (hc : ∀ b, Topology.IsEmbedding (c b)) :
    (g.comap a ha).comap c hc =
      g.comap (fun b ↦ (a b).comp (c b)) (fun b ↦ (ha b).comp (hc b)) := by
  apply HermitianMetric.ext
  intro b v w
  rfl

end Fiberwise

section Continuous

variable {κ : Type uκ} [RCLike κ] {B : Type uB} [TopologicalSpace B]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
  {D : B → Type uD} [∀ b, TopologicalSpace (D b)]
  [∀ b, AddCommGroup (D b)] [∀ b, Module κ (D b)]
  [TopologicalSpace (TotalSpace G D)] [FiberBundle G D] [VectorBundle κ G D]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]

-- This expands to the original Hom topology, with derived fiber-operation Prop proofs.
local notation "homDE" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B G _ _ D _ _ _ F _ _ E _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ F E b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ F E b)) _

-- Isolate the two nested Hom chart computations from the continuity argument.
private theorem sesquilinear_trivializationAt_apply (b₀ : B) {b : B}
    (hb : b ∈ (trivializationAt G D b₀).baseSet)
    (q : D b →L⋆[κ] D b →L[κ] κ) (v w : G) :
    (trivializationAt (G →L⋆[κ] G →L[κ] κ)
      (fun b ↦ D b →L⋆[κ] D b →L[κ] κ) b₀
      (TotalSpace.mk' (G →L⋆[κ] G →L[κ] κ) b q)).2 v w =
        q ((trivializationAt G D b₀).symmL κ b v)
          ((trivializationAt G D b₀).symmL κ b w) := by
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem κ _
    (show b ∈ (trivializationAt (G →L[κ] κ)
      (fun b ↦ D b →L[κ] κ) b₀).baseSet by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hb, Set.mem_univ b⟩)]
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem κ _ (Set.mem_univ b)]
  rfl

-- These lemmas involve only normed model spaces, not bundle charts or fiber topologies.
-- Linear postcomposition is bilinear on operator spaces even when the inner maps are semilinear.
private theorem continuousAt_postcomp_semilinear
    {𝕜₁ 𝕜₂ V U W : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜₁ V]
    [SeminormedAddCommGroup U] [NormedSpace 𝕜₂ U]
    [SeminormedAddCommGroup W] [NormedSpace 𝕜₂ W]
    {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
    {P : B → U →L[𝕜₂] W} {S : B → V →SL[σ] U} {b₀ : B}
    (hP : ContinuousAt P b₀) (hS : ContinuousAt S b₀) :
    ContinuousAt (fun b ↦ (P b).comp (S b)) b₀ := by
  exact (ContinuousLinearMap.compSL (𝕜 := 𝕜₁) (𝕜₂ := 𝕜₂) (𝕜₃ := 𝕜₂)
    (σ₁₃ := σ) V U W σ (RingHom.id 𝕜₂)).continuous₂.continuousAt.comp (hP.prodMk hS)

private theorem continuousAt_comap_model_precomp {A : B → G →L[κ] F}
    {Q : B → F →L⋆[κ] F →L[κ] κ} {b₀ : B}
    (hA : ContinuousAt A b₀) (hQ : ContinuousAt Q b₀) :
    ContinuousAt (fun b ↦ (Q b).comp (A b)) b₀ := by
  exact ((ContinuousLinearMap.compSL (𝕜 := κ) (𝕜₂ := κ) (𝕜₃ := κ)
    (σ₁₃ := starRingEnd κ) G F (F →L[κ] κ)
    (RingHom.id κ) (starRingEnd κ)).flip.continuous.continuousAt.comp hA).clm_apply hQ

private theorem continuousAt_comap_model {A : B → G →L[κ] F}
    {Q : B → F →L⋆[κ] F →L[κ] κ} {b₀ : B}
    (hA : ContinuousAt A b₀) (hQ : ContinuousAt Q b₀) :
    ContinuousAt (fun b ↦
      ((ContinuousLinearMap.compL κ G F κ).flip (A b)).comp
        ((Q b).comp (A b))) b₀ := by
  have hP : ContinuousAt (fun b ↦
      (ContinuousLinearMap.compL κ G F κ).flip (A b)) b₀ :=
    (ContinuousLinearMap.compL κ G F κ).flip.continuous.continuousAt.comp hA
  exact continuousAt_postcomp_semilinear hP (continuousAt_comap_model_precomp hA hQ)

-- Prove section continuity directly for the curried form, independently of the metric
-- constructor and its positivity/boundedness proofs.
private theorem continuous_comap_inner (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b)
    (hcont : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b))) :
    Continuous (fun b ↦ TotalSpace.mk' (G →L⋆[κ] G →L[κ] κ) b
      (((a b).precomp κ).comp ((g.inner b).comp (a b)))) := by
  let : ∀ b, IsTopologicalAddGroup (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).toContinuousAddEquiv.isTopologicalAddGroup
  let : ∀ b, ContinuousSMul κ (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).continuousSMul
  refine continuous_iff_continuousAt.mpr fun b₀ ↦ ?_
  refine (FiberBundle.continuousAt_section (G →L⋆[κ] G →L[κ] κ)
    (E := fun b ↦ D b →L⋆[κ] D b →L[κ] κ)
    (s := fun b ↦ ((a b).precomp κ).comp ((g.inner b).comp (a b))) b₀).mpr ?_
  let A : B → G →L[κ] F := fun b ↦
    (trivializationAt (G →L[κ] F) (fun b ↦ D b →L[κ] E b) b₀
      (TotalSpace.mk' (G →L[κ] F) b (a b))).2
  let Q : B → F →L⋆[κ] F →L[κ] κ := fun b ↦
    (trivializationAt (F →L⋆[κ] F →L[κ] κ)
      (fun b ↦ E b →L⋆[κ] E b →L[κ] κ) b₀
      (TotalSpace.mk' (F →L⋆[κ] F →L[κ] κ) b (g.inner b))).2
  have hA : ContinuousAt A b₀ :=
    (FiberBundle.continuousAt_section (G →L[κ] F)
      (E := fun b ↦ D b →L[κ] E b) (s := a) b₀).mp hcont.continuousAt
  have hQ : ContinuousAt Q b₀ :=
    (FiberBundle.continuousAt_section (F →L⋆[κ] F →L[κ] κ)
      (E := fun b ↦ E b →L⋆[κ] E b →L[κ] κ) (s := g.inner) b₀).mp
        g.continuous.continuousAt
  apply (continuousAt_comap_model hA hQ).congr_of_eventuallyEq
  filter_upwards [(trivializationAt G D b₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G D b₀),
    (trivializationAt F E b₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E b₀)] with b hbD hbE
  have hA_apply (v : G) : A b v =
      (trivializationAt F E b₀).continuousLinearMapAt κ b
        (a b ((trivializationAt G D b₀).symmL κ b v)) := by
    dsimp only [A]
    rw [hom_trivializationAt_apply]
    rfl
  have hQ_apply (v w : F) : Q b v w =
      g.inner b ((trivializationAt F E b₀).symmL κ b v)
        ((trivializationAt F E b₀).symmL κ b w) :=
    sesquilinear_trivializationAt_apply b₀ hbE (g.inner b) v w
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  rw [sesquilinear_trivializationAt_apply b₀ hbD]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [hQ_apply, hA_apply, hA_apply,
    Trivialization.symmL_continuousLinearMapAt _ hbE,
    Trivialization.symmL_continuousLinearMapAt _ hbE]

-- Lift the public pointwise forgetful law to an equality of curried forms.
private theorem toHermitianMetric_inner_eq (g : ContinuousHermitianMetric κ F E) (b : B) :
    g.toHermitianMetric.inner b = g.inner b :=
  ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦
    g.toHermitianMetric_inner b v w

/-- Pull a supplied continuous Hermitian metric back along a continuous section of the
Hom bundle whose fiber maps are topological embeddings. Only the models are normed. -/
def ContinuousHermitianMetric.comap (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (hcont : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b))) :
    ContinuousHermitianMetric κ G D where
  inner := (g.toHermitianMetric.comap a ha).inner
  symm := by
    exact (g.toHermitianMetric.comap a ha).symm
  pos := by
    exact (g.toHermitianMetric.comap a ha).pos
  isVonNBounded := by
    exact (g.toHermitianMetric.comap a ha).isVonNBounded
  continuous := by
    simpa only [HermitianMetric.comap_inner, toHermitianMetric_inner_eq] using
      continuous_comap_inner g a hcont

/-- The curried form of the continuous comap is precomposition in both arguments. -/
@[simp]
theorem ContinuousHermitianMetric.comap_inner (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (hcont : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b))) (b : B) :
    (g.comap a ha hcont).inner b =
      ((a b).precomp κ).comp ((g.inner b).comp (a b)) := by
  change (g.toHermitianMetric.comap a ha).inner b = _
  rw [HermitianMetric.comap_inner, toHermitianMetric_inner_eq]

/-- The characteristic pairing of the continuous induced metric. -/
theorem ContinuousHermitianMetric.comap_inner_apply (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (hcont : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b))) (b : B) (v w : D b) :
    (g.comap a ha hcont).inner b v w = g.inner b (a b v) (a b w) := by
  simp only [ContinuousHermitianMetric.comap_inner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]

/-- Forgetting continuity commutes with comap, preserving the original fiber metric data. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_comap
    (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (hcont : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b))) :
    (g.comap a ha hcont).toHermitianMetric = g.toHermitianMetric.comap a ha := by
  apply HermitianMetric.ext
  intro b v w
  rw [ContinuousHermitianMetric.toHermitianMetric_inner,
    ContinuousHermitianMetric.comap_inner_apply, HermitianMetric.comap_inner_apply,
    ContinuousHermitianMetric.toHermitianMetric_inner]

/-- Comapping a continuous metric along the identity leaves it unchanged. -/
@[simp]
theorem ContinuousHermitianMetric.comap_id (g : ContinuousHermitianMetric κ F E) :
    g.comap (G := F) (fun b ↦ ContinuousLinearMap.id κ (E b))
      (fun _ ↦ Topology.IsEmbedding.id)
      (Bundle.continuous_id_hom_section (κ := κ) (F := F) (E := E)) = g := by
  refine ContinuousHermitianMetric.ext (𝕜 := κ) (B := B) (F := F) (E := E) ?_
  intro b v w
  calc
    (g.comap (G := F) (fun b ↦ ContinuousLinearMap.id κ (E b))
        (fun _ ↦ Topology.IsEmbedding.id)
        (Bundle.continuous_id_hom_section (κ := κ) (F := F) (E := E))).inner b v w =
        g.inner b ((ContinuousLinearMap.id κ (E b)) v)
          ((ContinuousLinearMap.id κ (E b)) w) :=
      ContinuousHermitianMetric.comap_inner_apply (κ := κ) (B := B)
        (G := F) (D := E) (F := F) (E := E) g
        (fun b ↦ ContinuousLinearMap.id κ (E b)) (fun _ ↦ Topology.IsEmbedding.id)
        (Bundle.continuous_id_hom_section (κ := κ) (F := F) (E := E)) b v w
    _ = g.inner b v w := rfl

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace κ H]
  {C : B → Type uC} [∀ b, TopologicalSpace (C b)]
  [∀ b, AddCommGroup (C b)] [∀ b, Module κ (C b)]
  [TopologicalSpace (TotalSpace H C)] [FiberBundle H C] [VectorBundle κ H C]

local notation "homCD" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B H _ _ C _ _ _ G _ _ D _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ G D b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ G D b)) _

/-- Continuous comap is contravariantly compatible with composition. The composite section's
continuity follows from the two input sections, rather than being an additional assumption. -/
theorem ContinuousHermitianMetric.comap_comp (g : ContinuousHermitianMetric κ F E)
    (a : ∀ b, D b →L[κ] E b) (ha : ∀ b, Topology.IsEmbedding (a b))
    (hconta : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b)))
    (c : ∀ b, C b →L[κ] D b) (hc : ∀ b, Topology.IsEmbedding (c b))
    (hcontc : @Continuous _ _ _ homCD
      (fun b ↦ TotalSpace.mk' (H →L[κ] G) b (c b))) :
    (g.comap a ha hconta).comap c hc hcontc =
      g.comap (G := H) (fun b ↦ (a b).comp (c b))
        (fun b ↦ (ha b).comp (hc b)) (hconta.clm_bundle_comp hcontc) := by
  refine ContinuousHermitianMetric.ext (𝕜 := κ) (B := B) (F := H) (E := C) ?_
  intro b v w
  calc
    ((g.comap (G := G) a ha hconta).comap (G := H) c hc hcontc).inner b v w =
        (g.comap (G := G) a ha hconta).inner b (c b v) (c b w) :=
      ContinuousHermitianMetric.comap_inner_apply (κ := κ) (B := B)
        (G := H) (D := C) (F := G) (E := D)
        (g.comap (G := G) a ha hconta) c hc hcontc b v w
    _ = g.inner b (a b (c b v)) (a b (c b w)) :=
      ContinuousHermitianMetric.comap_inner_apply (κ := κ) (B := B)
        (G := G) (D := D) (F := F) (E := E) g a ha hconta b (c b v) (c b w)
    _ = (g.comap (G := H) (fun b ↦ (a b).comp (c b))
        (fun b ↦ (ha b).comp (hc b)) (hconta.clm_bundle_comp hcontc)).inner b v w :=
      (ContinuousHermitianMetric.comap_inner_apply (κ := κ) (B := B)
        (G := H) (D := C) (F := F) (E := E) g (fun b ↦ (a b).comp (c b))
        (fun b ↦ (ha b).comp (hc b)) (hconta.clm_bundle_comp hcontc) b v w).symm

end Continuous

end Bundle
