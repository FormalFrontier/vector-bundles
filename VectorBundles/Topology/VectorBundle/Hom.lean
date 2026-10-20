/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Identity and composition of sections of the Hom bundle

Identity operators and compositions of continuous sections are continuous in Mathlib's
Hom-bundle topology. Only the models are normed. The fiber and total-space topologies and
the chosen vector-bundle atlases are unchanged.

The topology expressions below supply the fiber-operation laws transported along the preferred
continuous linear charts. These are proofs of properties of the original topologies, not
additional hypotheses or choices of topology. On model operators, the topology is the
operator-norm topology, not a topology of pointwise convergence.

## References

* Heather Macbeth and Floris van Doorn, Mathlib's `Topology.VectorBundle.Hom`.
* Mathlib's continuous linear composition operators on normed spaces.
-/

@[expose] public section

noncomputable section

open Bundle

universe uκ uB uF uG uH uE uD uC

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {E : B → Type uE} [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle κ F E]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
  {D : B → Type uD} [∀ b, AddCommGroup (D b)] [∀ b, Module κ (D b)]
  [TopologicalSpace (TotalSpace G D)] [∀ b, TopologicalSpace (D b)]
  [FiberBundle G D] [VectorBundle κ G D]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace κ H]
  {C : B → Type uC} [∀ b, AddCommGroup (C b)] [∀ b, Module κ (C b)]
  [TopologicalSpace (TotalSpace H C)] [∀ b, TopologicalSpace (C b)]
  [FiberBundle H C] [VectorBundle κ H C]

-- Each notation expands to Mathlib's topology with only derived Prop arguments supplied.
local notation "homEE" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B F _ _ E _ _ _ F _ _ E _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ F E b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ F E b)) _

local notation "homDE" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B G _ _ D _ _ _ F _ _ E _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ F E b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ F E b)) _

local notation "homCD" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B H _ _ C _ _ _ G _ _ D _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ G D b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ G D b)) _

local notation "homCE" =>
  @Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    κ _ κ _ (RingHom.id κ) B H _ _ C _ _ _ F _ _ E _ _ _
    _ _ _ _ _ _ _
    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
      (ContinuousLinearEquiv.toContinuousAddEquiv (VectorBundle.continuousLinearEquivAt κ F E b)))
    (fun b ↦ ContinuousLinearEquiv.continuousSMul
      (VectorBundle.continuousLinearEquivAt κ F E b)) _

/-- Identity maps on the fibers form a continuous section of the Hom bundle. -/
theorem Bundle.continuous_id_hom_section :
    @Continuous _ _ _ homEE
      (fun b : B ↦ TotalSpace.mk' (F →L[κ] F)
        (E := fun b ↦ E b →L[κ] E b) b (ContinuousLinearMap.id κ (E b))) := by
  letI : ∀ b, IsTopologicalAddGroup (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).toContinuousAddEquiv.isTopologicalAddGroup
  letI : ∀ b, ContinuousSMul κ (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).continuousSMul
  apply continuous_iff_continuousAt.2
  intro b₀
  refine (continuousAt_hom_bundle (σ := RingHom.id κ)
    (F₁ := F) (E₁ := E) (F₂ := F) (E₂ := E) _).2 ⟨continuousAt_id, ?_⟩
  have he : ∀ᶠ b in nhds b₀, b ∈ (trivializationAt F E b₀).baseSet :=
    (trivializationAt F E b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b₀)
  have hid : ContinuousAt (fun _ : B ↦ ContinuousLinearMap.id κ F) b₀ := continuousAt_const
  apply hid.congr
  filter_upwards [he] with b hb
  symm
  rw [ContinuousLinearMap.inCoordinates_eq hb hb]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- The fiberwise composition of two continuous Hom-bundle sections is continuous.
No finite-dimensionality or continuity of just the pointwise evaluations is assumed. -/
theorem Continuous.clm_bundle_comp
    {a : ∀ b, D b →L[κ] E b} {c : ∀ b, C b →L[κ] D b}
    (ha : @Continuous _ _ _ homDE
      (fun b ↦ TotalSpace.mk' (G →L[κ] F) b (a b)))
    (hc : @Continuous _ _ _ homCD
      (fun b ↦ TotalSpace.mk' (H →L[κ] G) b (c b))) :
    @Continuous _ _ _ homCE
      (fun b ↦ TotalSpace.mk' (H →L[κ] F) b ((a b).comp (c b))) := by
  letI : ∀ b, IsTopologicalAddGroup (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).toContinuousAddEquiv.isTopologicalAddGroup
  letI : ∀ b, ContinuousSMul κ (E b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ F E b).continuousSMul
  letI : ∀ b, IsTopologicalAddGroup (D b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ G D b).toContinuousAddEquiv.isTopologicalAddGroup
  letI : ∀ b, ContinuousSMul κ (D b) := fun b ↦
    (VectorBundle.continuousLinearEquivAt κ G D b).continuousSMul
  apply continuous_iff_continuousAt.2
  intro b₀
  have ha' : ContinuousAt
      (fun b ↦ ContinuousLinearMap.inCoordinates G D F E b₀ b b₀ b (a b)) b₀ :=
    ((continuousAt_hom_bundle (σ := RingHom.id κ)
      (F₁ := G) (E₁ := D) (F₂ := F) (E₂ := E) _).1 ha.continuousAt).2
  have hc' : ContinuousAt
      (fun b ↦ ContinuousLinearMap.inCoordinates H C G D b₀ b b₀ b (c b)) b₀ :=
    ((continuousAt_hom_bundle (σ := RingHom.id κ)
      (F₁ := H) (E₁ := C) (F₂ := G) (E₂ := D) _).1 hc.continuousAt).2
  refine (continuousAt_hom_bundle (σ := RingHom.id κ)
    (F₁ := H) (E₁ := C) (F₂ := F) (E₂ := E) _).2 ⟨continuousAt_id, ?_⟩
  have he : ∀ᶠ b in nhds b₀, b ∈ (trivializationAt F E b₀).baseSet :=
    (trivializationAt F E b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b₀)
  have hd : ∀ᶠ b in nhds b₀, b ∈ (trivializationAt G D b₀).baseSet :=
    (trivializationAt G D b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G D b₀)
  have hC : ∀ᶠ b in nhds b₀, b ∈ (trivializationAt H C b₀).baseSet :=
    (trivializationAt H C b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt H C b₀)
  apply (ha'.clm_comp hc').congr
  filter_upwards [he, hd, hC] with b hbE hbD hbC
  rw [ContinuousLinearMap.inCoordinates_eq hbD hbE,
    ContinuousLinearMap.inCoordinates_eq hbC hbD,
    ContinuousLinearMap.inCoordinates_eq hbC hbE]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
