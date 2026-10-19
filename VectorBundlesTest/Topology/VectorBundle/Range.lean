/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.VectorBundle.Range

/-!
# A proper coordinate-axis range bundle

The trivial real line bundle over the noncompact real line maps into the horizontal axis
of `ℝ × ℝ`. Its total embedding is proved using the trivial-bundle product
homeomorphism, independently of the range-bundle construction. The resulting coupled
bundle data are installed in a proof, and the homeomorphism and fiber linearity APIs
are used on this proper, positive-rank image.
-/

-- This leaf contains only named private client checks, not a public library API.
set_option linter.privateModule false

open Bundle

private def axisMap (_b : ℝ) : Bundle.Trivial ℝ ℝ _b →ₗ[ℝ] ℝ × ℝ :=
  LinearMap.inl ℝ ℝ ℝ

private theorem axis_total_isEmbedding :
    Topology.IsEmbedding (fun p : TotalSpace ℝ (Bundle.Trivial ℝ ℝ) ↦
      (p.proj, axisMap p.proj p.2)) := by
  change Topology.IsEmbedding
    ((Prod.map id (fun v : ℝ ↦ (v, 0))) ∘ (Bundle.Trivial.homeomorphProd ℝ ℝ))
  exact (Topology.IsEmbedding.id.prodMap (isEmbedding_prodMkLeft (0 : ℝ))).comp
    (Bundle.Trivial.homeomorphProd ℝ ℝ).isEmbedding

private abbrev axisTopology :
    TopologicalSpace (TotalSpace ℝ (fun b ↦ (axisMap b).range)) :=
  VectorBundle.rangeTotalSpaceTopology (F := ℝ) axisMap

private noncomputable def axisBundle :
    Σ' fb : @FiberBundle ℝ ℝ _ _ (fun b ↦ (axisMap b).range) axisTopology _,
      @VectorBundle ℝ ℝ ℝ (fun b ↦ (axisMap b).range) _ _ _ _ _ _ axisTopology _ fb :=
  VectorBundle.rangeBundle axisMap axis_total_isEmbedding

private theorem axis_zeroSection_continuous :
    @Continuous ℝ (TotalSpace ℝ (fun b ↦ (axisMap b).range)) inferInstance axisTopology
      (Bundle.zeroSection ℝ (fun b ↦ (axisMap b).range)) := by
  let : TopologicalSpace (TotalSpace ℝ (fun b ↦ (axisMap b).range)) := axisTopology
  let : FiberBundle ℝ (fun b ↦ (axisMap b).range) := axisBundle.1
  let : VectorBundle ℝ ℝ (fun b ↦ (axisMap b).range) := axisBundle.2
  exact Bundle.Trivialization.continuous_zeroSection ℝ

private noncomputable def axisHomeomorph :
    @Homeomorph (TotalSpace ℝ (Bundle.Trivial ℝ ℝ))
      (TotalSpace ℝ (fun b ↦ (axisMap b).range)) inferInstance axisTopology :=
  VectorBundle.imageHomeomorph axisMap axis_total_isEmbedding

private theorem axis_forward (b v : ℝ) :
    axisHomeomorph (TotalSpace.mk' ℝ b v) =
      TotalSpace.mk' ℝ b (⟨(v, 0), ⟨v, rfl⟩⟩ : (axisMap b).range) := by
  exact VectorBundle.imageHomeomorph_apply axisMap axis_total_isEmbedding b v

private theorem axis_inverse (b v : ℝ) :
    (@Homeomorph.symm _ _ inferInstance axisTopology axisHomeomorph)
      (TotalSpace.mk' ℝ b (⟨(v, 0), ⟨v, rfl⟩⟩ : (axisMap b).range)) =
        TotalSpace.mk' ℝ b v := by
  have hv : (⟨(v, 0), ⟨v, rfl⟩⟩ : (axisMap b).range) =
      VectorBundle.rangeLinearEquiv axisMap axis_total_isEmbedding b v := by
    apply Subtype.ext
    exact (VectorBundle.rangeLinearEquiv_apply axisMap axis_total_isEmbedding b v).symm
  rw [hv]
  simpa only [axisHomeomorph, LinearEquiv.symm_apply_apply] using
    VectorBundle.imageHomeomorph_symm_apply axisMap axis_total_isEmbedding b
      (VectorBundle.rangeLinearEquiv axisMap axis_total_isEmbedding b v)

private theorem axis_fiber_linearity (b a v w : ℝ) :
    axisHomeomorph (TotalSpace.mk' ℝ b (a • v + w)) =
      TotalSpace.mk' ℝ b
        (a • VectorBundle.rangeLinearEquiv axisMap axis_total_isEmbedding b v +
          VectorBundle.rangeLinearEquiv axisMap axis_total_isEmbedding b w) := by
  rw [axisHomeomorph, VectorBundle.imageHomeomorph_map_add, map_smul]

private theorem axis_inclusion_isEmbedding :
    @Topology.IsEmbedding (TotalSpace ℝ (fun b ↦ (axisMap b).range)) (ℝ × (ℝ × ℝ))
      axisTopology inferInstance (fun p ↦ (p.proj, (p.2 : ℝ × ℝ))) :=
  VectorBundle.rangeInclusion_isEmbedding axisMap

private theorem axis_fiber_proper (b : ℝ) : (0, 1) ∉ (axisMap b).range := by
  rintro ⟨v, hv⟩
  exact zero_ne_one (congrArg Prod.snd hv)
