/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Equiv
public import VectorBundles.Analysis.Normed.Operator.LowerBound
public import VectorBundles.Data.Bundle
public import VectorBundles.Topology.MetricSpace.Antilipschitz
public import VectorBundles.Topology.VectorBundle.CoordinateMap
public import Mathlib.Topology.LocalAtTarget

/-!
# Embeddings from fiberwise injective vector-bundle maps

The embedding criterion concerns a continuous, fiberwise linear map between vector bundles
with their given fiber topologies, total-space topologies and atlases. The models are normed
κ-spaces; only the source model is finite dimensional. The linear ranges carry the subtype
topologies from the target fibers. The range hypothesis is `IsModuleTopology` for these
existing topologies, not a choice of new topologies.

Neither the field nor the models need to be complete. No norms on the fibers, finite
dimensionality of the target model, nonempty base, or inverse family are assumed. In
particular, there is no global module-topology hypothesis on the source model: an empty
base cannot supply one through a fiberwise condition.

## Implementation notes

The module topology on the source model is derived only after fixing a base point, from the
original range topology and the source chart. On the overlap of two charts, the coordinate
operators vary continuously in operator norm. A lower bound at each operator persists on a
base neighborhood, giving an embedding of the coordinate products. The original total-space
embedding follows by chart homeomorphisms and the open-cover criterion for embeddings.

## References

The statement uses Mathlib's vector-bundle and module-topology interfaces. The coordinate-map
interface is `Bundle.Trivialization.continuousOn_linearMapAt_comp_of_isModuleTopology`.
-/

public section

open Bundle Filter Set Topology
open scoped NNReal

universe uκ uB uF uG uE uE'

namespace VectorBundle

section PointTopology

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {G : Type uG} [TopologicalSpace G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]
  {E' : B → Type uE'} [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace G E')] [FiberBundle G E']

private noncomputable def continuousLinearEquivRange_of_injective_at
    (φ : ∀ b, E b →ₗ[κ] E' b) (b : B) (hf : Function.Injective (φ b))
    [IsModuleTopology κ (φ b).range]
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) : E b ≃L[κ] (φ b).range := by
  have hφb : Continuous (φ b) := by
    apply (FiberBundle.totalSpaceMk_isInducing G E' b).continuous_iff.mpr
    exact hφ.comp (FiberBundle.continuous_totalSpaceMk F E b)
  let e := LinearEquiv.ofInjective (φ b) hf
  let c := VectorBundle.continuousLinearEquivAt κ F E b
  -- Pass through the model so no continuous-operation instances on the fiber are needed.
  exact
    { e with
      continuous_toFun := hφb.subtype_mk (LinearMap.mem_range_self (φ b))
      continuous_invFun :=
        (c.symm.continuous.comp (IsModuleTopology.continuous_of_linearMap
          (c.toLinearEquiv.toLinearMap.comp e.symm.toLinearMap))).congr
            (fun x ↦ c.symm_apply_apply (e.symm x)) }

private theorem isModuleTopology_model_of_injective_at
    (φ : ∀ b, E b →ₗ[κ] E' b) (b : B) (hf : Function.Injective (φ b))
    [IsModuleTopology κ (φ b).range]
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) : IsModuleTopology κ F :=
  IsModuleTopology.iso
    ((continuousLinearEquivRange_of_injective_at φ b hf hφ).symm.trans
      (VectorBundle.continuousLinearEquivAt κ F E b))

private theorem isEmbedding_fibre_of_injective_at
    (φ : ∀ b, E b →ₗ[κ] E' b) (b : B) (hf : Function.Injective (φ b))
    [IsModuleTopology κ (φ b).range]
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) : Topology.IsEmbedding (φ b) :=
  (Submodule.isEmbedding_subtype (φ b).range).comp
    (continuousLinearEquivRange_of_injective_at φ b hf hφ).toHomeomorph.isEmbedding

end PointTopology

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F] [FiniteDimensional κ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]
  {E' : B → Type uE'} [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace G E')] [FiberBundle G E'] [VectorBundle κ G E']

omit [FiniteDimensional κ F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle κ F E] [∀ b, TopologicalSpace (E' b)] [FiberBundle G E']
  [VectorBundle κ G E'] in
private theorem linearMapAt_comp_eq_chart
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b) (p : TotalSpace F E)
    (hp : p.proj ∈ e.baseSet ∩ e'.baseSet) :
    (p.proj, e'.linearMapAt κ p.proj
      (φ p.proj (e.symmₗ κ p.proj (e p).2))) =
      e' (TotalSpace.map F G id (fun b ↦ φ b) p) := by
  have hs : e.symmₗ κ p.proj (e p).2 = p.2 := by
    rw [← congrFun (e.coe_linearMapAt_of_mem (R := κ) hp.1) p.2]
    exact e.symmₗ_linearMapAt hp.1 p.2
  apply Prod.ext
  · exact (e'.coe_fst' (x := TotalSpace.map F G id (fun b ↦ φ b) p) hp.2).symm
  · rw [hs]
    exact congrFun (e'.coe_linearMapAt_of_mem (R := κ) hp.2) (φ p.proj p.2)

omit [FiniteDimensional κ F] [VectorBundle κ G E'] in
private theorem isEmbedding_linearMapAt_comp
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b) (b : B) (hb : b ∈ e.baseSet ∩ e'.baseSet)
    (hf : Function.Injective (φ b)) [IsModuleTopology κ (φ b).range]
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) :
    Topology.IsEmbedding (fun v : F ↦
      e'.linearMapAt κ b (φ b (e.symmₗ κ b v))) := by
  let c := e.continuousLinearEquivAt κ b hb.1
  let c' := e'.continuousLinearEquivAt κ b hb.2
  have heq : (fun v : F ↦ e'.linearMapAt κ b (φ b (e.symmₗ κ b v))) =
      c' ∘ φ b ∘ c.symm := by
    funext v
    rw [e'.coe_linearMapAt_of_mem (R := κ) hb.2,
      e.symmₗ_apply (R := κ) hb.1 v]
    rfl
  rw [heq]
  exact c'.toHomeomorph.isEmbedding.comp
    ((isEmbedding_fibre_of_injective_at φ b hf hφ).comp c.symm.toHomeomorph.isEmbedding)

omit [FiniteDimensional κ F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle κ F E] [∀ b, TopologicalSpace (E' b)] [FiberBundle G E']
  [VectorBundle κ G E'] in
private theorem isEmbedding_restrictPreimage_of_coordinates
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b) (s : Set B)
    (hs : s ⊆ e.baseSet ∩ e'.baseSet)
    (h : Topology.IsEmbedding (fun p : s × F ↦
      (p.1, e'.linearMapAt κ p.1 (φ p.1 (e.symmₗ κ p.1 p.2))))) :
    Topology.IsEmbedding (((π G E') ⁻¹' s).restrictPreimage
      (TotalSpace.map F G id (fun b ↦ φ b))) := by
  let eF := e.preimageHomeomorph (fun b hb ↦ (hs hb).1)
  let eG := e'.preimageHomeomorph (fun b hb ↦ (hs hb).2)
  let ψ : ((π F E) ⁻¹' s) → ((π G E') ⁻¹' s) :=
    fun q ↦ ⟨TotalSpace.map F G id (fun b ↦ φ b) q.1, q.2⟩
  have hcomm : eG ∘ ψ =
      (fun p : s × F ↦
        (p.1, e'.linearMapAt κ p.1 (φ p.1 (e.symmₗ κ p.1 p.2)))) ∘ eF := by
    funext q
    have hF : eF q = (⟨q.1.proj, q.2⟩, (e q.1).2) :=
      e.preimageHomeomorph_apply (fun b hb ↦ (hs hb).1) q
    have hG : eG (ψ q) = (⟨(ψ q).1.proj, (ψ q).2⟩, (e' (ψ q).1).2) :=
      e'.preimageHomeomorph_apply (fun b hb ↦ (hs hb).2) (ψ q)
    simp only [Function.comp_apply]
    rw [hG, hF]
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.snd
        (linearMapAt_comp_eq_chart e e' φ q.1 (hs q.2))).symm
  change Topology.IsEmbedding ψ
  apply (eG.isEmbedding.of_comp_iff).mp
  rw [hcomm]
  exact h.comp eF.isEmbedding

/-- A continuous fiberwise linear injection with finite-dimensional source model is an embedding
when each range has the module topology inherited from the original target fiber. No completeness
of the scalar field or models, or finite dimensionality of the target model, is required. -/
theorem isEmbedding_of_injective
    (φ : ∀ b, E b →ₗ[κ] E' b) (hf : ∀ b, Function.Injective (φ b))
    [∀ b, IsModuleTopology κ (φ b).range]
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) :
    Topology.IsEmbedding (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E')) := by
  classical
  let Φ := TotalSpace.map F G id (fun b ↦ φ b)
  let e := fun b ↦ trivializationAt F E b
  let e' := fun b ↦ trivializationAt G E' b
  let s := fun b ↦ (e b).baseSet ∩ (e' b).baseSet
  let U : B → TopologicalSpace.Opens (TotalSpace G E') := fun b ↦
    ⟨(π G E') ⁻¹' s b,
      ((e b).open_baseSet.inter (e' b).open_baseSet).preimage
        (FiberBundle.continuous_proj G E')⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets
      (fun b ↦ ((e b).open_baseSet.inter (e' b).open_baseSet).preimage
        (FiberBundle.continuous_proj G E'))
    ext p
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨p.proj, FiberBundle.mem_baseSet_trivializationAt F E p.proj,
      FiberBundle.mem_baseSet_trivializationAt G E' p.proj⟩
  change Topology.IsEmbedding Φ
  apply (hU.isEmbedding_iff_restrictPreimage (show Continuous Φ from hφ)).2
  intro b₀
  -- This instance is derived in a context containing a given base point.
  let : IsModuleTopology κ F := isModuleTopology_model_of_injective_at φ b₀ (hf b₀) hφ
  let A : s b₀ → F →L[κ] G := fun b ↦
    ⟨((e' b₀).linearMapAt κ b).comp ((φ b).comp ((e b₀).symmₗ κ b)),
      IsModuleTopology.continuous_of_linearMap _⟩
  have hA : Continuous A :=
    ((e b₀).continuousOn_linearMapAt_comp_of_isModuleTopology (e' b₀) φ hφ).domRestrict
  have hanti : ∀ b : s b₀, ∃ V ∈ 𝓝 b, ∃ K : ℝ≥0,
      ∀ c ∈ V, AntilipschitzWith K (A c) := by
    intro b
    have hb : Topology.IsEmbedding (A b) :=
      isEmbedding_linearMapAt_comp (e b₀) (e' b₀) φ b b.2 (hf b) hφ
    obtain ⟨K, hK⟩ := (A b).antilipschitz_of_isEmbedding hb
    -- Enlarge the constant so its inverse is positive even for a zero source model.
    have hK' : AntilipschitzWith (K + 1) (A b) :=
      AntilipschitzWith.of_le_mul_nndist fun x y ↦
        (hK.le_mul_nndist x y).trans
          (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 1 from zero_le_one))
            (show 0 ≤ nndist (A b x) (A b y) from zero_le))
    have hKpos : 0 < K + 1 :=
      add_pos_of_nonneg_of_pos (show (0 : ℝ≥0) ≤ K from zero_le) zero_lt_one
    have hc : 0 < ((K + 1)⁻¹ : ℝ≥0) := inv_pos.mpr hKpos
    obtain ⟨V, hV, hbV, δ, hδ, hbound⟩ :=
      ContinuousLinearMap.exists_isOpen_uniform_lower_bound (hA.continuousAt (x := b))
        (NNReal.coe_pos.mpr hc)
        (fun v ↦ by simpa only [map_zero, dist_zero_right] using hK'.mul_le_dist v 0)
    let δ' : ℝ≥0 := ⟨δ, hδ.le⟩
    refine ⟨V, hV.mem_nhds hbV, δ'⁻¹, ?_⟩
    intro c hcV
    apply (A c).antilipschitz_of_bound
    intro v
    change ‖v‖ ≤ δ⁻¹ * ‖A c v‖
    rw [← div_eq_inv_mul, le_div_iff₀ hδ]
    simpa only [mul_comm] using hbound c hcV v
  have hprod : Topology.IsEmbedding (fun p : s b₀ × F ↦ (p.1, A p.1 p.2)) :=
    Topology.isEmbedding_prodMk_of_locally_antilipschitz
      ((hA.comp continuous_fst).clm_apply continuous_snd) hanti
  exact isEmbedding_restrictPreimage_of_coordinates (e b₀) (e' b₀) φ (s b₀)
    (fun _ hb ↦ hb) hprod

end VectorBundle
