/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Metrization.LocallyFinite
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizability of fiber bundles

A fiber bundle with metrizable base and model has a metrizable total space. Conversely,
metrizability of the total space gives metrizability of the model at any specified base point.
These results use the given topologies on the base, model, total space, and individual fibers,
together with their fiber-bundle structure. No scalar or vector-space structure is required.

The model conclusion needs a base point: an empty base has empty total space, independently
of the topology on the model. Neither result requires the model to be inhabited.

## References

* Mathlib's fiber-bundle and metrizable-space developments.
-/

@[expose] public section

open Bundle TopologicalSpace

universe uB uF uE

namespace FiberBundle

/-- The total space of a fiber bundle with metrizable base and model is metrizable for its
given topology. Neither the base nor the model is required to be inhabited. -/
theorem metrizableSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [MetrizableSpace B] [MetrizableSpace F] :
    MetrizableSpace (TotalSpace F E) := by
  classical
  haveI : ParacompactSpace B := by
    letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric B
    infer_instance
  have hshrink : ∀ b : B, ∃ V : Set B,
      b ∈ V ∧ IsOpen V ∧ closure V ⊆ (trivializationAt F E b).baseSet := by
    intro b
    obtain ⟨V, ⟨hb, hVopen⟩, hVsub⟩ := (hasBasis_opens_closure b).mem_iff.mp
      ((trivializationAt F E b).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E b))
    exact ⟨V, hb, hVopen, hVsub⟩
  choose V hVmem hVopen hVsub using hshrink
  have hVcover : (⋃ b, V b) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    exact Set.mem_iUnion.mpr ⟨b, hVmem b⟩
  obtain ⟨W, hWopen, hWcover, hWfin, hWsub⟩ :=
    precise_refinement V hVopen hVcover
  have hchart : ∀ b, closure (W b) ⊆ (trivializationAt F E b).baseSet := by
    intro b
    exact (closure_mono (hWsub b)).trans (hVsub b)
  refine TopologicalSpace.metrizableSpace_of_locallyFinite_isClosed_interior_cover
    (fun b => (π F E) ⁻¹' closure (W b))
    (hWfin.closure.preimage_continuous (continuous_proj F E))
    (fun _ => isClosed_closure.preimage (continuous_proj F E)) ?_ ?_
  · apply Set.eq_univ_of_forall
    intro x
    have hx : π F E x ∈ ⋃ b, W b := by
      rw [hWcover]
      exact Set.mem_univ _
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    exact interior_maximal (Set.preimage_mono subset_closure)
      ((hWopen b).preimage (continuous_proj F E)) hb
  · intro b
    exact ((trivializationAt F E b).preimageHomeomorph (hchart b)).isEmbedding.metrizableSpace

/-- If the total space of a fiber bundle is metrizable, its model is metrizable at any
specified base point. The point is essential: over an empty base the total space is empty,
so its metrizability imposes no restriction on the model. -/
theorem metrizableSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [MetrizableSpace (TotalSpace F E)] (b : B) :
    MetrizableSpace F := by
  exact ((FiberBundle.totalSpaceMk_isEmbedding F E b).comp
    (FiberBundle.homeomorphAt F E b).symm.isEmbedding).metrizableSpace

end FiberBundle
