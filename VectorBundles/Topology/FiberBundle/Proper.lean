/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper projections and compactness of fiber bundles

The projection of a topological fiber bundle is proper if and only if every fiber is compact.
In particular, a compact model fiber makes the projection proper. These statements use the given
topologies on the base, model, total space, and fibers, together with their `FiberBundle` structure.
No separation, local compactness, or inhabitation assumption on the base is needed.

Properness means Mathlib's `IsProperMap`: continuity and universal closedness, equivalently
continuity, closedness, and compact fibers. Compactness of every fiber is the sharp formulation:
when the base is empty, the projection is proper even if the model is not compact.

A compact base and compact model give a compact total space. When the model is nonempty,
compactness of the total space also implies compactness of the base. If the base has a point,
compactness of the total space implies compactness of the model. Thus, when both base and model
are nonempty, compactness of the total space is equivalent to compactness of the base and model.
These results also require no separation assumptions.

## References

* Mathlib's fiber-bundle and trivialization development, by Sébastien Gouëzel, Floris van Doorn,
  Heather Macbeth, and contributors.
* Mathlib's proper-map development, by Anatole Dedecker and Etienne Marion, including
  `isProperMap_iff_isClosedMap_and_compact_fibers` and `isProperMap_fst_of_compactSpace`.
* Mathlib's compactness development, by Johannes Hölzl, Mario Carneiro, Yury Kudryashov,
  and contributors, including `IsClosed.exists_minimal_nonempty_closed_subset`.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

private theorem compactSpace_fiber_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) :
    CompactSpace (E b) ↔ IsCompact (TotalSpace.proj (F := F) (E := E) ⁻¹' {b}) := by
  rw [← isCompact_univ_iff, (totalSpaceMk_isEmbedding F E b).isCompact_iff,
    Set.image_univ, TotalSpace.range_mk]

/-- A fiber-bundle projection is proper exactly when every fiber, with its given topology,
is compact. The base and the model need not be inhabited. -/
theorem isProperMap_proj_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] :
    IsProperMap (TotalSpace.proj (F := F) (E := E)) ↔ ∀ b, CompactSpace (E b) := by
  constructor
  · intro h b
    exact (compactSpace_fiber_iff F E b).2 (h.isCompact_preimage isCompact_singleton)
  · intro h
    refine isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨continuous_proj F E, ?_, fun b ↦ (compactSpace_fiber_iff F E b).1 (h b)⟩
    -- The chosen chart at each base point gives an open cover, including for an empty base.
    have hcover := TopologicalSpace.IsOpenCover.of_sets
      (fun b ↦ (trivializationAt F E b).open_baseSet) (by
        ext b
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        exact ⟨b, mem_baseSet_trivializationAt F E b⟩)
    apply hcover.isClosedMap_iff_restrictPreimage.2
    intro b
    let : CompactSpace (E b) := h b
    let : CompactSpace F := (homeomorphAt F E b).compactSpace
    -- The restriction targets the chart's base subtype, so it is a product projection.
    have hproj :
        (trivializationAt F E b).baseSet.restrictPreimage
            (TotalSpace.proj (F := F) (E := E)) =
          Prod.fst ∘ (trivializationAt F E b).preimageHomeomorph Set.Subset.rfl := by
      funext x
      apply Subtype.ext
      simp only [Set.restrictPreimage_coe, Function.comp_apply,
        Trivialization.preimageHomeomorph_apply]
    rw [hproj]
    exact ((isProperMap_fst_of_compactSpace
      (X := (trivializationAt F E b).baseSet) (Y := F)).comp
        ((trivializationAt F E b).preimageHomeomorph Set.Subset.rfl).isProperMap).isClosedMap

/-- The projection of a fiber bundle with compact model fiber is proper, without separation
or local compactness assumptions on the base. -/
theorem isProperMap_proj
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [CompactSpace F] :
    IsProperMap (TotalSpace.proj (F := F) (E := E)) := by
  apply (isProperMap_proj_iff F E).2
  intro b
  exact (homeomorphAt F E b).symm.compactSpace

/-! ## Compactness transfer -/

/-- A fiber bundle with compact base and compact model has compact total space.
No separation or inhabitation assumption is needed. -/
theorem compactSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [CompactSpace B] [CompactSpace F] :
    CompactSpace (TotalSpace F E) := by
  rw [← isCompact_univ_iff]
  simpa only [Set.preimage_univ] using
    (isProperMap_proj F E).isCompact_preimage (isCompact_univ : IsCompact (Set.univ : Set B))

/-- If the total space of a fiber bundle is compact and the base has a point, then the model
is compact. No separation assumption on the base is needed. -/
theorem compactSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [CompactSpace (TotalSpace F E)] (b : B) :
    CompactSpace F := by
  classical
  cases isEmpty_or_nonempty F with
  | inl hF =>
    let : IsEmpty F := hF
    infer_instance
  | inr hF =>
    let : Nonempty F := hF
    let : CompactSpace B :=
      Function.Surjective.compactSpace (continuous_proj F E) (surjective_proj F E)
    obtain ⟨K, -, hKne, hKclosed, hKmin⟩ :=
      isClosed_univ.exists_minimal_nonempty_closed_subset
        (show (Set.univ : Set B).Nonempty from ⟨b, Set.mem_univ b⟩)
    obtain ⟨c, hc⟩ := hKne
    -- A minimal nonempty closed set lies in any chart meeting it. This avoids requiring
    -- a closed singleton, which need not exist without separation assumptions.
    have hKchart : K ⊆ (trivializationAt F E c).baseSet := by
      intro x hx
      by_contra hxchart
      have hdiff : K \ (trivializationAt F E c).baseSet = K :=
        hKmin _ (fun _ hy ↦ hy.1) ⟨x, hx, hxchart⟩
          (hKclosed.inter (trivializationAt F E c).open_baseSet.isClosed_compl)
      have hc' : c ∈ K \ (trivializationAt F E c).baseSet := by
        rw [hdiff]
        exact hc
      exact hc'.2 (mem_baseSet_trivializationAt F E c)
    let : CompactSpace (TotalSpace.proj (F := F) (E := E) ⁻¹' K) :=
      isCompact_iff_compactSpace.mp
        (hKclosed.preimage (continuous_proj F E)).isCompact
    let : CompactSpace (K × F) :=
      ((trivializationAt F E c).preimageHomeomorph hKchart).compactSpace
    exact Function.Surjective.compactSpace
      (continuous_snd : Continuous (Prod.snd : K × F → F))
      (fun y ↦ ⟨(⟨c, hc⟩, y), rfl⟩)

/-- For a fiber bundle with nonempty base and model, compactness of the total space is equivalent
to compactness of the base and the model. No separation assumption is needed. -/
theorem compactSpace_totalSpace_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [Nonempty B] [Nonempty F] :
    CompactSpace (TotalSpace F E) ↔ CompactSpace B ∧ CompactSpace F := by
  constructor
  · intro htotal
    let : CompactSpace (TotalSpace F E) := htotal
    exact ⟨Function.Surjective.compactSpace (continuous_proj F E) (surjective_proj F E),
      compactSpace_model F E (Classical.choice ‹Nonempty B›)⟩
  · rintro ⟨hB, hF⟩
    let : CompactSpace B := hB
    let : CompactSpace F := hF
    exact compactSpace_totalSpace F E

end FiberBundle
