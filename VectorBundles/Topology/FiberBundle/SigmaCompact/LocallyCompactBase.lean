/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.LocallyCompact
public import VectorBundles.Topology.FiberBundle.SigmaCompact
public import VectorBundles.Topology.FiberBundle.Trivialization.SigmaCompact

/-!
# Sigma-compact bundle totals over locally compact Lindelöf bases

A fiber bundle with a locally compact Lindelöf base and sigma-compact model has
sigma-compact total space. Mathlib's `LocallyCompactSpace` supplies compact
neighborhoods inside prescribed open chart bases; these compact neighborhoods need
not be open or closed. No separation assumption on the base, model, or total space,
and no nonemptiness assumption, is required. The four given topology instances
and their coupled `FiberBundle` structure are retained.

## References

The statement uses Mathlib's local compactness, Lindelöf, trivialization, and
sigma-compactness APIs. The formulation follows Formal Frontier's fiber-bundle
total-space approach, developed with AI assistance.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle over a locally compact Lindelöf base with sigma-compact model has
sigma-compact total space, without separation or nonemptiness assumptions. -/
theorem sigmaCompactSpace_of_locallyCompactSpace_base
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [LindelofSpace B] [LocallyCompactSpace B] [SigmaCompactSpace F] :
    SigmaCompactSpace (TotalSpace F E) := by
  classical
  have hcompact (b : B) :
      ∃ K : Set B, IsCompact K ∧ b ∈ interior K ∧
        K ⊆ (trivializationAt F E b).baseSet :=
    exists_compact_subset (trivializationAt F E b).open_baseSet
      (mem_baseSet_trivializationAt F E b)
  choose K hKcompact hKmem hKbase using hcompact
  obtain ⟨s, hs, hcover⟩ :=
    LindelofSpace.elim_nhds_subcover (fun b : B ↦ interior (K b))
      (fun b ↦ isOpen_interior.mem_nhds (hKmem b))
  have hpreimage (b : B) : IsSigmaCompact ((π F E) ⁻¹' K b) :=
    (trivializationAt F E b).isSigmaCompact_preimage (K b)
      (hKcompact b).isSigmaCompact (hKbase b)
  have hunion : (⋃ b ∈ s, (π F E) ⁻¹' K b) =
      (Set.univ : Set (TotalSpace F E)) := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : (π F E) z ∈ ⋃ b ∈ s, interior (K b) := by
      rw [hcover]
      exact Set.mem_univ _
    rcases Set.mem_iUnion.mp hz with ⟨b, hb⟩
    rcases Set.mem_iUnion.mp hb with ⟨hbs, hzb⟩
    exact Set.mem_iUnion.mpr
      ⟨b, Set.mem_iUnion.mpr ⟨hbs, (interior_subset : interior (K b) ⊆ K b) hzb⟩⟩
  apply isSigmaCompact_univ_iff.mp
  rw [← hunion]
  exact isSigmaCompact_biUnion hs (fun b _ ↦ hpreimage b)

end FiberBundle
