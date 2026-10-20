/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Lindelof
public import VectorBundles.Topology.FiberBundle.Trivialization.Lindelof

/-!
# Lindelöf bundles over locally compact Lindelöf bases

A fiber bundle over a locally compact Lindelöf base has Lindelöf total space
when its model is Lindelöf. The base, model, total-space and fiber topologies,
and the `FiberBundle` data coupling them, are the original ones. Neither
separation nor nonemptiness assumptions are imposed.

## References

The compact-neighborhood argument follows the corresponding sigma-compact
bundle proof, using Mathlib's local compactness and Lindelöf subcover APIs.
Compact neighborhoods inside chart bases give Lindelöf supported preimages;
a countable subcover of their interiors then covers the original total space.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle with Lindelöf model over a locally compact Lindelöf base
has Lindelöf original total space, without separation or nonemptiness assumptions. -/
theorem lindelofSpace_of_locallyCompactSpace_base
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [LindelofSpace B] [LocallyCompactSpace B]
    [LindelofSpace F] : LindelofSpace (Bundle.TotalSpace F E) := by
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
  have hpreimage (b : B) : IsLindelof ((π F E) ⁻¹' K b) :=
    (trivializationAt F E b).isLindelof_preimage (K b)
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
  apply isLindelof_univ_iff.mp
  rw [← hunion]
  exact hs.isLindelof_biUnion (fun b _ ↦ hpreimage b)

end FiberBundle
