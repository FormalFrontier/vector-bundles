/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Compactness.Lindelof
public import VectorBundles.Topology.FiberBundle.Proper

/-!
# Lindelöf total spaces with compact model fibers

A fiber bundle over a Lindelöf base with compact model fiber has a Lindelöf total space.
The result uses the given topologies on the base, model, total space, and fibers, together with
their `FiberBundle` structure. It requires no separation, local compactness, or nonemptiness
assumptions.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle over a Lindelöf base with compact model fiber has a Lindelöf total space,
with respect to the given total-space topology. -/
theorem lindelofSpace_totalSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [LindelofSpace B] [CompactSpace F] :
    LindelofSpace (TotalSpace F E) := by
  exact isLindelof_univ_iff.mp
    ((FiberBundle.isProperMap_proj F E).isLindelof_preimage
      (isLindelof_univ : IsLindelof (Set.univ : Set B)))

end FiberBundle

/-- A fiber bundle with compact model fiber has Lindelöf total space if and only if its model
fiber is empty or its base is Lindelöf. -/
theorem FiberBundle.lindelofSpace_totalSpace_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [CompactSpace F] :
    LindelofSpace (Bundle.TotalSpace F E) ↔ (IsEmpty F ∨ LindelofSpace B) := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty F with hF | hF
    · exact Or.inl hF
    · letI : Nonempty F := hF
      letI : LindelofSpace (Bundle.TotalSpace F E) := h
      exact Or.inr (LindelofSpace.of_continuous_surjective
        (FiberBundle.continuous_proj F E) (FiberBundle.surjective_proj F E))
  · rintro (hF | hB)
    · letI : IsEmpty F := hF
      letI : IsEmpty (Bundle.TotalSpace F E) :=
        isEmpty_iff.mpr fun z =>
          isEmptyElim ((FiberBundle.homeomorphAt F E z.proj) z.snd)
      infer_instance
    · letI : LindelofSpace B := hB
      exact FiberBundle.lindelofSpace_totalSpace F E
