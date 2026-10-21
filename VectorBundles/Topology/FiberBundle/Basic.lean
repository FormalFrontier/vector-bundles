/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Emptiness of fiber-bundle total spaces

A fiber bundle has empty total space exactly when its base or its model fiber is empty.
The characterization retains the given topologies and fiber-bundle structure.
-/

@[expose] public section

universe uB uF uE

namespace FiberBundle

/-- A fiber bundle has empty total space if and only if its base or its model fiber is empty. -/
theorem isEmpty_totalSpace_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [tB : TopologicalSpace B] [tF : TopologicalSpace F]
    [tT : TopologicalSpace (Bundle.TotalSpace F E)]
    [tE : ∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] :
    IsEmpty (Bundle.TotalSpace F E) ↔ (IsEmpty B ∨ IsEmpty F) := by
  classical
  constructor
  · intro h
    by_cases hB : Nonempty B
    · obtain ⟨b⟩ := hB
      exact Or.inr ⟨fun f =>
        h.false ((trivializationAt F E b).toOpenPartialHomeomorph.symm (b, f))⟩
    · exact Or.inl ⟨fun b => hB ⟨b⟩⟩
  · rintro (hB | hF)
    · exact ⟨fun t => hB.false t.proj⟩
    · exact ⟨fun t => hF.false ((trivializationAt F E t.proj) t).2⟩

end FiberBundle
