/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order
public import VectorBundles.Topology.LocallyFinite

/-!
# Locally finite images of a two-sheeted discrete projection

The first projection `ℕ × Fin 2 → ℕ` is closed with compact fibers. Its family of
fibers is indexed by the infinite type `ℕ`, and every member is nonempty. Discrete
singleton neighborhoods give local finiteness on `ℕ`; Mathlib's
`LocallyFinite.preimage_continuous` supplies the source-family hypothesis.
The image conclusion is obtained directly from `IsClosedMap.locallyFinite_image`,
not from finiteness of the index type.
-/

@[expose] public section

/-- The images of the infinitely many nonempty fibers of the canonical two-sheeted
projection form a locally finite family in the discrete natural numbers. -/
example : LocallyFinite (fun n : ℕ =>
    (Prod.fst : ℕ × Fin 2 → ℕ) ''
      ((Prod.fst : ℕ × Fin 2 → ℕ) ⁻¹' ({n} : Set ℕ))) := by
  have hsingle : LocallyFinite (fun n : ℕ => ({n} : Set ℕ)) := by
    intro n
    refine ⟨{n}, (isOpen_discrete ({n} : Set ℕ)).mem_nhds (Set.mem_singleton n), ?_⟩
    refine (Set.finite_singleton n).subset ?_
    rintro i ⟨x, hxi, hxn⟩
    exact Set.mem_singleton_iff.mpr
      ((Set.mem_singleton_iff.mp hxi).symm.trans (Set.mem_singleton_iff.mp hxn))
  have hproper : IsProperMap (Prod.fst : ℕ × Fin 2 → ℕ) :=
    isProperMap_fst_of_compactSpace (X := ℕ) (Y := Fin 2)
  exact IsClosedMap.locallyFinite_image hproper.isClosedMap
    (fun n => hproper.isCompact_preimage (isCompact_singleton : IsCompact ({n} : Set ℕ)))
    (fun n => (Prod.fst : ℕ × Fin 2 → ℕ) ⁻¹' ({n} : Set ℕ))
    (hsingle.preimage_continuous continuous_fst)
