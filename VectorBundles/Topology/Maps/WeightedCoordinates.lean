/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.LinearAlgebra.WeightedCoordinates
public import VectorBundles.Topology.ContinuousMap.WeightedExtension
public import Mathlib.Topology.Constructions

/-!
# Continuity of supported weighted coordinates

The fibres in this module are the original equality subtypes of a map `p : T → X`.
Their additive and module structures are given, and their topology is inherited
from `T`. Exact inverse coordinates are assumed continuous only on their
domains. No topological compatibility of the fibre operations is assumed.

Unlike the chart domains of an open atlas, the subsets used by this continuity
helper may be arbitrary. The closed cozero support of each weight must lie in its
domain; containment of the cozero set alone would not suffice.

## Implementation notes

For each coordinate, the value bridge uses the existing
`ContinuousMap.smulExtend` on `T`, with domain `p ⁻¹' U i`, composed weight
`w i ∘ p`, and the exact inverse coordinates. Its support input is the stock
`Continuous.closure_preimage_subset` applied to the weight's cozero set, followed
by the given support containment. Membership and nonmembership characteristic
rules identify its values with the raw coordinate; stock `continuous_pi` then
handles the full product. No second zero-extension construction is needed.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2: motivation for the finite
  weighted local-coordinate construction.
-/

@[expose] public section

universe uK uT uX uI uG

namespace LinearMap

variable {K : Type uK} [CommSemiring K] [TopologicalSpace K]
  {T : Type uT} [TopologicalSpace T] {X : Type uX} [TopologicalSpace X]
  {I : Type uI} {G : I → Type uG}
  [∀ i, AddCommMonoid (G i)] [∀ i, Module K (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, ContinuousSMul K (G i)]

variable (p : T → X)
  [∀ x, AddCommMonoid {t : T // p t = x}]
  [∀ x, Module K {t : T // p t = x}]
  (U : I → Set X) (w : I → X → K)
  (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[K] {t : T // p t = x})

/-- The total weighted coordinates on the original fibres are continuous when the
exact inverse coordinates and weights are continuous and the weights' closed cozero
supports lie in their domains. The domains need not be open; this does not weaken
any openness requirement on an atlas used by a later consumer.
-/
theorem continuous_weightedCoordinates
    (hp : Continuous p) (hw : ∀ i, Continuous (w i))
    (hσ : ∀ i, Continuous fun t : p ⁻¹' U i ↦
      (c i (p t.1) t.2).symm ⟨t.1, rfl⟩)
    (hsupport : ∀ i, closure {x | w i x ≠ 0} ⊆ U i) :
    Continuous (fun t : T ↦ weightedCoordinates U w c (p t) ⟨t, rfl⟩) := by
  classical
  apply continuous_pi
  intro i
  let wi : C(T, K) := ⟨w i ∘ p, (hw i).comp hp⟩
  let σi : C(p ⁻¹' U i, G i) :=
    ⟨fun t ↦ (c i (p t.1) t.2).symm ⟨t.1, rfl⟩, hσ i⟩
  have hsupporti : closure {t : T | w i (p t) ≠ 0} ⊆ p ⁻¹' U i :=
    (hp.closure_preimage_subset {x : X | w i x ≠ 0}).trans
      (Set.preimage_mono (hsupport i))
  have hvalue : (fun t : T ↦ weightedCoordinates U w c (p t) ⟨t, rfl⟩ i) =
      (wi.smulExtend hsupporti σi : T → G i) := by
    funext t
    by_cases ht : p t ∈ U i
    · rw [weightedCoordinates_apply_of_mem U w c ht]
      exact (ContinuousMap.smulExtend_apply_of_mem wi hsupporti σi t ht).symm
    · rw [weightedCoordinates_apply_of_notMem U w c ht]
      exact (ContinuousMap.smulExtend_apply_of_notMem wi hsupporti σi t ht).symm
  rw [hvalue]
  exact (wi.smulExtend hsupporti σi).continuous

end LinearMap
