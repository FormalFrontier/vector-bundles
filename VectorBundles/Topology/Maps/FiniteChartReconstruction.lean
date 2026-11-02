/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.LinearAlgebra.WeightedCoordinates
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed embeddings from finite chart reconstruction

A finite chart reconstruction that is a linear left inverse to weighted coordinates
induces a left inverse on the original total space. The range of the total coordinate
map is the equalizer of two model-valued maps: reconstructing and taking coordinates
again, and the original model projection.

If the total coordinate map and reconstruction are continuous, this equalizer is
closed whenever the full product of models is Hausdorff. Thus the total coordinate
map is a closed embedding, without any separation assumption on the base or total
space.

## Implementation notes

The fibre modules are the given modules on the equality subtypes of the original
total space. Reconstruction uses the existing finite constructor on the indices
valid at each base point. Continuity of the exact total maps and their pointwise
linear left-inverse law are hypotheses; no topology on the scalars or continuity
of the model operations is needed for these consequences.

## References

* Mathlib's `Topology.IsEmbedding.of_leftInverse` and `isClosed_eq` supply the
  topological embedding and Hausdorff equalizer arguments.
-/

@[expose] public section

universe uR uX uT uI uG

namespace LinearMap

variable {R : Type uR} [CommSemiring R]
  {X : Type uX} {T : Type uT} {I : Type uI}
  {G : I → Type uG} {p : T → X}
  [∀ x : X, AddCommMonoid {t : T // p t = x}]
  [∀ x : X, Module R {t : T // p t = x}]
  [∀ i : I, AddCommMonoid (G i)]
  [∀ i : I, Module R (G i)]

variable (U : I → Set X)
  (c : ∀ (i : I) (x : X),
    x ∈ U i → G i ≃ₗ[R] {t : T // p t = x})
  (s : Finset I) (a w : I → X → R)

attribute [local instance] Classical.propDecidable

local notation "ρ" =>
  (fun x : X =>
    finiteChartReconstruction U c x
      (s.filter (fun i : I => x ∈ U i))
      (fun i : I => a i x)
      (fun (i : I) hi =>
        And.right (Iff.mp
          (Finset.mem_filter (p := fun j : I => x ∈ U j) (s := s) (a := i)) hi)))

local notation "r" =>
  (fun z : X × (∀ i : I, G i) => Subtype.val (ρ (Prod.fst z) (Prod.snd z)))

local notation "b" =>
  (fun t : T =>
    Prod.mk (p t) (weightedCoordinates U w c (p t) (Subtype.mk t rfl)))

private theorem leftInverse_weightedCoordinates_of_finiteChartReconstruction
    (hleft : ∀ x : X,
      (ρ x).comp (weightedCoordinates U w c x) = LinearMap.id) :
    Function.LeftInverse r b := by
  intro t
  -- Evaluate the linear-map identity in the original equality fibre, then forget
  -- only the subtype proof, not the given fibre operations.
  have hv : ρ (p t) (weightedCoordinates U w c (p t) ⟨t, rfl⟩) = ⟨t, rfl⟩ :=
    congrArg
      (fun f : {v : T // p v = p t} →ₗ[R] {v : T // p v = p t} =>
        f ⟨t, rfl⟩)
      (hleft (p t))
  exact congrArg Subtype.val hv

/-- The range of weighted coordinates is the model-coordinate equalizer of
reconstruction followed by the total coordinate map and the model projection. -/
theorem range_weightedCoordinates_eq_finiteChartReconstruction_equalizer
    (hleft : ∀ x : X,
      (ρ x).comp (weightedCoordinates U w c x) = LinearMap.id) :
    Set.range b =
      {z : X × (∀ i : I, G i) | (b (r z)).2 = z.2} := by
  have hleft_total : Function.LeftInverse r b :=
    leftInverse_weightedCoordinates_of_finiteChartReconstruction U c s a w hleft
  apply Set.ext
  intro z
  constructor
  · rintro ⟨t, rfl⟩
    exact congrArg (fun t : T => (b t).2) (hleft_total t)
  · intro hz
    exact ⟨r z, Prod.ext (ρ z.1 z.2).property hz⟩

section ClosedRange

variable [TopologicalSpace X] [TopologicalSpace T]
  [∀ i : I, TopologicalSpace (G i)]

/-- Continuous weighted coordinates with a continuous finite reconstruction have
closed range when the model product is Hausdorff. No separation assumption on the
base or original total space is required. -/
theorem isClosed_range_weightedCoordinates_of_finiteChartReconstruction
    [T2Space (∀ i : I, G i)]
    (hr : Continuous r) (hb : Continuous b)
    (hleft : ∀ x : X,
      (ρ x).comp (weightedCoordinates U w c x) = LinearMap.id) :
    IsClosed (Set.range b) := by
  rw [range_weightedCoordinates_eq_finiteChartReconstruction_equalizer U c s a w hleft]
  exact isClosed_eq (continuous_snd.comp (hb.comp hr)) continuous_snd

/-- Continuous weighted coordinates with a continuous finite reconstruction form
a closed embedding when the model product is Hausdorff. Only model-valued maps
are compared to prove closedness. -/
theorem isClosedEmbedding_weightedCoordinates_of_finiteChartReconstruction
    [T2Space (∀ i : I, G i)]
    (hr : Continuous r) (hb : Continuous b)
    (hleft : ∀ x : X,
      (ρ x).comp (weightedCoordinates U w c x) = LinearMap.id) :
    Topology.IsClosedEmbedding b := by
  have hleft_total : Function.LeftInverse r b :=
    leftInverse_weightedCoordinates_of_finiteChartReconstruction U c s a w hleft
  exact ⟨hleft_total.isEmbedding hr hb,
    isClosed_range_weightedCoordinates_of_finiteChartReconstruction U c s a w hr hb hleft⟩

end ClosedRange

end LinearMap
