/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.FiberEmbedding
public import VectorBundles.Topology.FiniteNormalWeights
public import VectorBundles.Topology.Maps.WeightedCoordinates

/-!
# Finite Euclidean embeddings from local coordinates

Over a normal base, a finite family of normed finite-dimensional local models,
with exact jointly continuous coordinate maps in both directions, gives a closed
embedding of the total space into a product with a Euclidean space whenever the
interiors of the specified domains cover the base. Continuous real weights with
closed cozero supports in those domains and no common zero are supplied by the
construction. Their scalar images define the weighted coordinates. The inverse
on the image extends to a jointly continuous fibrewise linear retraction. The
fibres retain their given module structures and inherited subtype topologies.

The supplied-weight theorem also applies without normality when continuous scalar
weights with the required supports and no common zero are given. The domain sets
need not be open: the nonzero-weight sets provide an open cover.

The full product of the models carries its finite-product supremum norm only as
an auxiliary space. A linear equivalence from a distinct Euclidean space supplies
the Euclidean weighted coordinates; no isometry between these norms is asserted.
No inner product on the given models, positive rank, compactness, or completeness
of an additional ambient space is required. The normal-cover theorem does not
require a T1 base. The supplied-weight theorem requires no separation axiom on
the base, positivity, or normalization of its weights.

## Implementation notes

The normal-cover theorem applies the finite real partition-of-unity theorem to
the whole base and the interiors of the domains. It retains only continuity,
closed support containment, and absence of a common zero, casts the weights to
the scalar field, and applies the supplied-weight theorem.

The supplied-weight proof composes the continuous weighted coordinates with a
finite-dimensional linear equivalence. Restricting the given charts to the open
nonzero-weight sets preserves their continuous realizations and inverse
coordinates. The realizations then give fixed-vector parameter continuity, and
the closed-embedding theorem for local coordinates supplies the extended inverse.
No norm or topological-operation structure is added to a fibre.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2: motivation for the
  finite weighted local-coordinate embedding method. The local-model hypotheses
  here permit different ranks on different components, rather than transcribing
  a variable-rank theorem from the source.
-/

@[expose] public section

open scoped BigOperators

universe uK uX uT uI uG

namespace ContinuousLinearMap

/-- Finitely many normed finite-dimensional local models and continuous scalar
weights with no common zero and closed cozero supports contained in their
specified domains give Euclidean weighted coordinates defining a closed embedding.
The supplied domain sets need not be open.
The inverse extends to a jointly continuous fibrewise linear retraction on the
whole product. The coordinates use the given chart inverses and weights without
normalization, and the equality-subtype fibres keep their given operations and
topologies. The equivalence from Euclidean space to the full product of models
is linear, not asserted to be isometric. This is motivated by the finite weighted
local-coordinate method in Hatcher, *Vector Bundles and K-Theory*, version 2.2. -/
theorem exists_retraction_isClosedEmbedding_of_weighted_local_coordinates
    (K : Type uK) [RCLike K]
    (X : Type uX) [TopologicalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommGroup {t : T // p t = x}]
    [∀ x, Module K {t : T // p t = x}]
    (I : Type uI) [Finite I] (G : I → Type uG)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (U : I → Set X) (w : I → X → K)
    (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[K] {t : T // p t = x})
    (hp : Continuous p)
    (hw : ∀ i, Continuous (w i))
    (hRealization : ∀ i, Continuous (fun q : {x : X // x ∈ U i} × G i =>
      (c i q.1.1 q.1.2 q.2).val))
    (hσ : ∀ i, Continuous (fun t : p ⁻¹' U i =>
      (c i (p t.1) t.2).symm ⟨t.1, rfl⟩))
    (hsupport : ∀ i, closure {x | w i x ≠ 0} ⊆ U i)
    (hNonzero : ∀ x, ∃ i, w i x ≠ 0) :
    ∃ e : EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) ≃ₗ[K] (∀ i, G i),
      ∃ ρ : ∀ x, EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) →L[K]
          {t : T // p t = x},
        (∀ x (v : {t : T // p t = x}),
          ρ x (e.symm (LinearMap.weightedCoordinates U w c x v)) = v) ∧
        Continuous (fun q : X × EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) =>
          (ρ q.1 q.2).val) ∧
        Topology.IsClosedEmbedding (fun t : T =>
          (p t, e.symm (LinearMap.weightedCoordinates U w c (p t) ⟨t, rfl⟩))) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let M := ∀ i, G i
  let E := EuclideanSpace K (Fin (Module.finrank K M))
  have he : Nonempty (E ≃ₗ[K] M) := by
    apply FiniteDimensional.nonempty_euclideanSpace_linearEquiv
  obtain ⟨e⟩ := he
  let β : ∀ x, {t : T // p t = x} →ₗ[K] E := fun x =>
    e.symm.toLinearMap.comp (LinearMap.weightedCoordinates U w c x)
  have hMem {x : X} {i : I} (hi : w i x ≠ 0) : x ∈ U i :=
    hsupport i (subset_closure hi)
  let V (i : I) : Set X := {x | w i x ≠ 0}
  have hOpen (i : I) : IsOpen (V i) :=
    (isClosed_eq (hw i) continuous_const).isOpen_compl
  have hCover : ∀ x, ∃ i, x ∈ V i := hNonzero
  have hInj (x : X) : Function.Injective (β x) := by
    obtain ⟨i, hi⟩ := hNonzero x
    exact e.symm.injective.comp
      (LinearMap.weightedCoordinates_injective_of_isUnit U w c (hMem hi)
        (isUnit_iff_ne_zero.mpr hi))
  have heCont : Continuous (e.symm : M → E) :=
    e.symm.toLinearMap.continuous_of_finiteDimensional
  have hBCont : Continuous (fun t : T => β (p t) ⟨t, rfl⟩) :=
    heCont.comp (LinearMap.continuous_weightedCoordinates p U w c hp hw hσ hsupport)
  have hIndex (x : X) (v : {t : T // p t = x}) :
      β (p v.val) ⟨v.val, rfl⟩ = β x v := by
    rcases v with ⟨t, ht⟩
    subst x
    rfl
  have hRealizationV : ∀ i, Continuous (fun q : {x : X // x ∈ V i} × G i =>
      (c i q.1.1 (hMem q.1.2) q.2).val) := by
    intro i
    have hIncl : Continuous (fun z : {x : X // x ∈ V i} =>
        (⟨z.1, hMem z.2⟩ : {x : X // x ∈ U i})) :=
      continuous_subtype_val.subtype_mk _
    exact (hRealization i).comp
      ((hIncl.comp continuous_fst).prodMk continuous_snd)
  have hInverse : ∀ i, Continuous (fun t : {t : T // p t ∈ V i} =>
      ((⟨p t.1, t.2⟩ : {x : X // x ∈ V i}),
        (c i (p t.1) (hMem t.2)).symm ⟨t.1, rfl⟩)) := by
    intro i
    have hIncl : Continuous (fun t : {t : T // p t ∈ V i} =>
        (⟨t.1, hMem t.2⟩ : {t : T // p t ∈ U i})) :=
      continuous_subtype_val.subtype_mk _
    exact ((hp.comp continuous_subtype_val).subtype_mk (fun t => t.2)).prodMk
      ((hσ i).comp hIncl)
  have hFrame : ∀ i (v : G i), Continuous (fun z : {x : X // x ∈ V i} =>
      β z.1 (c i z.1 (hMem z.2) v)) := by
    intro i v
    have hΦ : Continuous (fun z : {x : X // x ∈ V i} =>
        (c i z.1 (hMem z.2) v).val) :=
      (hRealizationV i).comp (continuous_id.prodMk continuous_const)
    apply (hBCont.comp hΦ).congr
    intro z
    exact hIndex z.1 (c i z.1 (hMem z.2) v)
  obtain ⟨ρ, hρ, hCont, hClosed⟩ :=
    ContinuousLinearMap.exists_retraction_isClosedEmbedding_of_local_coordinates
      K X T p E I G V β (fun i z => c i z.1 (hMem z.2))
      hp hOpen hCover hInj hRealizationV hInverse hFrame
  exact ⟨e, ρ, hρ, hCont, hClosed⟩

/-- Over a normal base, finitely many normed finite-dimensional local models with
jointly continuous realizations and inverse vector coordinates admit supported
continuous real weights whenever their domain interiors cover the base. The
scalar images of these weights give Euclidean weighted coordinates defining a
closed embedding. Its inverse extends to a jointly continuous fibrewise linear
retraction on the whole product.

The equality-subtype fibres keep their given operations and inherited topologies.
The dimension is the finrank of the full product of models; the equivalence from
Euclidean space to that product is linear, not asserted to be isometric. No T1 or
compactness assumption on the base, nonemptiness of the base or index type,
positive rank, or inner product on the given models is needed. The finite weighted
local-coordinate method in Hatcher, *Vector Bundles and K-Theory*, version 2.2,
motivates this construction; the local models here may have different dimensions
on different base components. -/
theorem exists_retraction_isClosedEmbedding_of_finite_normal_cover
    (K : Type uK) [RCLike K]
    (X : Type uX) [TopologicalSpace X] [NormalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommGroup {t : T // p t = x}]
    [∀ x, Module K {t : T // p t = x}]
    (I : Type uI) [Finite I] (G : I → Type uG)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (U : I → Set X)
    (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[K] {t : T // p t = x})
    (hp : Continuous p)
    (hRealization : ∀ i, Continuous (fun q : {x : X // x ∈ U i} × G i =>
      (c i q.1.1 q.1.2 q.2).val))
    (hσ : ∀ i, Continuous (fun t : p ⁻¹' U i =>
      (c i (p t.1) t.2).symm ⟨t.1, rfl⟩))
    (hcover : ∀ x, ∃ i, x ∈ interior (U i)) :
    ∃ w : I → X → ℝ,
      (∀ i, Continuous (w i)) ∧
      (∀ i, closure {x | w i x ≠ 0} ⊆ U i) ∧
      (∀ x, ∃ i, w i x ≠ 0) ∧
      ∃ e : EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) ≃ₗ[K] (∀ i, G i),
        ∃ ρ : ∀ x, EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) →L[K]
            {t : T // p t = x},
          (∀ x (v : {t : T // p t = x}),
            ρ x (e.symm (LinearMap.weightedCoordinates U (fun i x => (w i x : K))
              c x v)) = v) ∧
          Continuous (fun q : X × EuclideanSpace K (Fin (Module.finrank K (∀ i, G i))) =>
            (ρ q.1 q.2).val) ∧
          Topology.IsClosedEmbedding (fun t : T =>
            (p t, e.symm (LinearMap.weightedCoordinates U (fun i x => (w i x : K))
              c (p t) ⟨t, rfl⟩))) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hCover : (Set.univ : Set X) ⊆ ⋃ i, interior (U i) := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨w, hw, _, _, hsum, hsupp⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set X)).exists_finite_continuous_partition_of_unity
      (fun i => isOpen_interior) hCover
  have hsupport : ∀ i, closure {x | w i x ≠ 0} ⊆ U i := by
    intro i
    exact (hsupp i).trans interior_subset
  have hNonzero : ∀ x, ∃ i, w i x ≠ 0 := by
    intro x
    by_contra h
    have hz : ∀ i, w i x = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have hzero : (∑ i, w i x) = 0 := Finset.sum_eq_zero (fun i _ => hz i)
    exact zero_ne_one (hzero.symm.trans (hsum x (Set.mem_univ x)))
  let wK : I → X → K := fun i x => (w i x : K)
  have hwK : ∀ i, Continuous (wK i) := fun i =>
    RCLike.continuous_ofReal.comp (hw i)
  have hcozero (i : I) : {x | wK i x ≠ 0} = {x | w i x ≠ 0} := by
    ext x
    exact RCLike.ofReal_ne_zero
  have hsupportK : ∀ i, closure {x | wK i x ≠ 0} ⊆ U i := by
    intro i
    rw [hcozero i]
    exact hsupport i
  have hNonzeroK : ∀ x, ∃ i, wK i x ≠ 0 := by
    intro x
    obtain ⟨i, hi⟩ := hNonzero x
    exact ⟨i, RCLike.ofReal_ne_zero.mpr hi⟩
  obtain ⟨e, ρ, hρ, hCont, hClosed⟩ :=
    ContinuousLinearMap.exists_retraction_isClosedEmbedding_of_weighted_local_coordinates
      K X T p I G U wK c hp hwK hRealization hσ hsupportK hNonzeroK
  exact ⟨w, hw, hsupport, hNonzero, e, ρ, hρ, hCont, hClosed⟩

end ContinuousLinearMap
