/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.InducingRetraction
public import VectorBundles.Analysis.Normed.Module.JointEvaluation

/-!
# Continuity and closed fibre embeddings from finite-dimensional local coordinates

Over a complete nontrivially normed field, algebraic maps from the equality-subtype
fibres of a continuous map into a module with continuous addition and scalar
multiplication are continuous on the total space when their values at each fixed
local coordinate vector depend continuously on the base point and their exact
inverse vector coordinates are continuous. The finite-dimensional Hausdorff
topological coordinate models may vary over an arbitrary open cover. The fibres
retain their given module structures and subspace topologies; no injectivity or
continuity of forward coordinate realizations is required.

Over real or complex scalars, jointly continuous coordinate realizations and
injective fibre maps into a normed inner-product space give the stronger conclusion
of a closed embedding into a product, whose inverse extends to a jointly continuous
fibrewise linear retraction. No norm or new topology is imposed on the fibres,
the ambient space need not be complete, and the base need not satisfy any
separation axiom.

The proofs use finite-dimensional evaluation continuity and the inducing-retraction
criterion. The embedded image is the fixed-point set of the resulting continuous
family of ambient projections.
-/

@[expose] public section

universe uK uX uT uA uI uG

namespace LinearMap

/-- Algebraic fibre maps are continuous on the total space if their values on each
fixed local coordinate vector depend continuously on the base point and their exact
inverse vector coordinates are continuous. The equality-subtype fibres retain their
given module structures and subspace topologies. The scalar field is complete, the
finite-dimensional coordinate models carry their given Hausdorff topological module
structures, and the target only needs continuous addition and scalar multiplication;
no injectivity or continuity of forward coordinate realizations is required. -/
theorem continuous_total_of_local_coordinates
    (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
    (X : Type uX) [TopologicalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommMonoid {t : T // p t = x}]
    [∀ x, Module K {t : T // p t = x}]
    (A : Type uA) [AddCommMonoid A] [Module K A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul K A]
    (I : Type uI) (G : I → Type uG)
    [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalAddGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, ContinuousSMul K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (U : I → Set X)
    (β : ∀ x, {t : T // p t = x} →ₗ[K] A)
    (c : ∀ i (z : {x : X // x ∈ U i}), G i ≃ₗ[K] {t : T // p t = z.1})
    (hp : Continuous p)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hInverseCoordinates : ∀ i, Continuous (fun t : {t : T // p t ∈ U i} =>
      (c i ⟨p t.1, t.2⟩).symm ⟨t.1, rfl⟩))
    (hFrame : ∀ i (v : G i), Continuous (fun z : {x : X // x ∈ U i} =>
      β z.1 (c i z v))) :
    Continuous (fun t : T => β (p t) ⟨t, rfl⟩) := by
  let L (i : I) (z : {x : X // x ∈ U i}) : G i →ₗ[K] A :=
    (β z.1).comp (c i z).toLinearMap
  have hLJoint (i : I) : Continuous
      (fun q : {x : X // x ∈ U i} × G i => L i q.1 q.2) :=
    (LinearMap.continuous_uncurry_iff_of_finiteDimensional
      (L := L i)).2 (hFrame i)
  let V (i : I) : Set T := {t | p t ∈ U i}
  refine continuous_of_cover_nhds (s := V) ?_ ?_
  · intro t
    obtain ⟨i, hi⟩ := hCover (p t)
    exact ⟨i, ((hOpen i).preimage hp).mem_nhds hi⟩
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hBase : Continuous (fun t : {t : T // p t ∈ U i} =>
        (⟨p t.1, t.2⟩ : {x : X // x ∈ U i})) :=
      (hp.comp continuous_subtype_val).subtype_mk _
    have h := (hLJoint i).comp (hBase.prodMk (hInverseCoordinates i))
    apply h.congr
    intro t
    change β (p t.1)
      (c i ⟨p t.1, t.2⟩ ((c i ⟨p t.1, t.2⟩).symm ⟨t.1, rfl⟩)) =
        β (p t.1) ⟨t.1, rfl⟩
    exact congrArg (β (p t.1)) ((c i ⟨p t.1, t.2⟩).apply_symm_apply _)

end LinearMap

namespace ContinuousLinearMap

/-- Normed finite-dimensional local coordinates with jointly continuous realizations
and continuous inverse coordinates turn injective algebraic fibre maps, continuous
in the parameter at each fixed coordinate vector, into a closed embedding. Its inverse
on the image extends to a jointly continuous fibrewise linear retraction on the whole
product. The equality-subtype fibres retain their given module structures and subspace
topologies; no completeness of the ambient space or separation of the base is required. -/
theorem exists_retraction_isClosedEmbedding_of_local_coordinates
    (K : Type uK) [RCLike K]
    (X : Type uX) [TopologicalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommGroup {t : T // p t = x}]
    [∀ x, Module K {t : T // p t = x}]
    (A : Type uA) [NormedAddCommGroup A] [InnerProductSpace K A]
    (I : Type uI) (G : I → Type uG)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (U : I → Set X)
    (β : ∀ x, {t : T // p t = x} →ₗ[K] A)
    (c : ∀ i (z : {x : X // x ∈ U i}), G i ≃ₗ[K] {t : T // p t = z.1})
    (hp : Continuous p)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hInj : ∀ x, Function.Injective (β x))
    (hRealization : ∀ i, Continuous (fun q : {x : X // x ∈ U i} × G i =>
      (c i q.1 q.2).val))
    (hInverseCoordinates : ∀ i, Continuous (fun t : {t : T // p t ∈ U i} =>
      ((⟨p t.1, t.2⟩ : {x : X // x ∈ U i}),
        (c i ⟨p t.1, t.2⟩).symm ⟨t.1, rfl⟩)))
    (hFrame : ∀ i (v : G i), Continuous (fun z : {x : X // x ∈ U i} =>
      β z.1 (c i z v))) :
    ∃ ρ : ∀ x, A →L[K] {t : T // p t = x},
      (∀ x (v : {t : T // p t = x}), ρ x (β x v) = v) ∧
      Continuous (fun q : X × A => (ρ q.1 q.2).val) ∧
      Topology.IsClosedEmbedding (fun t : T => (p t, β (p t) ⟨t, rfl⟩)) := by
  obtain ⟨ρ, P, hρ, _hOrth, hH, hP, hPCont, _hRest⟩ :=
    exists_retraction_of_inducing_local_finite_frames K X A
      (fun x => {t : T // p t = x}) T (fun _ v => v.val) I G U β c
      hOpen hCover hInj (fun _ => ⟨rfl⟩) hRealization hFrame
  let H : X × A → T := fun q => (ρ q.1 q.2).val
  let B : T → X × A := fun t => (p t, β (p t) ⟨t, rfl⟩)
  have hBetaCont : Continuous (fun t : T => β (p t) ⟨t, rfl⟩) :=
    LinearMap.continuous_total_of_local_coordinates K X T p A I G U β c hp hOpen hCover
      (fun i => continuous_snd.comp (hInverseCoordinates i)) hFrame
  have hBCont : Continuous B := hp.prodMk hBetaCont
  have hHB (t : T) : H (B t) = t :=
    congrArg (fun v : {s : T // p s = p t} => v.val) (hρ (p t) ⟨t, rfl⟩)
  have hIndex (x : X) (v : {t : T // p t = x}) :
      β (p v.val) ⟨v.val, rfl⟩ = β x v := by
    rcases v with ⟨t, ht⟩
    subst x
    rfl
  have hBH (q : X × A) : B (H q) = (q.1, P q.1 q.2) := by
    apply Prod.ext
    · exact (ρ q.1 q.2).property
    · exact (hIndex q.1 (ρ q.1 q.2)).trans (hP q.1 q.2).symm
  have hRange : Set.range B = {q : X × A | P q.1 q.2 = q.2} := by
    ext q
    constructor
    · rintro ⟨t, rfl⟩
      exact (congrArg Prod.snd (hBH (B t))).symm.trans
        (congrArg (fun s : T => (B s).2) (hHB t))
    · intro hq
      exact ⟨H q, (hBH q).trans (Prod.ext rfl hq)⟩
  have hClosed : IsClosed (Set.range B) := by
    rw [hRange]
    exact isClosed_eq ((hPCont.comp continuous_fst).clm_apply continuous_snd) continuous_snd
  have hEmbedding : Topology.IsEmbedding B :=
    Topology.IsEmbedding.of_leftInverse hHB hH hBCont
  exact ⟨ρ, hρ, hH, ⟨hEmbedding, hClosed⟩⟩

end ContinuousLinearMap
