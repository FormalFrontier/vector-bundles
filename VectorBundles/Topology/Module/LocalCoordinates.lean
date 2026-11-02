/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Module.JointEvaluation

/-!
# Total-space continuity of semilinear maps from finite local bases

Semilinear maps over a ring homomorphism `σ : R →+* S` from the equality-subtype
fibres of a continuous map are continuous on the total space when finite local bases
have scalar coordinates continuous after applying `σ`, their exact inverse vector
coordinates are continuous, and their basis-vector images vary continuously over an
open cover. No topology on `R` or continuity of `σ` is required. Only the target module
needs continuous addition and `S`-scalar multiplication; no continuity of the model
operations is assumed.

The equality-subtype fibres retain their given module structures and subspace
topologies. The finite basis types may vary over an arbitrary open cover, without a
uniform rank bound. No injectivity of the fibre maps or continuity of forward
coordinate realizations is required.

Over a complete nontrivially normed field, finite-dimensional Hausdorff topological
coordinate models supply such bases and continuous scalar coordinates. This gives
`LinearMap.continuous_total_of_local_coordinates` with fixed-vector frame continuity,
without changing the given model topologies.

## References

The evaluation step reuses `Module.Basis.continuous_uncurry_iff_semilinear` from
`VectorBundles.Analysis.Normed.Module.JointEvaluation`. The finite-dimensional
specialization uses Mathlib's `Module.Basis.continuous_coe_repr` and follows the
finite-dimensional evaluation API developed by Sébastien Gouëzel.
-/

@[expose] public section

universe uR uS uX uT uA uI uG uJ
universe uK

namespace LinearMap

/-- Semilinear fibre maps are continuous on the total space when supplied finite
local bases have scalar coordinates continuous after applying the scalar homomorphism,
inverse local vector coordinates are continuous, and the images of the local basis
vectors vary continuously. No topology on the source semiring or continuity of the
scalar homomorphism is required; only the target needs continuous addition and
scalar multiplication. -/
theorem continuous_total_of_local_coordinates_of_basis_semilinear
    (R : Type uR) [Semiring R]
    (S : Type uS) [Semiring S] [TopologicalSpace S]
    (σ : R →+* S)
    (X : Type uX) [TopologicalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommMonoid {t : T // p t = x}]
    [∀ x, Module R {t : T // p t = x}]
    (A : Type uA) [AddCommMonoid A] [Module S A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul S A]
    (I : Type uI) (G : I → Type uG)
    [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i, TopologicalSpace (G i)]
    (J : I → Type uJ) [∀ i, Finite (J i)]
    (b : ∀ i, Module.Basis (J i) R (G i))
    (hcoord : ∀ i (j : J i),
      Continuous (fun v : G i => σ ((b i).repr v j)))
    (U : I → Set X)
    (β : ∀ x, {t : T // p t = x} →ₛₗ[σ] A)
    (c : ∀ i (z : {x : X // x ∈ U i}),
      G i ≃ₗ[R] {t : T // p t = z.1})
    (hp : Continuous p)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hInverseCoordinates : ∀ i,
      Continuous (fun t : {t : T // p t ∈ U i} =>
        (c i ⟨p t.1, t.2⟩).symm ⟨t.1, rfl⟩))
    (hFrame : ∀ i (j : J i),
      Continuous (fun z : {x : X // x ∈ U i} =>
        β z.1 (c i z (b i j)))) :
    Continuous (fun t : T => β (p t) ⟨t, rfl⟩) := by
  let L (i : I) (z : {x : X // x ∈ U i}) : G i →ₛₗ[σ] A :=
    (β z.1).comp (c i z).toLinearMap
  have hLJoint (i : I) : Continuous
      (fun q : {x : X // x ∈ U i} × G i => L i q.1 q.2) :=
    ((b i).continuous_uncurry_iff_semilinear (hcoord i) (L := L i)).2 (hFrame i)
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

/-- Algebraic fibre maps are continuous on the total space when supplied finite
local bases have continuous scalar coordinates, inverse local vector coordinates
are continuous, and the images of the local basis vectors vary continuously.
Only the target needs continuous addition and scalar multiplication. -/
theorem continuous_total_of_local_coordinates_of_basis
    (R : Type uR) [Semiring R] [TopologicalSpace R]
    (X : Type uX) [TopologicalSpace X]
    (T : Type uT) [TopologicalSpace T]
    (p : T → X)
    [∀ x, AddCommMonoid {t : T // p t = x}]
    [∀ x, Module R {t : T // p t = x}]
    (A : Type uA) [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul R A]
    (I : Type uI) (G : I → Type uG)
    [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i, TopologicalSpace (G i)]
    (J : I → Type uJ) [∀ i, Finite (J i)]
    (b : ∀ i, Module.Basis (J i) R (G i))
    (hcoord : ∀ i (j : J i),
      Continuous (fun v : G i => (b i).repr v j))
    (U : I → Set X)
    (β : ∀ x, {t : T // p t = x} →ₗ[R] A)
    (c : ∀ i (z : {x : X // x ∈ U i}),
      G i ≃ₗ[R] {t : T // p t = z.1})
    (hp : Continuous p)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hInverseCoordinates : ∀ i,
      Continuous (fun t : {t : T // p t ∈ U i} =>
        (c i ⟨p t.1, t.2⟩).symm ⟨t.1, rfl⟩))
    (hFrame : ∀ i (j : J i),
      Continuous (fun z : {x : X // x ∈ U i} =>
        β z.1 (c i z (b i j)))) :
    Continuous (fun t : T => β (p t) ⟨t, rfl⟩) := by
  exact continuous_total_of_local_coordinates_of_basis_semilinear R R (RingHom.id R)
    X T p A I G J b hcoord U β c hp hOpen hCover hInverseCoordinates hFrame

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
  exact continuous_total_of_local_coordinates_of_basis K X T p A I G
    (fun i => Fin (Module.finrank K (G i))) (fun i => Module.finBasis K (G i))
    (fun i j => (continuous_apply j).comp (Module.finBasis K (G i)).continuous_coe_repr)
    U β c hp hOpen hCover hInverseCoordinates
    (fun i j => hFrame i (Module.finBasis K (G i) j))

end LinearMap
