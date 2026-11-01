/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib
import VectorBundles.Analysis.InnerProductSpace.GramFamily

/-!
# Continuity of finite-rank projections

A self-adjoint idempotent with the same ambient image as an injective finite-dimensional
frame agrees with the frame's Gram projection. The comparison uses adjoint partners in
the complete auxiliary domain and does not require completeness of the ambient space.
Operator-norm continuity can then be checked using such frames on an arbitrary open cover.

## References

Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017), provides the
vector-bundle context. The criterion here is an analytic ingredient for a given family,
not a bundle-complement or projection-existence theorem.
-/

@[expose] public section

universe uX uK uA uI uE uM

namespace ContinuousLinearMap

variable {K : Type uK} {E : Type uE} {A : Type uA}
  [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace K A]

private theorem projection_eq_comp_of_adjoint_data
    (Γ : E →L[K] A) (g r : A →L[K] E) (B : E →L[K] E)
    (P : A →L[K] A)
    (hAdj : Function.IsAdjointPair (inner K) (inner K) Γ g)
    (hIdem : P.comp P = P)
    (hSymm : ∀ u v : A, inner K (P u) v = inner K u (P v))
    (hImage : ∀ a : A, (∃ v : E, Γ v = a) ↔ (∃ w : A, P w = a))
    (hLeft : r.comp Γ = ContinuousLinearMap.id K E)
    (hDef : r = B.comp g) :
    P = Γ.comp r := by
  have hFix (v : E) : P (Γ v) = Γ v := by
    obtain ⟨a, ha⟩ := (hImage (Γ v)).mp ⟨v, rfl⟩
    calc
      P (Γ v) = P (P a) := congrArg P ha.symm
      _ = P a := congrArg (fun T : A →L[K] A => T a) hIdem
      _ = Γ v := ha
  have hAdjP : Function.IsAdjointPair (inner K) (inner K) Γ (g.comp P) := by
    intro v w
    calc
      inner K (Γ v) w = inner K (P (Γ v)) w := by rw [hFix]
      _ = inner K (Γ v) (P w) := hSymm (Γ v) w
      _ = inner K v ((g.comp P) w) := hAdj.apply v (P w)
  have hgP : g.comp P = g := by
    ext a
    exact congrFun
      (((isAdjointPair_iff_eq_adjointMap Γ (g.comp P)).mp hAdjP).trans
        ((isAdjointPair_iff_eq_adjointMap Γ g).mp hAdj).symm) a
  have hrP (a : A) : r (P a) = r a := by
    rw [hDef]
    exact congrArg B (congrArg (fun T : A →L[K] E => T a) hgP)
  ext a
  obtain ⟨v, hv⟩ := (hImage (P a)).mpr ⟨a, rfl⟩
  have hrΓ : r (Γ v) = v :=
    congrArg (fun T : E →L[K] E => T v) hLeft
  have hQP : Γ (r (P a)) = P a := by
    calc
      Γ (r (P a)) = Γ (r (Γ v)) := congrArg (fun w : A => Γ (r w)) hv.symm
      _ = Γ v := congrArg Γ hrΓ
      _ = P a := hv
  calc
    P a = Γ (r (P a)) := hQP.symm
    _ = Γ (r a) := congrArg Γ (hrP a)

private theorem continuous_of_injective_frame
    {X : Type uX} [TopologicalSpace X] [FiniteDimensional K E]
    (Γ : X → E →L[K] A) (P : X → A →L[K] A)
    (hJoint : Continuous (fun p : X × E => Γ p.1 p.2))
    (hInj : ∀ x, Function.Injective (Γ x))
    (hIdem : ∀ x, (P x).comp (P x) = P x)
    (hSymm : ∀ (x : X) (a c : A), inner K (P x a) c = inner K a (P x c))
    (hImage : ∀ (x : X) (a : A),
      (∃ v : E, Γ x v = a) ↔ (∃ w : A, P x w = a)) :
    Continuous P := by
  obtain ⟨g, r, Q, hAdj, hR, hQ, _hgCont, _hrCont, hQCont, hLeft, _hProps⟩ :=
    exists_gramFamily Γ hJoint hInj
  have hCompare (x : X) : P x = (Γ x).comp (r x) :=
    projection_eq_comp_of_adjoint_data (Γ x) (g x) (r x)
      (Ring.inverse ((g x).comp (Γ x))) (P x)
      (hAdj x) (hIdem x) (hSymm x) (hImage x) (hLeft x) (hR x)
  exact hQCont.congr (fun x => (hQ x).trans (hCompare x).symm)

private theorem continuous_of_local_frames
    {X : Type uX} [TopologicalSpace X] {I : Type uI} {F : I → Type uE}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace K (F i)]
    [∀ i, CompleteSpace (F i)] [∀ i, FiniteDimensional K (F i)]
    (U : I → Set X) (P : X → A →L[K] A)
    (Γ : ∀ i, {x : X // x ∈ U i} → F i →L[K] A)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hJoint : ∀ i, Continuous (fun p : {x : X // x ∈ U i} × F i => Γ i p.1 p.2))
    (hInj : ∀ i z, Function.Injective (Γ i z))
    (hIdem : ∀ x, (P x).comp (P x) = P x)
    (hSymm : ∀ (x : X) (a c : A), inner K (P x a) c = inner K a (P x c))
    (hImage : ∀ (i : I) (z : {x : X // x ∈ U i}) (a : A),
      (∃ v : F i, Γ i z v = a) ↔ (∃ w : A, P z.1 w = a)) :
    Continuous P := by
  refine continuous_of_cover_nhds (s := U) ?_ ?_
  · intro x
    obtain ⟨i, hi⟩ := hCover x
    exact ⟨i, (hOpen i).mem_nhds hi⟩
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_of_injective_frame (Γ i) (fun z => P z.1)
      (hJoint i) (hInj i) (fun z => hIdem z.1) (fun z => hSymm z.1) (hImage i)

private theorem continuous_of_algebraic_local_frames
    {X : Type uX} [TopologicalSpace X] {I : Type uI} {M : I → Type uM}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (U : I → Set X) (P : X → A →L[K] A)
    (b : ∀ i, {x : X // x ∈ U i} → M i →ₗ[K] A)
    (n : I → ℕ) (e : ∀ i, EuclideanSpace K (Fin (n i)) ≃ₗ[K] M i)
    (Γ : ∀ i, {x : X // x ∈ U i} → EuclideanSpace K (Fin (n i)) →L[K] A)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ∀ x, ∃ i, x ∈ U i)
    (hJoint : ∀ i, Continuous
      (fun p : {x : X // x ∈ U i} × EuclideanSpace K (Fin (n i)) => Γ i p.1 p.2))
    (hΓ : ∀ i z v, Γ i z v = b i z (e i v))
    (hInj : ∀ i z, Function.Injective (b i z))
    (hIdem : ∀ x, (P x).comp (P x) = P x)
    (hSymm : ∀ (x : X) (a c : A), inner K (P x a) c = inner K a (P x c))
    (hImage : ∀ (i : I) (z : {x : X // x ∈ U i}) (a : A),
      (∃ v : M i, b i z v = a) ↔ (∃ w : A, P z.1 w = a)) :
    Continuous P := by
  apply continuous_of_local_frames U P Γ hOpen hCover hJoint ?_ hIdem hSymm ?_
  · intro i z v w h
    apply (e i).injective
    apply hInj i z
    exact ((hΓ i z v).symm.trans h).trans (hΓ i z w)
  · intro i z a
    constructor
    · rintro ⟨v, hv⟩
      exact (hImage i z a).mp ⟨e i v, (hΓ i z v).symm.trans hv⟩
    · intro h
      obtain ⟨m, hm⟩ := (hImage i z a).mpr h
      refine ⟨(e i).symm m, ?_⟩
      calc
        Γ i z ((e i).symm m) = b i z (e i ((e i).symm m)) := hΓ i z _
        _ = b i z m := congrArg (b i z) ((e i).apply_symm_apply m)
        _ = a := hm

/-- A finite-dimensional module admits an algebraic Euclidean model of its dimension. -/
theorem _root_.FiniteDimensional.nonempty_euclideanSpace_linearEquiv
    {M : Type uM} [AddCommGroup M] [Module K M] [FiniteDimensional K M] :
    Nonempty (EuclideanSpace K (Fin (Module.finrank K M)) ≃ₗ[K] M) := by
  classical
  have hfinrank :
      Module.finrank K (EuclideanSpace K (Fin (Module.finrank K M))) =
        Module.finrank K M := by
    simp
  exact FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.mpr hfinrank

/-- A family of self-adjoint idempotents is operator-norm continuous if its images admit
local injective finite-dimensional algebraic frames that are continuous in the parameter
at each fixed vector.

The algebraic frame domains may vary with the open set and may have dimension zero.
They carry no specified norm or topology, and the given ambient inner-product space need
not be complete. The conclusion concerns the supplied family, not a new projection. -/
theorem continuous_of_local_finite_frames
    {X : Type uX} [TopologicalSpace X] {I : Type uI} {M : I → Type uM}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    (U : I → Set X) (P : X → A →L[K] A)
    (b : ∀ i, {x : X // x ∈ U i} → M i →ₗ[K] A)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ∀ x, ∃ i, x ∈ U i)
    (hIdem : ∀ x, (P x).comp (P x) = P x)
    (hSymm : ∀ (x : X) (a c : A), inner K (P x a) c = inner K a (P x c))
    (hFixed : ∀ (i : I) (v : M i),
      Continuous (fun z : {x : X // x ∈ U i} => b i z v))
    (hInj : ∀ i z, Function.Injective (b i z))
    (hImage : ∀ (i : I) (z : {x : X // x ∈ U i}) (a : A),
      (∃ v : M i, b i z v = a) ↔ (∃ w : A, P z.1 w = a)) :
    Continuous P := by
  classical
  let n (i : I) : ℕ := Module.finrank K (M i)
  let e (i : I) : EuclideanSpace K (Fin (n i)) ≃ₗ[K] M i :=
    Classical.choice
      (FiniteDimensional.nonempty_euclideanSpace_linearEquiv (K := K) (M := M i))
  let Γ (i : I) (z : {x : X // x ∈ U i}) :
      EuclideanSpace K (Fin (n i)) →L[K] A :=
    ⟨(b i z).comp (e i).toLinearMap,
      ((b i z).comp (e i).toLinearMap).continuous_of_finiteDimensional⟩
  have hΓCont (i : I) : Continuous (Γ i) := by
    rw [continuous_clm_apply]
    intro v
    exact hFixed i (e i v)
  have hJoint (i : I) : Continuous
      (fun p : {x : X // x ∈ U i} × EuclideanSpace K (Fin (n i)) => Γ i p.1 p.2) :=
    ((hΓCont i).comp continuous_fst).clm_apply continuous_snd
  exact continuous_of_algebraic_local_frames U P b n e Γ hOpen hCover hJoint
    (fun _ _ _ => rfl) hInj hIdem hSymm hImage

end ContinuousLinearMap
