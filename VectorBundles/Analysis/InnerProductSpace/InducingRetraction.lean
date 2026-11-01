/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.GramFamily
public import VectorBundles.Analysis.InnerProductSpace.ProjectionContinuity

/-!
# Retractions from inducing realizations and local finite frames

The algebraic fibre modules retain their given topologies; no norms or continuity
of their algebraic operations are required.
If their realization maps induce their given topologies, jointly continuous local
realizations and parameter-continuous injective finite frames yield continuous linear
retractions. The associated orthogonal projections vary continuously in operator norm.
The ambient inner-product space need not be complete, and the finite-dimensional
seminormed local models may have varying or zero dimension.
-/

@[expose] public section

universe uK uX uA uF uT uI uG

namespace ContinuousLinearMap

/-- Injective algebraic fibre maps with inducing realizations, jointly continuous
local realizations, and local finite frames continuous in the parameter at each fixed
vector admit continuous linear orthogonal retractions on the original fibres.
Their realizations are jointly continuous, and their ambient projections are
operator-norm continuous, self-adjoint idempotents with precisely the prescribed image.
Orthogonality characterizes both the normalized value and its kernel. -/
theorem exists_retraction_of_inducing_local_finite_frames
    (K : Type uK) [RCLike K]
    (X : Type uX) [TopologicalSpace X]
    (A : Type uA) [NormedAddCommGroup A] [InnerProductSpace K A]
    (F : X → Type uF)
    [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)]
    [∀ x, TopologicalSpace (F x)]
    (T : Type uT) [TopologicalSpace T]
    (j : ∀ x, F x → T)
    (I : Type uI) (G : I → Type uG)
    [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (U : I → Set X)
    (β : ∀ x, F x →ₗ[K] A)
    (c : ∀ i (z : {x : X // x ∈ U i}), G i ≃ₗ[K] F z.1)
    (hOpen : ∀ i, IsOpen (U i))
    (hCover : ∀ x, ∃ i, x ∈ U i)
    (hInj : ∀ x, Function.Injective (β x))
    (hInducing : ∀ x, Topology.IsInducing (j x))
    (hRealization : ∀ i, Continuous (fun p : {x : X // x ∈ U i} × G i =>
      j p.1.1 (c i p.1 p.2)))
    (hFrame : ∀ i (v : G i), Continuous (fun z : {x : X // x ∈ U i} =>
      β z.1 (c i z v))) :
    ∃ (ρ : ∀ x, A →L[K] F x) (P : X → (A →L[K] A)),
      (∀ x (v : F x), ρ x (β x v) = v) ∧
      (∀ x (a : A) (v : F x), inner K (β x v) (a - β x (ρ x a)) = 0) ∧
      Continuous (fun p : X × A => j p.1 (ρ p.1 p.2)) ∧
      (∀ x (a : A), P x a = β x (ρ x a)) ∧
      Continuous P ∧
      (∀ x, (P x).comp (P x) = P x) ∧
      (∀ x (a d : A), inner K (P x a) d = inner K a (P x d)) ∧
      (∀ x (a : A), (∃ v : F x, β x v = a) ↔ (∃ w : A, P x w = a)) ∧
      (∀ x (a : A) (w : F x),
        (∀ v : F x, inner K (β x v) (a - β x w) = 0) ↔ w = ρ x a) ∧
      (∀ x (a : A), ρ x a = 0 ↔ ∀ v : F x, inner K (β x v) a = 0) := by
  classical
  let E (i : I) := EuclideanSpace K (Fin (Module.finrank K (G i)))
  let e (i : I) : E i ≃ₗ[K] G i :=
    Classical.choice (FiniteDimensional.nonempty_euclideanSpace_linearEquiv (K := K) (M := G i))
  let d (i : I) (z : {x : X // x ∈ U i}) : E i ≃ₗ[K] F z.1 :=
    (e i).trans (c i z)
  let Γ (i : I) (z : {x : X // x ∈ U i}) : E i →L[K] A :=
    ⟨(β z.1).comp (d i z).toLinearMap,
      ((β z.1).comp (d i z).toLinearMap).continuous_of_finiteDimensional⟩
  have hΓCont (i : I) : Continuous (Γ i) := by
    rw [continuous_clm_apply]
    intro v
    exact hFrame i (e i v)
  have hΓJoint (i : I) : Continuous
      (fun p : {x : X // x ∈ U i} × E i => Γ i p.1 p.2) :=
    ((hΓCont i).comp continuous_fst).clm_apply continuous_snd
  have hΓInj (i : I) (z : {x : X // x ∈ U i}) : Function.Injective (Γ i z) :=
    (hInj z.1).comp (d i z).injective
  have hLocal (i : I) :
      ∃ (r : {x : X // x ∈ U i} → A →L[K] E i)
        (Q : {x : X // x ∈ U i} → A →L[K] A),
        Continuous r ∧
        (∀ z, Q z = (Γ i z).comp (r z)) ∧
        (∀ z, (r z).comp (Γ i z) = ContinuousLinearMap.id K (E i)) ∧
        (∀ z, (Q z).comp (Q z) = Q z) ∧
        (∀ z (a b : A), inner K (Q z a) b = inner K a (Q z b)) ∧
        (∀ z (v : E i) (a : A), inner K (Γ i z v) (a - Q z a) = 0) := by
    obtain ⟨g, r, Q, _hAdj, _hR, hQ, _hg, hr, _hQCont, hLeft, hProps⟩ :=
      exists_gramFamily (Γ i) (hΓJoint i) (hΓInj i)
    exact ⟨r, Q, hr, hQ, hLeft, fun z => (hProps z).1,
      fun z => (hProps z).2.2.1, fun z => (hProps z).2.2.2.2⟩
  choose r Q hr hQ hLeft hIdem hSymm hOrth using hLocal
  let q (i : I) (z : {x : X // x ∈ U i}) : A →ₗ[K] F z.1 :=
    (d i z).toLinearMap.comp (r i z).toLinearMap
  have hqLeft (i : I) (z : {x : X // x ∈ U i}) (v : F z.1) :
      q i z (β z.1 v) = v := by
    have h := congrArg (fun f : E i →L[K] E i => f ((d i z).symm v)) (hLeft i z)
    have hh := congrArg (d i z) h
    simpa [q, Γ] using hh
  have hQβ (i : I) (z : {x : X // x ∈ U i}) (a : A) :
      Q i z a = β z.1 (q i z a) :=
    congrArg (fun f : A →L[K] A => f a) (hQ i z)
  let k (x : X) : I := (hCover x).choose
  let z (x : X) : {y : X // y ∈ U (k x)} := ⟨x, (hCover x).choose_spec⟩
  let ρ₀ (x : X) : A →ₗ[K] F x := q (k x) (z x)
  let P (x : X) : A →L[K] A := Q (k x) (z x)
  have hρLeft (x : X) (v : F x) : ρ₀ x (β x v) = v := hqLeft (k x) (z x) v
  have hPβ (x : X) (a : A) : P x a = β x (ρ₀ x a) := hQβ (k x) (z x) a
  have hρOrth (x : X) (a : A) (v : F x) :
      inner K (β x v) (a - β x (ρ₀ x a)) = 0 := by
    rw [← hPβ]
    simpa [Γ] using hOrth (k x) (z x) ((d (k x) (z x)).symm v) a
  have hPIdem (x : X) : (P x).comp (P x) = P x := hIdem (k x) (z x)
  have hPSymm (x : X) (a b : A) : inner K (P x a) b = inner K a (P x b) :=
    hSymm (k x) (z x) a b
  have hImage (x : X) (a : A) :
      (∃ v : F x, β x v = a) ↔ (∃ w : A, P x w = a) := by
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨β x v, by rw [hPβ, hρLeft]⟩
    · rintro ⟨w, hw⟩
      exact ⟨ρ₀ x w, (hPβ x w).symm.trans hw⟩
  have hPCont : Continuous P := by
    apply continuous_of_local_finite_frames U P
      (fun i z => (β z.1).comp (c i z).toLinearMap)
      hOpen hCover hPIdem hPSymm hFrame
    · intro i z
      exact (hInj z.1).comp (c i z).injective
    · intro i z a
      rw [← hImage]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨c i z v, hv⟩
      · rintro ⟨v, hv⟩
        exact ⟨(c i z).symm v, by simpa using hv⟩
  have hqP (i : I) (z : {x : X // x ∈ U i}) (a : A) :
      q i z (P z.1 a) = ρ₀ z.1 a := by
    rw [hPβ]
    exact hqLeft i z (ρ₀ z.1 a)
  have heCont (i : I) : Continuous (e i) :=
    (e i).toLinearMap.continuous_of_finiteDimensional
  have hJointLocal (i : I) : Continuous
      (fun p : {x : X // x ∈ U i} × A => j p.1.1 (ρ₀ p.1.1 p.2)) := by
    have hPApply : Continuous
        (fun p : {x : X // x ∈ U i} × A => P p.1.1 p.2) :=
      (hPCont.comp (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd
    have hCoord : Continuous (fun p : {x : X // x ∈ U i} × A =>
        e i (r i p.1 (P p.1.1 p.2))) :=
      (heCont i).comp (((hr i).comp continuous_fst).clm_apply hPApply)
    have h := (hRealization i).comp (continuous_fst.prodMk hCoord)
    apply h.congr
    intro p
    exact congrArg (j p.1.1) (hqP i p.1 p.2)
  have hJoint : Continuous (fun p : X × A => j p.1 (ρ₀ p.1 p.2)) := by
    let V (i : I) : Set (X × A) := {p | p.1 ∈ U i}
    refine continuous_of_cover_nhds (s := V) ?_ ?_
    · intro p
      obtain ⟨i, hi⟩ := hCover p.1
      exact ⟨i, ((hOpen i).preimage continuous_fst).mem_nhds hi⟩
    · intro i
      apply continuousOn_iff_continuous_domRestrict.mpr
      have hf : Continuous (fun p : {p : X × A // p ∈ V i} =>
          (⟨p.1.1, p.2⟩ : {x : X // x ∈ U i})) :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.2)
      exact (hJointLocal i).comp (hf.prodMk (continuous_snd.comp continuous_subtype_val))
  have hρCont (x : X) : Continuous (ρ₀ x) := by
    apply (hInducing x).continuous_iff.mpr
    exact hJoint.comp (continuous_const.prodMk continuous_id)
  have hNormalize (x : X) (a : A) (w : F x) :
      (∀ v : F x, inner K (β x v) (a - β x w) = 0) ↔ w = ρ₀ x a := by
    constructor
    · intro hw
      apply hInj x
      have hd : inner K (β x (w - ρ₀ x a)) (β x (w - ρ₀ x a)) = 0 := by
        have h₁ := hw (w - ρ₀ x a)
        have h₂ := hρOrth x a (w - ρ₀ x a)
        rw [inner_sub_right] at h₁ h₂
        calc
          inner K (β x (w - ρ₀ x a)) (β x (w - ρ₀ x a)) =
              inner K (β x (w - ρ₀ x a)) (β x w - β x (ρ₀ x a)) :=
            congrArg (inner K (β x (w - ρ₀ x a))) ((β x).map_sub _ _)
          _ = 0 := by
            rw [inner_sub_right]
            exact sub_eq_zero.mpr ((sub_eq_zero.mp h₁).symm.trans (sub_eq_zero.mp h₂))
      have hz := inner_self_eq_zero.mp hd
      simpa only [map_sub, sub_eq_zero] using hz
    · intro hw
      subst w
      exact hρOrth x a
  let ρ (x : X) : A →L[K] F x := ⟨ρ₀ x, hρCont x⟩
  refine ⟨ρ, P, hρLeft, hρOrth, hJoint, hPβ, hPCont, hPIdem, hPSymm, hImage,
    hNormalize, ?_⟩
  intro x a
  change ρ₀ x a = 0 ↔ ∀ v : F x, inner K (β x v) a = 0
  constructor
  · intro ha v
    have h := hρOrth x a v
    simpa only [ha, map_zero, sub_zero] using h
  · intro ha
    exact ((hNormalize x a 0).mp (by simpa only [map_zero, sub_zero] using ha)).symm

end ContinuousLinearMap
