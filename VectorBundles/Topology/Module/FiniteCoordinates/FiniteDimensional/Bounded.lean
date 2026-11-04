/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
public import VectorBundles.Analysis.Normed.Operator.Basic
public import VectorBundles.Topology.Bornology.LinearMap
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Pointwise bounded sets of continuous semilinear maps

For a finite-dimensional seminormed domain, a set of continuous semilinear maps is
bounded in operator seminorm exactly when every fixed-vector evaluation has bounded
image. The scalar homomorphism need only be isometric; its target field need only be
normed. Neither the fields nor the spaces need be complete, and the spaces need not
be separated.

The proof uses the finite-dimensional equivalence with pointwise convergence,
von Neumann boundedness, and its reflection along the inducing evaluation map.
-/

@[expose] public section

universe uK uL uA uG

namespace ContinuousLinearMap

/-- A set of continuous semilinear maps from a finite-dimensional seminormed space is
bounded if and only if its image under evaluation at each vector is bounded. The scalar
homomorphism is isometric but need not be surjective. Neither field nor either space
is required to be complete, and the spaces need not be separated. -/
theorem isBounded_iff_forall_isBounded_image_applyₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [hL : NormedField L]
    {A : Type uA} [sA : SeminormedAddCommGroup A] [nA : NormedSpace K A]
    {G : Type uG} [sG : SeminormedAddCommGroup G] [nG : NormedSpace L G]
    {σ : K →+* L} [RingHomIsometric σ]
    [hA : FiniteDimensional K A] (s : Set (A →SL[σ] G)) :
    Bornology.IsBounded s ↔
      ∀ v : A, Bornology.IsBounded ((fun T : A →SL[σ] G => T v) '' s) :=
  letI : NontriviallyNormedField L :=
    { toNormedField := hL
      non_trivial := by
        obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
        refine ⟨σ x, ?_⟩
        simpa only [RingHomIsometric.norm_map] using hx }
  by
    let 𝔖 : Set (Set A) := {t | t.Finite}
    have hbounded : ∀ t ∈ 𝔖, Bornology.IsBounded t :=
      fun t ht => ht.isBounded
    have hspan : Submodule.span K (⋃₀ 𝔖) = ⊤ := by
      have hcover : ⋃₀ 𝔖 = Set.univ := by
        apply Set.eq_univ_of_forall
        intro v
        exact Set.mem_sUnion.2 ⟨{v}, Set.finite_singleton v, by simp⟩
      rw [hcover, Submodule.span_univ]
    let e : (A →SL[σ] G) ≃L[L] PointwiseConvergenceCLM σ A G :=
      ContinuousLinearEquiv.toUniformConvergenceCLMOfFiniteDimensional
        K L σ A G 𝔖 hbounded hspan
    have heval (T : A →SL[σ] G) (v : A) : e T v = T v :=
      ContinuousLinearEquiv.toUniformConvergenceCLMOfFiniteDimensional_apply
        𝔖 hbounded hspan T v
    let J : PointwiseConvergenceCLM σ A G →L[L] (A → G) :=
      ContinuousLinearMap.pi
        (fun v : A => PointwiseConvergenceCLM.evalCLM σ G v)
    let j : PointwiseConvergenceCLM σ A G →ₗ[L] (A → G) := J.toLinearMap
    have hj_apply (T : PointwiseConvergenceCLM σ A G) (v : A) : j T v = T v := by
      change (ContinuousLinearMap.pi
        (fun v : A => PointwiseConvergenceCLM.evalCLM σ G v)) T v = T v
      simpa only [ContinuousLinearMap.pi_apply] using
        (show PointwiseConvergenceCLM.evalCLM σ G v T = T v from rfl)
    have hj : Topology.IsInducing
        (j : PointwiseConvergenceCLM σ A G → (A → G)) := by
      have hcoe : (j : PointwiseConvergenceCLM σ A G → (A → G)) =
          (fun T : PointwiseConvergenceCLM σ A G => (T : A → G)) := by
        funext T v
        exact hj_apply T v
      rw [hcoe]
      exact (PointwiseConvergenceCLM.isEmbedding_coeFn σ A G).isInducing
    have himage (v : A) :
        Function.eval v '' (j '' (e '' s)) =
          (fun T : A →SL[σ] G => T v) '' s := by
      simp only [Set.image_image, Function.eval, hj_apply, heval]
    have hpi :
        Bornology.IsVonNBounded L (j '' (e '' s)) ↔
          ∀ v : A, Bornology.IsVonNBounded L
            ((fun T : A →SL[σ] G => T v) '' s) := by
      simpa only [himage] using
        (Bornology.isVonNBounded_pi_iff (𝕜 := L) (S := j '' (e '' s)))
    constructor
    · intro hs v
      have hs' : Bornology.IsVonNBounded L s :=
        NormedSpace.isVonNBounded_of_isBounded L hs
      have he : Bornology.IsVonNBounded L (e '' s) :=
        hs'.image e.toContinuousLinearMap
      have hj' : Bornology.IsVonNBounded L (j '' (e '' s)) :=
        he.image J
      exact (NormedSpace.isVonNBounded_iff L
        (s := (fun T : A →SL[σ] G => T v) '' s)).1 ((hpi.1 hj') v)
    · intro hs
      have hj' : Bornology.IsVonNBounded L (j '' (e '' s)) := by
        apply hpi.2
        intro v
        exact NormedSpace.isVonNBounded_of_isBounded L (hs v)
      have he : Bornology.IsVonNBounded L (e '' s) := by
        apply Bornology.IsVonNBounded.of_image_of_isInducing (f := j) <;> assumption
      have hs' : Bornology.IsVonNBounded L s := by
        have hpre : Bornology.IsVonNBounded L (e.symm '' (e '' s)) :=
          he.image e.symm.toContinuousLinearMap
        simpa only [ContinuousLinearEquiv.symm_image_image] using hpre
      exact (NormedSpace.isVonNBounded_iff L (s := s)).1 hs'

/-- A set of continuous linear maps from a finite-dimensional seminormed space is bounded
if and only if its image under evaluation at each vector is bounded. The scalar field may
be incomplete, and neither space is required to be complete or separated. -/
theorem isBounded_iff_forall_isBounded_image_apply
    {K : Type uK} [kK : NontriviallyNormedField K]
    {A : Type uA} [sA : SeminormedAddCommGroup A] [nA : NormedSpace K A]
    {G : Type uG} [sG : SeminormedAddCommGroup G] [nG : NormedSpace K G]
    [hA : FiniteDimensional K A] (s : Set (A →L[K] G)) :
    Bornology.IsBounded s ↔
      ∀ v : A, Bornology.IsBounded ((fun T : A →L[K] G => T v) '' s) :=
  isBounded_iff_forall_isBounded_image_applyₛₗ
    (K := K) (L := K) (σ := RingHom.id K) s

end ContinuousLinearMap
