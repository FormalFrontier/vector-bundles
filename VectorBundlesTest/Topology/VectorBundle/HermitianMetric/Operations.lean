/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric.Operations
public import VectorBundles.Topology.VectorBundle.MetricModel
public import VectorBundles.Topology.VectorBundle.TrivialMetric
public import VectorBundles.Topology.VectorBundle.WeightedForm
public import VectorBundles.Topology.VectorBundle.MetricComap
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra

/-!
# Varying metrics on the original real and complex planes

For either `κ = ℝ` or `κ = ℂ`, the model `κ × κ` keeps its stock supremum norm.
A compatible model form is chosen by `Bundle.HermitianMetric.ofFiniteDimensional` and
extended constantly over the real line. Adding this metric to its positive rescaling
by `1 + t²` gives the pairing `(2 + t²)` times the chosen model pairing.
The real diagonal on `(1, 0)` increases strictly between `t = 0` and `t = 1`.

No inner-product structure on the stock plane norm is assumed, and no coordinate formula
for the chosen model form or equality with the stock norm is asserted. Constant vector
sections are continuous through the original trivial-bundle homeomorphism.

A separate finite-average example uses the original supremum norm on `Fin 2 → ℝ`.
It constructs the diagonal pairing with coefficients `1, 2` using
`ContinuousHermitianMetric.ofContinuousPairing`, then averages its comaps by the
permutation action. The resulting coefficients are `3 / 2, 3 / 2`.

## References

* The compatible model and constant-extension constructions in `MetricModel` and
  `TrivialMetric`.
* The canonical-chart identity in `WeightedForm` and Mathlib's trivial-bundle homeomorphism.
-/

open Bundle

namespace HermitianMetricOperationsExamples

universe uκ

-- Select the original trivial-bundle structures, not the fiberwise-product structures.
attribute [local instance 2000] Bundle.Trivial.topologicalSpace Bundle.Trivial.fiberBundle
  Bundle.Trivial.vectorBundle

private noncomputable def modelMetric (κ : Type uκ) [RCLike κ] :
    HermitianMetric κ (Bundle.Trivial Unit (κ × κ)) :=
  HermitianMetric.ofFiniteDimensional κ (κ × κ)

private noncomputable def constantMetric (κ : Type uκ) [RCLike κ] :
    ContinuousHermitianMetric κ (κ × κ) (Bundle.Trivial ℝ (κ × κ)) :=
  ContinuousHermitianMetric.trivialOfHermitianMetric κ ℝ (κ × κ) (modelMetric κ)

private def weight : C(ℝ, ℝ) :=
  ⟨fun t ↦ 1 + t ^ 2, continuous_const.add (continuous_id.pow 2)⟩

private theorem weight_pos (t : ℝ) : 0 < weight t := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg t)

/-- On the stock plane over the real line, add the constant compatible metric to its
rescaling by the continuous positive function `1 + t²`. -/
public noncomputable def planeMetric (κ : Type uκ) [RCLike κ] :
    ContinuousHermitianMetric κ (κ × κ) (Bundle.Trivial ℝ (κ × κ)) :=
  (constantMetric κ).add ((constantMetric κ).rescale weight weight_pos)

/-- The combined metric has coefficient `2 + t²` relative to the chosen model form. -/
public theorem planeMetric_inner_apply (κ : Type uκ) [RCLike κ] (t : ℝ) (v w : κ × κ) :
    (planeMetric κ).inner t v w =
      ((2 + t ^ 2 : ℝ) : κ) * (HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () v w := by
  simp only [planeMetric, ContinuousHermitianMetric.add_inner_apply,
    ContinuousHermitianMetric.rescale_inner_apply, constantMetric,
    ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply, modelMetric, weight,
    ContinuousMap.coe_mk, RCLike.ofReal_add, RCLike.ofReal_one, RCLike.ofReal_ofNat,
    add_mul, one_mul, two_mul, add_assoc]

/-- On the global trivial chart, the rescaled constant metric is the weighted model form.
This uses the chart identity without changing its topological-support continuity theorem. -/
theorem rescale_constant_inner_eq_weightedForm (κ : Type uκ) [RCLike κ] (t : ℝ) :
    ((constantMetric κ).rescale weight weight_pos).inner t =
      (Bundle.Trivial.trivialization ℝ (κ × κ)).weightedSesquilinearForm
        ((modelMetric κ).inner ()) (fun s ↦ (weight s : κ)) t := by
  rw [Bundle.Trivialization.weightedSesquilinearForm_trivialization]
  apply DFunLike.ext _ _
  intro v
  apply DFunLike.ext _ _
  intro w
  simp only [ContinuousHermitianMetric.rescale_inner_apply, constantMetric,
    ContinuousHermitianMetric.trivialOfHermitianMetric_inner_apply, smul_apply, smul_eq_mul]

/-- The first coordinate vector has strictly positive diagonal in the chosen model form. -/
theorem coordinate_pos (κ : Type uκ) [RCLike κ] :
    0 < RCLike.re ((HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () (1, 0) (1, 0)) := by
  exact (HermitianMetric.ofFiniteDimensional κ (κ × κ)).pos () (1, 0) (by simp)

/-- Every constant vector section is continuous for the original trivial total topology. -/
theorem continuous_constant_section (κ : Type uκ) [RCLike κ] (v : κ × κ) :
    Continuous (fun t : ℝ ↦ TotalSpace.mk' (κ × κ) (E := Bundle.Trivial ℝ (κ × κ)) t v) := by
  exact (Bundle.Trivial.homeomorphProd ℝ (κ × κ)).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

/-- Pairing any two constant vector sections is continuous, using metric evaluation. -/
theorem continuous_planeMetric_inner (κ : Type uκ) [RCLike κ] (v w : κ × κ) :
    Continuous (fun t : ℝ ↦ (planeMetric κ).inner t v w) :=
  (planeMetric κ).continuous_inner (continuous_constant_section κ v)
    (continuous_constant_section κ w)

/-- On a nonzero coordinate vector the real diagonal is `2Q` at zero and `3Q` at one,
where `Q` is strictly positive, so the metric genuinely varies. -/
public theorem planeMetric_coordinate_variation (κ : Type uκ) [RCLike κ] :
    let Q := RCLike.re ((HermitianMetric.ofFiniteDimensional κ (κ × κ)).inner () (1, 0) (1, 0))
    0 < Q ∧
      RCLike.re ((planeMetric κ).inner 0 (1, 0) (1, 0)) = 2 * Q ∧
      RCLike.re ((planeMetric κ).inner 1 (1, 0) (1, 0)) = 3 * Q ∧
      RCLike.re ((planeMetric κ).inner 0 (1, 0) (1, 0)) <
        RCLike.re ((planeMetric κ).inner 1 (1, 0) (1, 0)) := by
  dsimp only
  have h0 := congrArg (RCLike.re (K := κ))
    (planeMetric_inner_apply κ 0 (1, 0) (1, 0))
  have h1 := congrArg (RCLike.re (K := κ))
    (planeMetric_inner_apply κ 1 (1, 0) (1, 0))
  norm_num only [RCLike.re_ofReal_mul] at h0 h1
  refine ⟨coordinate_pos κ, h0, h1, ?_⟩
  rw [h0, h1]
  exact mul_lt_mul_of_pos_right (by norm_num) (coordinate_pos κ)

-- The same construction genuinely varies on the stock real plane.
example :
    RCLike.re ((planeMetric ℝ).inner 0 (1, 0) (1, 0)) <
      RCLike.re ((planeMetric ℝ).inner 1 (1, 0) (1, 0)) := by
  exact (planeMetric_coordinate_variation ℝ).2.2.2

-- The same construction genuinely varies on the stock complex plane.
example :
    RCLike.re ((planeMetric ℂ).inner 0 (1, 0) (1, 0)) <
      RCLike.re ((planeMetric ℂ).inner 1 (1, 0) (1, 0)) := by
  exact (planeMetric_coordinate_variation ℂ).2.2.2


section FiniteAverage

local notation "P" => (Fin 2 → ℝ)
local notation "T" => Bundle.Trivial ℝ P
local notation "S" => Equiv.Perm (Fin 2)

-- Restrict inverse precomposition to permutations, retaining the real scalar action.
local instance : MulAction S P := arrowAction

private def diagonalPairing : P →ₗ⋆[ℝ] P →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun w ↦ v 0 * w 0 + 2 * v 1 * w 1
      map_add' := by intro w z; simp [mul_add]; ring
      map_smul' := by intro r w; simp [smul_eq_mul]; ring }
  map_add' := by intro v z; ext w; simp [add_mul]; ring
  map_smul' := by intro r v; ext w; simp [smul_eq_mul]; ring

private theorem diagonalPairing_apply (v w : P) :
    diagonalPairing v w = v 0 * w 0 + 2 * v 1 * w 1 := rfl

private noncomputable def diagonalMetric : ContinuousHermitianMetric ℝ P T :=
  ContinuousHermitianMetric.ofContinuousPairing (fun _ ↦ diagonalPairing)
    (by
      intro b v w
      change w 0 * v 0 + 2 * w 1 * v 1 = v 0 * w 0 + 2 * v 1 * w 1
      ring)
    (by
      intro b v hv
      change 0 < v 0 * v 0 + 2 * v 1 * v 1
      have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra! h
        apply hv
        ext i
        fin_cases i
        · exact h.1
        · exact h.2
      rcases hn with h | h
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 1)]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0)])
    (by
      let _ : TopologicalSpace (TotalSpace (P × P) (T ×ᵇ T)) :=
        @FiberBundle.Prod.topologicalSpace ℝ P T P T
          (Bundle.Trivial.topologicalSpace ℝ P) (Bundle.Trivial.topologicalSpace ℝ P)
      simp only [diagonalPairing_apply]
      have hd : Continuous (fun q : TotalSpace (P × P) (T ×ᵇ T) ↦
          (TotalSpace.mk' P (E := T) q.proj q.snd.1,
            TotalSpace.mk' P (E := T) q.proj q.snd.2)) :=
        (FiberBundle.Prod.isInducing_diag P T P T).continuous
      have hv : Continuous (fun q : TotalSpace (P × P) (T ×ᵇ T) ↦ q.snd.1) :=
        ((Bundle.Trivial.homeomorphProd ℝ P).continuous.comp hd.fst).snd
      have hw : Continuous (fun q : TotalSpace (P × P) (T ×ᵇ T) ↦ q.snd.2) :=
        ((Bundle.Trivial.homeomorphProd ℝ P).continuous.comp hd.snd).snd
      exact (((continuous_apply 0).comp hv).mul ((continuous_apply 0).comp hw)).add
        ((continuous_const.mul ((continuous_apply 1).comp hv)).mul
          ((continuous_apply 1).comp hw)))

private theorem diagonalMetric_inner_apply (b : ℝ) (v w : P) :
    diagonalMetric.inner b v w = v 0 * w 0 + 2 * v 1 * w 1 := by
  simp only [diagonalMetric, ContinuousHermitianMetric.ofContinuousPairing_inner_apply,
    diagonalPairing_apply]

private theorem permutation_smul_apply (g : S) (v : P) (i : Fin 2) :
    (g • v) i = v (g.symm i) := rfl

-- These are the existing inverse-precomposition operators for the permutation action.
private theorem permutationOperator_apply (g : S) (v : P) :
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g v = g • v := by
  ext i
  change Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℝ) g v i = v (g.symm i)
  simp [Equiv.piCongrLeft_apply]

private theorem permutationOperator_embedding_continuous (g : S) :
    (∀ b : ℝ, Topology.IsEmbedding
      ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toContinuousLinearMap :
        T b →L[ℝ] T b)) ∧
    @Continuous _ _ _
      (Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) P T P T)
      (fun b : ℝ ↦ TotalSpace.mk' (P →L[ℝ] P)
        (E := fun b ↦ T b →L[ℝ] T b) b
        (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toContinuousLinearMap) := by
  refine ⟨?_, ?_⟩
  · intro b
    exact (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toHomeomorph.isEmbedding
  · let _ : TopologicalSpace
        (TotalSpace (P →L[ℝ] P) (fun b : ℝ ↦ T b →L[ℝ] T b)) :=
      Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) P T P T
    apply continuous_iff_continuousAt.2
    intro b
    refine (continuousAt_hom_bundle (σ := RingHom.id ℝ)
      (F₁ := P) (E₁ := T) (F₂ := P) (E₂ := T) _).2 ⟨continuousAt_id, ?_⟩
    convert (continuousAt_const : ContinuousAt (fun _ : ℝ ↦
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toContinuousLinearMap) b)
      using 1
    funext t
    rw [ContinuousLinearMap.inCoordinates_eq (by simp) (by simp)]
    simp

private noncomputable def permutedMetric (m : ContinuousHermitianMetric ℝ P T) (g : S) :
    ContinuousHermitianMetric ℝ P T :=
  m.comap
    (fun _ ↦ (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toContinuousLinearMap)
    (permutationOperator_embedding_continuous g).1
    (permutationOperator_embedding_continuous g).2

private theorem permutedMetric_inner_apply (m : ContinuousHermitianMetric ℝ P T)
    (g : S) (b : ℝ) (v w : P) :
    (permutedMetric m g).inner b v w = m.inner b (g • v) (g • w) := by
  calc
    (permutedMetric m g).inner b v w =
        m.inner b
          (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g v)
          (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g w) :=
      ContinuousHermitianMetric.comap_inner_apply m
        (fun _ ↦ (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 2 ↦ ℝ) g).toContinuousLinearMap)
        (permutationOperator_embedding_continuous g).1
        (permutationOperator_embedding_continuous g).2 b v w
    _ = m.inner b (g • v) (g • w) :=
      congrArg₂ (fun x y : P ↦ m.inner b x y)
        (permutationOperator_apply g v) (permutationOperator_apply g w)

private theorem permutations_fin_two : (Finset.univ : Finset S) = {1, Equiv.swap 0 1} := by
  classical
  ext e
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have hzero : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases hzero with hzero | hzero
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact hzero
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      change e 1 = 1
      rw [hzero] at hne
      omega
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using hzero
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      change e 1 = 0
      rw [hzero] at hne
      omega

/-- Averaging the orbit of the diagonal pairing `(1, 2)` on the original supremum-normed
plane gives `(3/2, 3/2)`. The input is not invariant; the output is invariant and averaging
its orbit again does not double its coefficient. Both metric averages are used via their API. -/
example :
    let a := ContinuousHermitianMetric.average (permutedMetric diagonalMetric)
    (∀ b v w, a.inner b v w = (3 / 2 : ℝ) * (v 0 * w 0 + v 1 * w 1)) ∧
    a.toHermitianMetric =
      HermitianMetric.average (fun g : S ↦ (permutedMetric diagonalMetric g).toHermitianMetric) ∧
    diagonalMetric.inner 0 (![1, 0] : P) (![1, 0] : P) ≠
      diagonalMetric.inner 0 ((Equiv.swap 0 1 : S) • (![1, 0] : P))
        ((Equiv.swap 0 1 : S) • (![1, 0] : P)) ∧
    (∀ b, a.inner b (![1, 0] : P) (![1, 0] : P) = 3 / 2 ∧
      a.inner b (![0, 1] : P) (![0, 1] : P) = 3 / 2 ∧ a.inner b (![1, 0] : P) (![0, 1] : P) = 0) ∧
    permutedMetric a (Equiv.swap 0 1) = a ∧
    (∀ b v w, (ContinuousHermitianMetric.average (permutedMetric a)).inner b v w =
      (3 / 2 : ℝ) * (v 0 * w 0 + v 1 * w 1)) := by
  classical
  dsimp only
  let a := ContinuousHermitianMetric.average (permutedMetric diagonalMetric)
  have hcard : Nat.card S = 2 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hswap : (1 : S) ≠ Equiv.swap 0 1 := by
    intro h
    have hzero := congrArg (fun g : S ↦ g 0) h
    norm_num at hzero
  have hformula (b : ℝ) (v w : P) :
      a.inner b v w = (3 / 2 : ℝ) * (v 0 * w 0 + v 1 * w 1) := by
    rw [ContinuousHermitianMetric.average_inner_apply, hcard, finsum_eq_sum_of_fintype,
      permutations_fin_two]
    simp [hswap, permutedMetric_inner_apply, one_smul]
    simp [diagonalMetric_inner_apply, permutation_smul_apply]; ring
  have hinvariant (g : S) : permutedMetric a g = a := by
    have hg : g = 1 ∨ g = Equiv.swap 0 1 := by
      have := Finset.mem_univ g
      rwa [permutations_fin_two, Finset.mem_insert, Finset.mem_singleton] at this
    apply ContinuousHermitianMetric.ext
    intro b v w
    rw [permutedMetric_inner_apply, hformula, hformula]
    rcases hg with rfl | rfl
    · simp
    · simp [permutation_smul_apply]; ring
  have hreaverage : ContinuousHermitianMetric.average (permutedMetric a) = a :=
    (ContinuousHermitianMetric.average_congr hinvariant).trans
      (ContinuousHermitianMetric.average_const a)
  refine ⟨hformula, ContinuousHermitianMetric.toHermitianMetric_average _, ?_, ?_,
    hinvariant _, ?_⟩
  · norm_num [diagonalMetric_inner_apply, permutation_smul_apply]
  · intro b
    refine ⟨?_, ?_, ?_⟩
    · simpa using hformula b (![1, 0] : P) (![1, 0] : P)
    · simpa using hformula b (![0, 1] : P) (![0, 1] : P)
    · simpa using hformula b (![1, 0] : P) (![0, 1] : P)
  · intro b v w
    rw [hreaverage, hformula]

end FiniteAverage

end HermitianMetricOperationsExamples
