/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric.Invariant
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Topology.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Averaging a nonconstant metric over a moving two-point base

The transposition acts on the discrete base `Fin 2` and leaves the real fibre coordinate
unchanged. The supplied continuous metric has coefficients `1, 2`, so it is not invariant.
Its normalized average has coefficient `3 / 2` at both basepoints. The output invariance is
an application of `ContinuousHermitianMetric.average_smul_invariant`.

The model and fibres retain their usual real structures. The input pairing is continuous on
the canonical same-base product of the trivial total spaces. For the averaging construction,
continuity into the canonical pullback norm-Hom topology follows from the discrete domain;
no comparison of Hom atlases, or topology on the permutation group, is needed.

## References

* Mathlib's permutation evaluation action, finite permutation cardinality, and canonical
  trivial-bundle and same-base-product constructions.
* The supplied-pairing and product-continuity construction in
  `VectorBundlesTest.Topology.VectorBundle.HermitianMetric.Operations`.
-/

@[expose] public section

open Bundle

namespace HermitianMetricMovingBaseExamples

local notation "B" => Fin 2
local notation "G" => Equiv.Perm (Fin 2)
local notation "T" => Bundle.Trivial (Fin 2) ℝ

local instance : TopologicalSpace B := ⊥
local instance : DiscreteTopology B := ⟨rfl⟩

-- Select the original trivial-bundle structures for the original total space.
attribute [local instance 2000] Bundle.Trivial.topologicalSpace Bundle.Trivial.fiberBundle
  Bundle.Trivial.vectorBundle

local instance : ContinuousConstSMul G B where
  continuous_const_smul _ := continuous_of_discreteTopology

local instance : MulAction G (TotalSpace ℝ T) where
  smul σ p := TotalSpace.mk' ℝ (σ p.proj) p.snd
  one_smul p := by cases p; rfl
  mul_smul σ τ p := by cases p; rfl

private def fibreEquiv (σ : G) (b : B) : T b ≃L[ℝ] T (σ • b) :=
  ContinuousLinearEquiv.refl ℝ ℝ

private def coefficient (b : B) : ℝ := if b = 0 then 1 else 2

private theorem coefficient_pos (b : B) : 0 < coefficient b := by
  unfold coefficient
  split <;> norm_num

private def pairing (b : B) : T b →ₗ⋆[ℝ] T b →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun w ↦ coefficient b * v * w
      map_add' := by intro w z; exact mul_add (coefficient b * v) w z
      map_smul' := by
        intro r w
        change coefficient b * v * (r * w) = r * (coefficient b * v * w)
        ring }
  map_add' := by
    intro v z
    apply LinearMap.ext
    intro w
    change coefficient b * (v + z) * w =
      coefficient b * v * w + coefficient b * z * w
    ring
  map_smul' := by
    intro r v
    apply LinearMap.ext
    intro w
    change coefficient b * (r * v) * w = r * (coefficient b * v * w)
    ring

private theorem pairing_apply (b : B) (v w : T b) :
    pairing b v w = coefficient b * v * w := rfl

private noncomputable def inputMetric : ContinuousHermitianMetric ℝ ℝ T :=
  ContinuousHermitianMetric.ofContinuousPairing pairing
    (by
      intro b v w
      change coefficient b * w * v = coefficient b * v * w
      ring)
    (by
      intro b v hv
      change 0 < coefficient b * v * v
      simpa only [pow_two, mul_assoc] using
        mul_pos (coefficient_pos b) (sq_pos_of_ne_zero hv))
    (by
      let _ : TopologicalSpace (TotalSpace (ℝ × ℝ) (T ×ᵇ T)) :=
        @FiberBundle.Prod.topologicalSpace B ℝ T ℝ T
          (Bundle.Trivial.topologicalSpace B ℝ) (Bundle.Trivial.topologicalSpace B ℝ)
      simp only [pairing_apply]
      have hd : Continuous (fun q : TotalSpace (ℝ × ℝ) (T ×ᵇ T) ↦
          (TotalSpace.mk' ℝ (E := T) q.proj q.snd.1,
            TotalSpace.mk' ℝ (E := T) q.proj q.snd.2)) :=
        (FiberBundle.Prod.isInducing_diag ℝ T ℝ T).continuous
      have hb : Continuous (fun q : TotalSpace (ℝ × ℝ) (T ×ᵇ T) ↦ q.proj) :=
        ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp hd.fst).fst
      have hv : Continuous (fun q : TotalSpace (ℝ × ℝ) (T ×ᵇ T) ↦ q.snd.1) :=
        ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp hd.fst).snd
      have hw : Continuous (fun q : TotalSpace (ℝ × ℝ) (T ×ᵇ T) ↦ q.snd.2) :=
        ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp hd.snd).snd
      have hc : Continuous coefficient := continuous_of_discreteTopology
      exact ((hc.comp hb).mul hv).mul hw)

private theorem inputMetric_inner_apply (b : B) (v w : T b) :
    inputMetric.inner b v w = coefficient b * v * w := by
  simp only [inputMetric, ContinuousHermitianMetric.ofContinuousPairing_inner_apply,
    pairing_apply]

/-- The moving action changes the supplied input from `1` to `2`, whereas its normalized
average has coefficient `3 / 2` everywhere and satisfies the public invariance law. -/
example :
    let N : ContinuousHermitianMetric ℝ ℝ T :=
      ContinuousHermitianMetric.average (fun σ : G ↦
        show ContinuousHermitianMetric ℝ ℝ T from
          (inputMetric.pullback
            (⟨fun b : B ↦ σ • b, continuous_of_discreteTopology⟩ : C(B, B))).comap
              (fun b ↦ (fibreEquiv σ b).toContinuousLinearMap)
              (fun b ↦ (fibreEquiv σ b).toHomeomorph.isEmbedding)
              (by
                let f_g : C(B, B) :=
                  ContinuousMap.mk (fun b : B ↦ σ • b)
                    (ContinuousConstSMul.continuous_const_smul σ)
                let P_g := (f_g : B → B) *ᵖ T
                exact @continuous_of_discreteTopology B _ _
                  (TotalSpace (ℝ →L[ℝ] ℝ) (fun b ↦ T b →L[ℝ] P_g b))
                  (@Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
                    ℝ _ ℝ _ (RingHom.id ℝ) B ℝ _ _ T _ _ _ ℝ _ _ P_g _ _ _
                    _ _ _ _ _ _ _
                    (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
                      (ContinuousLinearEquiv.toContinuousAddEquiv
                        (VectorBundle.continuousLinearEquivAt ℝ ℝ P_g b)))
                    (fun b ↦ ContinuousLinearEquiv.continuousSMul
                      (VectorBundle.continuousLinearEquivAt ℝ ℝ P_g b)) _)
                  (fun b ↦ TotalSpace.mk' (ℝ →L[ℝ] ℝ) b
                    ((fibreEquiv σ b).toContinuousLinearMap : T b →L[ℝ] P_g b))))
    ((Equiv.swap 0 1 : G) • (0 : B) = (1 : B)) ∧
    inputMetric.inner 0 1 1 = 1 ∧
    inputMetric.inner ((Equiv.swap 0 1 : G) • (0 : B))
      (fibreEquiv (Equiv.swap 0 1) 0 1) (fibreEquiv (Equiv.swap 0 1) 0 1) = 2 ∧
    (∀ (b : B) (v w : T b), N.inner b v w = (3 / 2 : ℝ) * v * w) ∧
    (∀ (h : G) (b : B) (v w : T b),
      N.inner (h • b) (fibreEquiv h b v) (fibreEquiv h b w) = N.inner b v w) := by
  classical
  have hcard : Nat.card G = 2 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hswap : (1 : G) ≠ Equiv.swap 0 1 := by
    intro h
    have hzero := congrArg (fun σ : G ↦ σ 0) h
    norm_num at hzero
  -- The stock cardinality formula gives all permutations without a separate enumeration proof.
  have hperms : (Finset.univ : Finset G) = {1, Equiv.swap 0 1} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hswap, Fintype.card_perm]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Equiv.Perm.smul_def]
  · norm_num [inputMetric_inner_apply, coefficient]
  · norm_num [inputMetric_inner_apply, coefficient, fibreEquiv, Equiv.Perm.smul_def]
  · intro b v w
    rw [ContinuousHermitianMetric.average_smul_inner_apply, hcard,
      finsum_eq_sum_of_fintype, hperms]
    fin_cases b <;>
      norm_num [hswap, inputMetric_inner_apply, coefficient, fibreEquiv,
        Equiv.Perm.smul_def] <;> ring
  · intro h b v w
    exact ContinuousHermitianMetric.average_smul_invariant
      (m := inputMetric) (A := fibreEquiv)
      (hNorm := by
        intro σ
        let f_g : C(B, B) :=
          ContinuousMap.mk (fun b : B ↦ σ • b)
            (ContinuousConstSMul.continuous_const_smul σ)
        let P_g := (f_g : B → B) *ᵖ T
        exact @continuous_of_discreteTopology B _ _
          (TotalSpace (ℝ →L[ℝ] ℝ) (fun b ↦ T b →L[ℝ] P_g b))
          (@Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
            ℝ _ ℝ _ (RingHom.id ℝ) B ℝ _ _ T _ _ _ ℝ _ _ P_g _ _ _
            _ _ _ _ _ _ _
            (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
              (ContinuousLinearEquiv.toContinuousAddEquiv
                (VectorBundle.continuousLinearEquivAt ℝ ℝ P_g b)))
            (fun b ↦ ContinuousLinearEquiv.continuousSMul
              (VectorBundle.continuousLinearEquivAt ℝ ℝ P_g b)) _)
          (fun b ↦ TotalSpace.mk' (ℝ →L[ℝ] ℝ) b
            ((fibreEquiv σ b).toContinuousLinearMap : T b →L[ℝ] P_g b)))
      (hA := fun _ _ _ ↦ rfl) h b v w

end HermitianMetricMovingBaseExamples
