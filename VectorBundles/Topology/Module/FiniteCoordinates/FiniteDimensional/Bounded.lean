/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Pointwise bounded sets of continuous linear maps

For a finite-dimensional seminormed domain over a nontrivially normed field, a set of
continuous linear maps is bounded in operator seminorm exactly when every fixed-vector
evaluation has bounded image. Neither the field nor the spaces need be complete, and the
spaces need not be separated.

## References

The reverse implication uses `FiniteDimensional.exists_finset_opNorm_le_sum` and
Mathlib’s norm-bound characterization of bounded sets. The forward implication uses
Mathlib’s bundled evaluation map `ContinuousLinearMap.apply`.
-/

@[expose] public section

open scoped BigOperators NNReal

universe uK uA uG

namespace ContinuousLinearMap

/-- A set of continuous linear maps from a finite-dimensional seminormed space is bounded
if and only if its image under evaluation at each vector is bounded. The scalar field may
be incomplete, and neither space is required to be complete or separated. -/
theorem isBounded_iff_forall_isBounded_image_apply
    {K : Type uK} [kK : NontriviallyNormedField K]
    {A : Type uA} [sA : SeminormedAddCommGroup A] [nA : NormedSpace K A]
    {G : Type uG} [sG : SeminormedAddCommGroup G] [nG : NormedSpace K G]
    [hA : FiniteDimensional K A] (s : Set (A →L[K] G)) :
    Bornology.IsBounded s ↔
      ∀ v : A, Bornology.IsBounded ((fun T : A →L[K] G => T v) '' s) := by
  classical
  constructor
  · intro hs v
    have heval : (ContinuousLinearMap.apply K G v : (A →L[K] G) → G) =
        (fun T => T v) := by
      funext T
      exact apply_apply v T
    simpa only [heval] using
      (Bornology.IsBounded.image (ContinuousLinearMap.apply K G v) hs)
  · intro h
    obtain ⟨t, C, hbound⟩ :=
      FiniteDimensional.exists_finset_opNorm_le_sum.{uK, uA, uG}
        K A (kK := kK) (sA := sA) (nA := nA) (hA := hA)
    let R : A → ℝ := fun v => Classical.choose ((h v).exists_norm_le)
    have hR (v : A) (T : A →L[K] G) (hT : T ∈ s) : ‖T v‖ ≤ R v :=
      Classical.choose_spec ((h v).exists_norm_le) (T v) ⟨T, hT, rfl⟩
    refine isBounded_iff_forall_norm_le.2 ⟨(C : ℝ) * ∑ v ∈ t, R v, ?_⟩
    intro T hT
    calc
      ‖T‖ ≤ (C : ℝ) * ∑ v ∈ t, ‖T v‖ := hbound G sG nG T
      _ ≤ (C : ℝ) * ∑ v ∈ t, R v :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun v _ => hR v T hT) C.coe_nonneg

end ContinuousLinearMap
