/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier
-/
module

public import VectorBundles.Analysis.Normed.Operator.Composition

/-!
# Anti-dual precomposition on finite product spaces

Canonical continuous star-semilinear functionals pull back along continuous
linear maps. Composition is jointly continuous, including zero-dimensional
endpoints, and precomposition by the zero map gives the zero functional. A rectangular
projection onto a diagonal exhibits a nonzero kernel. Multiplication of the
input map by `I` is conjugated, as witnessed by the canonical conjugation map.
-/

@[expose] public section

example (K : Type*) [RCLike K] (n m : ℕ) :
    Continuous (fun p :
      ((Fin n → K) →L[K] (Fin m → K)) ×
        ((Fin m → K) →SL[starRingEnd K] K) =>
      (p.2.comp p.1 : (Fin n → K) →SL[starRingEnd K] K)) := by
  fun_prop

section

variable (K : Type*) [RCLike K]

example (n m : ℕ) (lambda : (Fin m → K) →SL[starRingEnd K] K) :
    lambda.comp (0 : (Fin n → K) →L[K] (Fin m → K)) = 0 := by
  ext v
  change lambda 0 = 0
  exact map_zero lambda

example (m : ℕ) (f : (Fin 0 → K) →L[K] (Fin m → K))
    (lambda : (Fin m → K) →SL[starRingEnd K] K) :
    (lambda.comp f : (Fin 0 → K) →SL[starRingEnd K] K) = 0 := by
  ext v
  change lambda (f v) = 0
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero f, map_zero lambda]

example (n : ℕ) (f : (Fin n → K) →L[K] (Fin 0 → K))
    (lambda : (Fin 0 → K) →SL[starRingEnd K] K) :
    (lambda.comp f : (Fin n → K) →SL[starRingEnd K] K) = 0 := by
  ext v
  change lambda (f v) = 0
  have hf : f v = 0 := Subsingleton.elim _ _
  rw [hf, map_zero]

example :
    (fun (f : (Fin 2 → K) →L[K] (Fin 3 → K)) =>
      f ≠ 0 ∧
        ((fun k : Fin 2 => if k = 0 then (0 : K) else 1) ≠ 0 ∧
          f (fun k : Fin 2 => if k = 0 then (0 : K) else 1) = 0) ∧
        (∀ (lambda : (Fin 3 → K) →SL[starRingEnd K] K),
          (lambda.comp f) (fun k : Fin 2 => if k = 0 then (0 : K) else 1) = 0))
      (ContinuousLinearMap.pi (fun _ : Fin 3 =>
        (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → K) →L[K] K))) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have h0 := congrArg
      (fun t : (Fin 2 → K) →L[K] (Fin 3 → K) =>
        t (fun _ => 1) (0 : Fin 3)) h
    simp at h0
  · intro h
    have h1 := congrFun h (1 : Fin 2)
    simp at h1
  · ext j
    simp
  · intro lambda
    change lambda 0 = 0
    exact map_zero lambda

end

example :
    (fun (lambda : (Fin 1 → ℂ) →SL[starRingEnd ℂ] ℂ) =>
      (lambda.comp (Complex.I • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)))
          (fun _ : Fin 1 => 1) = -Complex.I ∧
      (lambda.comp (Complex.I • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)))
          (fun _ : Fin 1 => 1) ≠
        Complex.I * (lambda.comp (ContinuousLinearMap.id ℂ (Fin 1 → ℂ)))
          (fun _ : Fin 1 => 1))
      ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.comp
        (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ)) := by
  constructor
  · simp
  · intro h
    have hi := congrArg Complex.im h
    norm_num at hi
