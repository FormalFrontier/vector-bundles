/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier
-/
module

public import Mathlib

/-!
# Joint continuity of star-semilinear precomposition

For a continuous linear map `f` and a continuous star-semilinear functional `λ`,
the map `(f, λ) ↦ λ.comp f` is jointly continuous. It is linear in the functional
and star-semilinear in the operator; over `ℂ`, it is conjugate-linear in the
operator, not complex-bilinear.
-/

@[expose] public section

universe u v w

namespace ContinuousLinearMap

variable {K : Type u} {E : Type v} {F : Type w} [RCLike K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- Star-semilinear functional precomposition is jointly continuous in the pair
`(f, λ)`, linear in `λ` and star-semilinear in `f`. -/
@[fun_prop]
theorem continuous_comp_star :
    Continuous (fun p : (E →L[K] F) × (F →SL[starRingEnd K] K) =>
      (p.2.comp p.1 : E →SL[starRingEnd K] K)) := by
  let B := ContinuousLinearMap.compSL E F K (RingHom.id K) (starRingEnd K)
  exact (B.flip.continuous.comp continuous_fst).clm_apply continuous_snd

end ContinuousLinearMap
