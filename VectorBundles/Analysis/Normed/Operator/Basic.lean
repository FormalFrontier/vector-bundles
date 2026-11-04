/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator seminorms over a normed target field

An isometric homomorphism from a nontrivially normed field makes its target
nontrivially normed without changing the given normed field structure. This gives
continuous semilinear maps their operator seminormed group even when the target
field is only assumed to be normed.

The group agrees with `ContinuousLinearMap.toSeminormedAddCommGroup` when the
target field is already nontrivially normed.
-/

@[expose] public section

universe uK uL uA uG

namespace ContinuousLinearMap

variable {K : Type uK} {L : Type uL}

private theorem exists_one_lt_norm_of_isometric
    [NontriviallyNormedField K] [hL : NormedField L]
    (σ : K →+* L) [RingHomIsometric σ] : ∃ x : L, 1 < ‖x‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  refine ⟨σ x, ?_⟩
  simpa only [RingHomIsometric.norm_map] using hx

section NormedField

variable [NontriviallyNormedField K] [hL : NormedField L]
    {A : Type uA} {G : Type uG}
    [SeminormedAddCommGroup A] [SeminormedAddCommGroup G]
    [NormedSpace K A] [NormedSpace L G]
    {σ : K →+* L} [RingHomIsometric σ]

/-- Continuous semilinear maps form a seminormed additive group for the operator norm
when the source field is nontrivially normed and the scalar homomorphism is isometric.
The given target field structure, space norms and scalar actions are unchanged. -/
@[instance_reducible]
noncomputable instance (priority := 100) toSeminormedAddCommGroupOfNormedField :
    SeminormedAddCommGroup (A →SL[σ] G) :=
  letI : NontriviallyNormedField L :=
    { toNormedField := hL
      non_trivial := by
        exact exists_one_lt_norm_of_isometric (hL := hL) σ }
  ContinuousLinearMap.toSeminormedAddCommGroup
    (𝕜 := K) (𝕜₂ := L) (E := A) (F := G) (σ₁₂ := σ)

/-- The operator seminorm is bounded by a nonnegative constant exactly when that
constant bounds every evaluation relative to the input seminorm. -/
theorem opNorm_le_iff_ofNormedField {f : A →SL[σ] G} {M : ℝ} (hM : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x : A, ‖f x‖ ≤ M * ‖x‖ :=
  letI : NontriviallyNormedField L :=
    { toNormedField := hL
      non_trivial := by
        exact exists_one_lt_norm_of_isometric (hL := hL) σ }
  ContinuousLinearMap.opNorm_le_iff (f := f) (σ₁₂ := σ) hM

/-- The operator seminorm bounds every evaluation of a continuous semilinear map. -/
theorem le_opNorm_ofNormedField (f : A →SL[σ] G) (x : A) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  (opNorm_le_iff_ofNormedField (f := f) (M := ‖f‖) (norm_nonneg f)).mp le_rfl x

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField K] [strongL : NontriviallyNormedField L]
    {A : Type uA} {G : Type uG}
    [SeminormedAddCommGroup A] [SeminormedAddCommGroup G]
    [NormedSpace K A] [NormedSpace L G]
    {σ : K →+* L} [RingHomIsometric σ]

/-- For a nontrivially normed target field, the operator seminormed group obtained
from its normed field structure agrees with the usual operator seminormed group. -/
theorem toSeminormedAddCommGroupOfNormedField_eq :
    toSeminormedAddCommGroupOfNormedField
      (K := K) (L := L) (A := A) (G := G) (σ := σ)
      (hL := strongL.toNormedField) =
    ContinuousLinearMap.toSeminormedAddCommGroup
      (𝕜 := K) (𝕜₂ := L) (E := A) (F := G) (σ₁₂ := σ) := rfl

end NontriviallyNormedField

end ContinuousLinearMap
