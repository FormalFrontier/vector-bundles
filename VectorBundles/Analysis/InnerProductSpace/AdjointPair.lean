/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.LinearAlgebra.Pairing.Adjoint
public import VectorBundles.Topology.MetricSpace.PairwiseDistance

/-!
# Norms and continuity of given adjoint partners

The pairings are the given conjugate-first inner products. A pointwise norm bound on a
function makes any given adjoint partner Lipschitz with the same constant. In particular,
a given adjoint partner of a continuous linear map is Lipschitz with its operator norm,
and hence continuous, without any linearity or continuity assumption on the partner.

Bundled adjoint partners have equal operator norms, and distances between two given pairs
agree. Consequently, families of bundled partners are continuous simultaneously on any
topological parameter space.

The spaces need only be seminormed, and partners are not asserted to be unique. The norm
bound uses Mathlib's isometric inner-product functional `innerSL` and Cauchy–Schwarz.
A zero Lipschitz constant gives zero pairwise pseudometric distances, not necessarily
equality of values.
-/

@[expose] public section

universe u v w z

namespace Function.IsAdjointPair

variable {K : Type u} {E : Type v} {F : Type w}
  [RCLike K] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [InnerProductSpace K E] [InnerProductSpace K F]

/-- Adjointness for the given inner products is symmetric. -/
theorem inner_symm {f : E → F} {g : F → E}
    (h : Function.IsAdjointPair (inner K) (inner K) f g) :
    Function.IsAdjointPair (inner K) (inner K) g f := by
  intro x y
  rw [← inner_conj_symm (g x) y, ← h.apply y x, inner_conj_symm]

/-- Subtracting two adjoint pairs of functions gives another adjoint pair. -/
theorem inner_sub {f₁ f₂ : E → F} {g₁ g₂ : F → E}
    (h₁ : Function.IsAdjointPair (inner K) (inner K) f₁ g₁)
    (h₂ : Function.IsAdjointPair (inner K) (inner K) f₂ g₂) :
    Function.IsAdjointPair (inner K) (inner K) (f₁ - f₂) (g₁ - g₂) := by
  intro x y
  change inner K (f₁ x - f₂ x) y = inner K x (g₁ y - g₂ y)
  rw [inner_sub_left, inner_sub_right, h₁.apply, h₂.apply]

/-- A function value is bounded in norm by a pointwise norm bound
on a given adjoint partner. -/
theorem norm_apply_le_of_bound {f : E → F} {g : F → E} {C : NNReal}
    (h : Function.IsAdjointPair (inner K) (inner K) f g)
    (hg : ∀ y, ‖g y‖ ≤ (C : ℝ) * ‖y‖) (x : E) :
    ‖f x‖ ≤ (C : ℝ) * ‖x‖ := by
  calc
    ‖f x‖ = ‖innerSL K (f x)‖ := by rw [innerSL_apply_norm]
    _ ≤ (C : ℝ) * ‖x‖ := by
      apply (innerSL K (f x)).opNorm_le_bound
        (mul_nonneg C.coe_nonneg (norm_nonneg x))
      intro y
      calc
        ‖(innerSL K (f x)) y‖ = ‖inner K x (g y)‖ := congrArg norm (h.apply x y)
        _ ≤ ‖x‖ * ‖g y‖ := norm_inner_le_norm x (g y)
        _ ≤ ‖x‖ * ((C : ℝ) * ‖y‖) :=
          mul_le_mul_of_nonneg_left (hg y) (norm_nonneg x)
        _ = ((C : ℝ) * ‖x‖) * ‖y‖ := by
          rw [← mul_assoc, mul_comm ‖x‖ (C : ℝ)]

/-- A function value is bounded in norm by a given continuous linear adjoint partner. -/
theorem norm_apply_le {f : E → F} {S : F →L[K] E}
    (h : Function.IsAdjointPair (inner K) (inner K) f S) (x : E) :
    ‖f x‖ ≤ ‖S‖ * ‖x‖ := by
  simpa only [coe_nnnorm] using
    h.norm_apply_le_of_bound (C := ‖S‖₊)
      (fun y => by simpa only [coe_nnnorm] using S.le_opNorm y) x

/-- A given adjoint partner of a pointwise norm-bounded function
is Lipschitz with the same bound. -/
theorem lipschitzWith_of_bound {Γ : E → F} {S : F → E} {C : NNReal}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ : ∀ v, ‖Γ v‖ ≤ (C : ℝ) * ‖v‖) :
    LipschitzWith C S := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  -- Translation and subtraction use only the full pairing identity, not linearity of S.
  have hab : Function.IsAdjointPair (inner K) (inner K) Γ
      (fun y => S (y + b) - S b) := by
    intro v y
    rw [inner_sub_right, ← h.apply v (y + b), ← h.apply v b,
      ← inner_sub_right, add_sub_cancel_right]
  simpa only [dist_eq_norm, sub_add_cancel] using
    hab.inner_symm.norm_apply_le_of_bound hΓ (a - b)

/-- A given adjoint partner of a continuous linear map is Lipschitz
with the operator-norm constant. -/
theorem lipschitzWith {Γ : E →L[K] F} {S : F → E}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    LipschitzWith ‖Γ‖₊ S :=
  h.lipschitzWith_of_bound (fun v => by simpa only [coe_nnnorm] using Γ.le_opNorm v)

/-- A given adjoint partner of a continuous linear map is continuous. -/
theorem continuous {Γ : E →L[K] F} {S : F → E}
    (h : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    Continuous S :=
  h.lipschitzWith.continuous

/-- An operator is bounded in norm by any given adjoint partner. -/
theorem norm_le {T : E →L[K] F} {S : F →L[K] E}
    (h : Function.IsAdjointPair (inner K) (inner K) T S) : ‖T‖ ≤ ‖S‖ :=
  T.opNorm_le_bound (norm_nonneg S) h.norm_apply_le

/-- Given adjoint partners have the same operator norm, even in seminormed spaces. -/
theorem norm_eq {T : E →L[K] F} {S : F →L[K] E}
    (h : Function.IsAdjointPair (inner K) (inner K) T S) : ‖T‖ = ‖S‖ :=
  le_antisymm h.norm_le h.inner_symm.norm_le

/-- Differences of two given adjoint pairs have the same operator norm. -/
theorem norm_sub_eq {T₁ T₂ : E →L[K] F} {S₁ S₂ : F →L[K] E}
    (h₁ : Function.IsAdjointPair (inner K) (inner K) T₁ S₁)
    (h₂ : Function.IsAdjointPair (inner K) (inner K) T₂ S₂) :
    ‖T₁ - T₂‖ = ‖S₁ - S₂‖ :=
  norm_eq (T := T₁ - T₂) (S := S₁ - S₂) (h₁.inner_sub h₂)

/-- Passing between two given adjoint pairs preserves operator-norm distance. -/
theorem dist_eq {T₁ T₂ : E →L[K] F} {S₁ S₂ : F →L[K] E}
    (h₁ : Function.IsAdjointPair (inner K) (inner K) T₁ S₁)
    (h₂ : Function.IsAdjointPair (inner K) (inner K) T₂ S₂) :
    dist T₁ T₂ = dist S₁ S₂ := by
  simpa only [dist_eq_norm] using h₁.norm_sub_eq h₂

/-- Families of given adjoint partners are continuous simultaneously on any
topological parameter space, in the operator-norm topologies. -/
theorem continuous_iff {X : Type z} [TopologicalSpace X]
    {f : X → (E →L[K] F)} {g : X → (F →L[K] E)}
    (h : ∀ x, Function.IsAdjointPair (inner K) (inner K) (f x) (g x)) :
    Continuous f ↔ Continuous g :=
  Metric.continuous_iff_of_pairwise_dist_eq fun x y => (h x).dist_eq (h y)

end Function.IsAdjointPair

namespace ContinuousLinearMap

variable (K : Type u) (E : Type v) (F : Type w)
  [RCLike K] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [InnerProductSpace K E] [InnerProductSpace K F]

/-- The assertion of operator-norm equality for two given adjoint partners. -/
def AdjointPairNormEquality : Prop :=
  ∀ (T : E →L[K] F) (S : F →L[K] E),
    Function.IsAdjointPair (inner K) (inner K) T S → ‖T‖ = ‖S‖

/-- The assertion of norm-distance equality for families of given adjoint partners. -/
def AdjointPairNormSubEquality (X : Type z) : Prop :=
  ∀ (f : X → (E →L[K] F)) (g : X → (F →L[K] E)),
    (∀ x, Function.IsAdjointPair (inner K) (inner K) (f x) (g x)) →
      ∀ x y, ‖g x - g y‖ = ‖f x - f y‖

/-- The assertion of equivalent operator-norm continuity for families of given adjoint partners. -/
def AdjointPairContinuity (X : Type z) [TopologicalSpace X] : Prop :=
  ∀ (f : X → (E →L[K] F)) (g : X → (F →L[K] E)),
    (∀ x, Function.IsAdjointPair (inner K) (inner K) (f x) (g x)) →
      (Continuous f ↔ Continuous g)

/-- Every pair of given adjoint partners satisfies operator-norm equality. -/
theorem adjointPairNormEquality : AdjointPairNormEquality K E F := by
  intro T S h
  exact h.norm_eq

/-- Families of given adjoint partners satisfy the norm-difference assertion. -/
theorem adjointPairNormSubEquality (X : Type z) : AdjointPairNormSubEquality K E F X := by
  intro f g h x y
  exact ((h x).norm_sub_eq (h y)).symm

/-- Families of given adjoint partners satisfy the continuity assertion. -/
theorem adjointPairContinuity (X : Type z) [TopologicalSpace X] :
    AdjointPairContinuity K E F X := by
  intro f g h
  exact Function.IsAdjointPair.continuous_iff h

end ContinuousLinearMap

/-- Multiplication by `I` and by `-I` are adjoint for the given complex inner product. -/
theorem Complex.isAdjointPair_I_smul_id :
    Function.IsAdjointPair (inner ℂ) (inner ℂ)
      (Complex.I • ContinuousLinearMap.id ℂ ℂ)
      (-Complex.I • ContinuousLinearMap.id ℂ ℂ) := by
  intro x y
  simp
  ring
