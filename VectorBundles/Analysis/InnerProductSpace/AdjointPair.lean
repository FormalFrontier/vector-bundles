/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.LinearAlgebra.Pairing.Adjoint
public import VectorBundles.Topology.MetricSpace.PairwiseDistance

/-!
# Norms and continuity of given adjoint partners

The pairings are the given conjugate-first inner products. Given adjoint partners have
equal operator norms, and distances between two given pairs agree. Consequently, families
of given partners are continuous simultaneously on any topological parameter space.

The spaces need only be seminormed, and partners are not asserted to be unique. The norm
proof uses Mathlib's isometric inner-product functional `innerSL` and the operator-norm
bound for composition.
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

/-- A function value is bounded in norm by a given continuous linear adjoint partner. -/
theorem norm_apply_le {f : E → F} {S : F →L[K] E}
    (h : Function.IsAdjointPair (inner K) (inner K) f S) (x : E) :
    ‖f x‖ ≤ ‖S‖ * ‖x‖ := by
  have heq : innerSL K (f x) = (innerSL K x).comp S := by
    ext y
    exact h.apply x y
  calc
    ‖f x‖ = ‖innerSL K (f x)‖ := by rw [innerSL_apply_norm]
    _ = ‖(innerSL K x).comp S‖ := congrArg norm heq
    _ ≤ ‖innerSL K x‖ * ‖S‖ := (innerSL K x).opNorm_comp_le S
    _ = ‖S‖ * ‖x‖ := by rw [innerSL_apply_norm, mul_comm]

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
