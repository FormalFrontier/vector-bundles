/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
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

/-! ## Linear and continuous-linear given adjoint partners -/

namespace Function.IsAdjointPair

universe uK uH uA

section GivenPartner

variable {K : Type uK} [RCLike K]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace K H]
  {A : Type uA} [SeminormedAddCommGroup A] [InnerProductSpace K A]

private theorem inner_right_column_injective :
    Function.Injective (fun y : H => fun x : H => (innerSL K x).toLinearMap y) := by
  intro y z h
  exact ext_inner_left K (fun x => congrFun h x)

variable {Γ : H → A} {S : A → H}
  (h : Function.IsAdjointPair (inner K) (inner K) Γ S)

/-- Bundle a given inner-product adjoint partner as a linear map. Only the target
of the partner must be normed; the other space may be seminormed. -/
noncomputable def toLinearMap : A →ₗ[K] H :=
  h.toLinearMapOfInjective
    (B₁ := fun x : H => (innerSL K x).toLinearMap)
    (B₂ := fun x : A => (innerSL K x).toLinearMap)
    (by exact inner_right_column_injective (K := K))

@[simp]
theorem coe_toLinearMap : ⇑h.toLinearMap = S := rfl

@[simp]
theorem toLinearMap_apply (a : A) : h.toLinearMap a = S a := rfl

/-- The linear map represents the same adjoint partner. -/
theorem isAdjointPair_toLinearMap :
    Function.IsAdjointPair (inner K) (inner K) Γ h.toLinearMap := h

/-- An adjoint relation determines the bundled linear partner uniquely. -/
theorem toLinearMap_unique (L : A →ₗ[K] H)
    (hL : Function.IsAdjointPair (inner K) (inner K) Γ L) : h.toLinearMap = L :=
  h.toLinearMapOfInjective_unique
    (B₁ := fun x : H => (innerSL K x).toLinearMap)
    (B₂ := fun x : A => (innerSL K x).toLinearMap)
    (inner_right_column_injective (K := K)) L hL

/-- The linear partner does not depend on the proof of the adjoint relation. -/
theorem toLinearMap_eq (h' : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    h.toLinearMap = h'.toLinearMap := rfl

/-- A pointwise bound on the first map makes its given adjoint partner
continuous-linear, without a completeness or linearity hypothesis on the first map. -/
noncomputable def toContinuousLinearMapOfBound {C : NNReal}
    (hΓ : ∀ v, ‖Γ v‖ ≤ (C : ℝ) * ‖v‖) : A →L[K] H :=
  h.toLinearMap.mkContinuous (C : ℝ)
    (fun a => h.inner_symm.norm_apply_le_of_bound hΓ a)

variable {C : NNReal} (hΓ : ∀ v, ‖Γ v‖ ≤ (C : ℝ) * ‖v‖)

@[simp]
theorem coe_toContinuousLinearMapOfBound :
    ⇑(h.toContinuousLinearMapOfBound hΓ) = S := rfl

@[simp]
theorem toContinuousLinearMapOfBound_apply (a : A) :
    h.toContinuousLinearMapOfBound hΓ a = S a := rfl

@[simp]
theorem toContinuousLinearMapOfBound_toLinearMap :
    (h.toContinuousLinearMapOfBound hΓ).toLinearMap = h.toLinearMap := rfl

/-- The continuous-linear map represents the same adjoint partner. -/
theorem isAdjointPair_toContinuousLinearMapOfBound :
    Function.IsAdjointPair (inner K) (inner K) Γ
      (h.toContinuousLinearMapOfBound hΓ) := h

/-- The bound on the first map is a Lipschitz constant for the bundled partner. -/
theorem lipschitzWith_toContinuousLinearMapOfBound :
    LipschitzWith C (h.toContinuousLinearMapOfBound hΓ) := h.lipschitzWith_of_bound hΓ

/-- Any continuous-linear map with the adjoint relation equals the constructed partner. -/
theorem toContinuousLinearMapOfBound_unique (T : A →L[K] H)
    (hT : Function.IsAdjointPair (inner K) (inner K) Γ T) :
    h.toContinuousLinearMapOfBound hΓ = T := by
  have heq := h.toLinearMap_unique T.toLinearMap hT
  ext a
  exact congrArg (fun L : A →ₗ[K] H => L a) heq

/-- Changing the constant, bound proof, or compatibility proof does not change the map. -/
theorem toContinuousLinearMapOfBound_eq {D : NNReal}
    (h' : Function.IsAdjointPair (inner K) (inner K) Γ S)
    (hΓ' : ∀ v, ‖Γ v‖ ≤ (D : ℝ) * ‖v‖) :
    h.toContinuousLinearMapOfBound hΓ = h'.toContinuousLinearMapOfBound hΓ' := by
  ext a
  rfl

end GivenPartner

section ContinuousFirstMap

variable {K : Type uK} [RCLike K]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace K H]
  {A : Type uA} [SeminormedAddCommGroup A] [InnerProductSpace K A]
  {Γ : H →L[K] A} {S : A → H}
  (h : Function.IsAdjointPair (inner K) (inner K) Γ S)

/-- Bundle the given adjoint partner of a continuous-linear map, using its operator
norm as a bound. No completeness assumption on either space is needed. -/
noncomputable def toContinuousLinearMap : A →L[K] H :=
  h.toContinuousLinearMapOfBound (C := ‖Γ‖₊) (fun v => Γ.le_opNorm v)

@[simp]
theorem coe_toContinuousLinearMap : ⇑h.toContinuousLinearMap = S := rfl

@[simp]
theorem toContinuousLinearMap_apply (a : A) : h.toContinuousLinearMap a = S a := rfl

@[simp]
theorem toContinuousLinearMap_toLinearMap :
    h.toContinuousLinearMap.toLinearMap = h.toLinearMap := rfl

/-- The operator-norm construction preserves the adjoint relation. -/
theorem isAdjointPair_toContinuousLinearMap :
    Function.IsAdjointPair (inner K) (inner K) Γ h.toContinuousLinearMap := h

/-- The bundled partner has Lipschitz constant bounded by the first map's operator norm. -/
theorem lipschitzWith_toContinuousLinearMap : LipschitzWith ‖Γ‖₊ h.toContinuousLinearMap :=
  h.lipschitzWith_of_bound (fun v => Γ.le_opNorm v)

/-- The bundled continuous-linear partner is unique among maps with the same relation. -/
theorem toContinuousLinearMap_unique (T : A →L[K] H)
    (hT : Function.IsAdjointPair (inner K) (inner K) Γ T) : h.toContinuousLinearMap = T :=
  h.toContinuousLinearMapOfBound_unique (C := ‖Γ‖₊) (fun v => Γ.le_opNorm v) T hT

/-- The operator-norm construction is independent of the compatibility proof. -/
theorem toContinuousLinearMap_eq
    (h' : Function.IsAdjointPair (inner K) (inner K) Γ S) :
    h.toContinuousLinearMap = h'.toContinuousLinearMap := rfl

end ContinuousFirstMap

end Function.IsAdjointPair
