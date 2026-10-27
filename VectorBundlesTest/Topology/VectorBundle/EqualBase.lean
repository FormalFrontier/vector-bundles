/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import VectorBundles.Topology.VectorBundle.EqualBase
public import VectorBundles.Topology.VectorBundle.FiniteRank.Discrete
public import VectorBundles.Topology.Algebra.GroupWithZero
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Equal-base sum interface tests

The private proposition below displays a compact-base complement statement type.
It is a type experiment, not a proof of the existence statement.
The continuity example uses the standard fibre topologies and final total-space
topologies of two discrete families with opposite ranks.
-/

@[expose] public section

open Bundle

universe uK uX uP uE uEta uInputIndex uEtaIndex uI

namespace Bundle

namespace FiniteRankAtlas

/-- Records the intended theorem type, not an additional public predicate.

The compact Hausdorff hypotheses specify the class of bases in this statement,
even though forming the proposition does not depend on their property instances.
-/
@[nolint unusedArguments]
private def compactFiniteRankComplementType
    (K : Type uK) [RCLike K]
    (X : Type uX) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (P : Type uP) (E : X → Type uE)
    [∀ x, AddCommGroup (E x)] [∀ x, Module K (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace P E)] : Prop :=
  Nonempty (FiniteRankAtlas.{uK, uX, uE, uP, uInputIndex} K P E) →
    ∃ (N : ℕ) (η : X → Type (max uK uEta))
      (ηAdd : ∀ x, AddCommGroup (η x))
      (ηModule : ∀ x, @Module K (η x) inferInstance (ηAdd x).toAddCommMonoid)
      (ηFiberTopology : ∀ x, TopologicalSpace (η x))
      (ηTotalTopology : TopologicalSpace (TotalSpace (Fin N → K) η)),
      Nonempty
        (@FiniteRankAtlas.{uK, uX, max uK uEta, uK, uEtaIndex}
          K inferInstance inferInstance X inferInstance
          (Fin N → K) η ηAdd ηModule ηFiberTopology ηTotalTopology) ∧
      Nonempty
        (@EqualBaseTrivialization K inferInstance inferInstance X inferInstance
          P E (Fin N → K) η
          inferInstance inferInstance
          (fun x => (ηAdd x).toAddCommMonoid) ηModule
          inferInstance ηTotalTopology N)

set_option pp.universes true in
#check @Bundle.FiniteRankAtlas

set_option pp.universes true in
#print compactFiniteRankComplementType

end FiniteRankAtlas
end Bundle

namespace Bundle.DiscreteFiniteRank

/-- The two-point rank family with rank one on the left and rank zero on the right. -/
def reverseTwoPointRank : TwoPoint → ℕ
  | .left => 1
  | .right => 0

/-- Pairing vectors in opposite-rank discrete fibres is continuous for the given
final total-space topologies.

The field assumption retains the uniform field/vector-space model scope of this
example; the pairing-continuity argument itself uses only the given topologies.
-/
@[nolint unusedArguments]
theorem continuous_oppositeRank_mk (K : Type uK) [Field K] [TopologicalSpace K]
    (x : TwoPoint) :
    Continuous (fun p : Fiber K twoPointRank x × Fiber K reverseTwoPointRank x =>
      EqualBaseSum.mk (P := Unit) (E := Fiber K twoPointRank)
        (Q := Unit) (H := Fiber K reverseTwoPointRank) x p.1 p.2) := by
  apply (EqualBaseSum.continuous_iff _).2
  exact ⟨(continuous_mk K twoPointRank x).comp continuous_fst,
    (continuous_mk K reverseTwoPointRank x).comp continuous_snd⟩

end Bundle.DiscreteFiniteRank

/-!
## Scalar normalization for finite-weight gluing

The propositions below describe reciprocals of finite sums of real squares, with
bundled weights or continuity hypotheses on a specified finite set of indices.
The original finite-type statement is a specialization of
`continuous_inv_finset_sum_sq`.
-/

section ScalarNormalization

open scoped BigOperators

/-- Reciprocal squared-weight continuity under pointwise nonvanishing. -/
private def continuousInvSumSquares : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] (I : Type uI) [Fintype I]
    (w : I → C(X, ℝ)),
    (∀ x : X, ∃ i : I, w i x ≠ 0) →
      Continuous (fun x : X => (∑ i : I, (w i x) ^ 2)⁻¹)

set_option pp.universes true in
#print continuousInvSumSquares

private theorem continuousInvSumSquares_holds : continuousInvSumSquares.{uX, uI} := by
  intro X _ I _ w h
  refine continuous_inv_finset_sum_sq Finset.univ (fun i x => w i x)
    (fun i _hi => (w i).continuous) ?_
  intro x
  obtain ⟨i, hi⟩ := h x
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- Reciprocal squared-weight continuity for a specified finite set of indices. -/
private def continuousInvFinsetSumSquares : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] (I : Type uI) (s : Finset I)
    (w : I → C(X, ℝ)),
    (∀ x : X, ∃ i ∈ s, w i x ≠ 0) →
      Continuous (fun x : X => (s.sum (fun i => (w i x) ^ 2))⁻¹)

set_option pp.universes true in
#print continuousInvFinsetSumSquares

end ScalarNormalization

private def continuousInvFinsetSumSquaresOfContinuous : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] (I : Type uI)
    (s : Finset I) (w : I → X → ℝ),
    (∀ i ∈ s, Continuous (w i)) →
    (∀ x, ∃ i ∈ s, w i x ≠ 0) →
    Continuous (fun x => (Finset.sum s (fun i => (w i x) ^ 2))⁻¹)

set_option pp.universes true in
#print continuousInvFinsetSumSquaresOfContinuous
