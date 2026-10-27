/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import VectorBundles.Topology.VectorBundle.EqualBase
public import VectorBundles.Topology.VectorBundle.FiniteRank.Discrete
public import Mathlib.Analysis.RCLike.Basic

/-!
# Equal-base sum interface tests

The private proposition below displays a compact-base complement statement type.
It is a type experiment, not a proof of the existence statement.
The continuity example uses the standard fibre topologies and final total-space
topologies of two discrete families with opposite ranks.
-/

@[expose] public section

open Bundle

universe uK uX uP uE uEta uInputIndex uEtaIndex

namespace Bundle

namespace FiniteRankAtlas

/-- Records the intended theorem type, not an additional public predicate. -/
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
final total-space topologies. -/
theorem continuous_oppositeRank_mk (K : Type uK) [Field K] [TopologicalSpace K]
    (x : TwoPoint) :
    Continuous (fun p : Fiber K twoPointRank x × Fiber K reverseTwoPointRank x =>
      EqualBaseSum.mk (P := Unit) (E := Fiber K twoPointRank)
        (Q := Unit) (H := Fiber K reverseTwoPointRank) x p.1 p.2) := by
  apply (EqualBaseSum.continuous_iff _).2
  exact ⟨(continuous_mk K twoPointRank x).comp continuous_fst,
    (continuous_mk K reverseTwoPointRank x).comp continuous_snd⟩

end Bundle.DiscreteFiniteRank
