/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Countability
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Second countability of the real plane bundle

The trivial real-line bundle over the real line is the real plane through
`Bundle.Trivial.homeomorphProd ℝ ℝ`. The first example obtains second countability of
its total space by applying `FiberBundle.secondCountableTopology`, then recovers second
countability of the model at the origin and of the base using stock embedding,
homeomorphism, and open-quotient APIs directly.

The empty-model bundle over the real line also applies the fiber-bundle instance directly.
It demonstrates that this forward transfer does not require a nonempty model. Both examples
retain Mathlib's original trivial-bundle topologies and `Bundle.Trivial.fiberBundle`.
-/

@[expose] public section

open Bundle

example :
    SecondCountableTopology (TotalSpace ℝ (Trivial ℝ ℝ)) ∧
      SecondCountableTopology ℝ ∧ SecondCountableTopology ℝ := by
  have htotal : SecondCountableTopology (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.secondCountableTopology ℝ (Trivial ℝ ℝ)
  let : SecondCountableTopology (TotalSpace ℝ (Trivial ℝ ℝ)) := htotal
  have hmodel : SecondCountableTopology ℝ := by
    let : SecondCountableTopology ((Trivial ℝ ℝ) (0 : ℝ)) :=
      (FiberBundle.totalSpaceMk_isEmbedding ℝ (Trivial ℝ ℝ) (0 : ℝ)).secondCountableTopology
    exact (FiberBundle.homeomorphAt ℝ (Trivial ℝ ℝ) (0 : ℝ)).symm.secondCountableTopology
  have hproj : IsOpenQuotientMap
      (TotalSpace.proj (F := ℝ) (E := Trivial ℝ ℝ)) :=
    ⟨FiberBundle.surjective_proj ℝ (Trivial ℝ ℝ),
      FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ),
      FiberBundle.isOpenMap_proj ℝ (Trivial ℝ ℝ)⟩
  have hbase : SecondCountableTopology ℝ := Topology.IsOpenQuotientMap.secondCountableTopology hproj
  exact ⟨htotal, hbase, hmodel⟩

example : SecondCountableTopology (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact FiberBundle.secondCountableTopology Empty (Trivial ℝ Empty)

section CountabilityCharacteristicClients

universe uCountabilityClientBase uCountabilityClientModel uCountabilityClientFiber

-- On the ordinary real trivial bundle, countability of the total plane reflects to both factors.
example :
    _root_.SecondCountableTopology _root_.Real ∧
      _root_.SecondCountableTopology _root_.Real := by
  have hTotal :
      _root_.SecondCountableTopology
        (_root_.Bundle.TotalSpace _root_.Real (_root_.Bundle.Trivial _root_.Real _root_.Real)) :=
    inferInstance
  rcases
      (_root_.FiberBundle.secondCountableTopology_totalSpace_iff
        _root_.Real (_root_.Bundle.Trivial _root_.Real _root_.Real)).mp hTotal with
    hBaseEmpty | hModelEmpty | hFactors
  · exact (hBaseEmpty.false (0 : _root_.Real)).elim
  · exact (hModelEmpty.false (0 : _root_.Real)).elim
  · exact hFactors

-- An empty base imposes no countability condition on the model.
example {B : Type uCountabilityClientBase} (F : Type uCountabilityClientModel)
    (E : B → Type uCountabilityClientFiber)
    [tB : _root_.TopologicalSpace B] [tF : _root_.TopologicalSpace F]
    [tTotal : _root_.TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [tE : ∀ b, _root_.TopologicalSpace (E b)] [fb : _root_.FiberBundle F E]
    [hBaseEmpty : _root_.IsEmpty B] :
    _root_.SecondCountableTopology (_root_.Bundle.TotalSpace F E) := by
  exact (_root_.FiberBundle.secondCountableTopology_totalSpace_iff F E).mpr
    (_root_.Or.inl hBaseEmpty)

-- An empty model imposes no countability condition on the base.
example {B : Type uCountabilityClientBase} (F : Type uCountabilityClientModel)
    (E : B → Type uCountabilityClientFiber)
    [tB : _root_.TopologicalSpace B] [tF : _root_.TopologicalSpace F]
    [tTotal : _root_.TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [tE : ∀ b, _root_.TopologicalSpace (E b)] [fb : _root_.FiberBundle F E]
    [hModelEmpty : _root_.IsEmpty F] :
    _root_.SecondCountableTopology (_root_.Bundle.TotalSpace F E) := by
  exact (_root_.FiberBundle.secondCountableTopology_totalSpace_iff F E).mpr
    (_root_.Or.inr (_root_.Or.inl hModelEmpty))

end CountabilityCharacteristicClients
