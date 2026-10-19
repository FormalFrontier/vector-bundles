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
