/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import VectorBundles.Topology.FiberBundle.Lindelof.Proper
public import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Order
import Mathlib.Topology.WithTopology

/-!
# Lindelöf total spaces of compact-model trivial bundles

These applications retain the standard topology on the noncompact real base and
all canonical trivial-bundle fiber and total-space topologies. The first model is
the indiscrete two-point space, compact by finiteness rather than discreteness.
The empty model is also finite and compact, and needs no nonemptiness hypothesis.
The real base is Lindelöf through its standard second-countable topology.
-/

@[expose] public section

namespace Bundle.Trivial

/-- The trivial bundle over the real line with the indiscrete two-point model has
Lindelöf total space, with its canonical bundle topology. -/
theorem real_indiscretePair_lindelofSpace_totalSpace :
    LindelofSpace
      (Bundle.TotalSpace (WithTopology (Fin 2) ⊤)
        (Bundle.Trivial ℝ (WithTopology (Fin 2) ⊤))) :=
  FiberBundle.lindelofSpace_totalSpace (B := ℝ) (WithTopology (Fin 2) ⊤)
    (Bundle.Trivial ℝ (WithTopology (Fin 2) ⊤))

/-- The trivial bundle over the real line with empty model has Lindelöf total space,
without requiring a point in the model fiber. -/
theorem real_empty_lindelofSpace_totalSpace :
    LindelofSpace (Bundle.TotalSpace Empty (Bundle.Trivial ℝ Empty)) :=
  FiberBundle.lindelofSpace_totalSpace (B := ℝ) Empty (Bundle.Trivial ℝ Empty)

end Bundle.Trivial
