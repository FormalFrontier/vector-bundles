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

The standard-base examples retain the usual topology on the noncompact real base
and all canonical trivial-bundle fiber and total-space topologies. The first model
is the indiscrete two-point space, compact by finiteness rather than discreteness.
The empty model is also finite and compact, and needs no nonemptiness hypothesis.
The usual real base is Lindelöf through its second-countable topology. The
empty-model characterization also applies over the uncountable discrete real
base, which is not Lindelöf, with the canonical bundle topologies.
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

namespace Bundle.Trivial

/-- The compact-model characterization applies to the canonical indiscrete pair over the reals. -/
theorem real_indiscretePair_lindelofSpace_totalSpace_via_iff :
    LindelofSpace
      (Bundle.TotalSpace (WithTopology (Fin 2) ⊤)
        (Bundle.Trivial ℝ (WithTopology (Fin 2) ⊤))) := by
  exact (FiberBundle.lindelofSpace_totalSpace_iff
    (WithTopology (Fin 2) ⊤)
    (Bundle.Trivial ℝ (WithTopology (Fin 2) ⊤))).mpr
      (Or.inr (inferInstance : LindelofSpace ℝ))

/-- The empty-model alternative works over the uncountable discrete real base. -/
theorem discreteReal_empty_lindelofSpace_totalSpace_via_iff :
    LindelofSpace
      (Bundle.TotalSpace Empty (Bundle.Trivial (WithTopology ℝ ⊥) Empty)) := by
  exact (FiberBundle.lindelofSpace_totalSpace_iff
    Empty (Bundle.Trivial (WithTopology ℝ ⊥) Empty)).mpr
      (Or.inl (inferInstance : IsEmpty Empty))

end Bundle.Trivial
