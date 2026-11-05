module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import VectorBundles.Topology.Algebra.TrivSqZeroExt.ProductTopology
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Additive topology of a square-zero extension

The coordinate product topology on `TrivSqZeroExt R M` makes its canonical
additive group a topological additive group whenever the two factors are
topological additive groups.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

variable (R : Type u) (M : Type v)
  [AddGroup R] [AddGroup M] [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalAddGroup R] [IsTopologicalAddGroup M]

/-- The coordinate product topology preserves the topological additive group
structures of the two factors. -/
theorem isTopologicalAddGroup_coordinateProductTopology :
    @IsTopologicalAddGroup (TrivSqZeroExt R M) (coordinateProductTopology R M)
      inferInstance := by
  let : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  have hcoord :
      Continuous (fun a : TrivSqZeroExt R M => a.fst) ∧
        Continuous (fun a : TrivSqZeroExt R M => a.snd) :=
    (continuous_coordinateProductTopology_iff R M id).mp continuous_id
  exact
    { continuous_add := (continuous_coordinateProductTopology_iff R M
        (fun p : TrivSqZeroExt R M × TrivSqZeroExt R M => p.1 + p.2)).mpr
        ⟨(hcoord.1.comp continuous_fst).add (hcoord.1.comp continuous_snd),
          (hcoord.2.comp continuous_fst).add (hcoord.2.comp continuous_snd)⟩
      continuous_neg := (continuous_coordinateProductTopology_iff R M
        (fun a : TrivSqZeroExt R M => -a)).mpr ⟨hcoord.1.neg, hcoord.2.neg⟩ }

end TrivSqZeroExt
