/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The value embedding of units in a seminormed ring

The value map embeds the existing units of a seminormed ring, with their usual topology.
It requires neither completeness nor separation. It does not assert that the unit locus is open
or that the ambient ring inverse is continuous.

The proof uses Mathlib's `Units.isOpenEmbedding_val` on the completion. The completion map
induces the original topology even when it is not injective, and Mathlib's
`Topology.IsInducing.units_map` lifts this property to units. Descending the inducing property
and using the algebraic injectivity of `Units.val` gives the embedding.
-/

@[expose] public section

universe uR

/-- The value map from the units of a seminormed ring is a topological embedding, without
completeness or separation assumptions. -/
theorem Units.isEmbedding_val_seminormedRing
    {R : Type uR} [SeminormedRing R] :
    Topology.IsEmbedding (Units.val : Rˣ → R) := by
  let c : R →+* UniformSpace.Completion R := UniformSpace.Completion.coeRingHom
  have hc : Topology.IsInducing c :=
    (UniformSpace.Completion.isUniformInducing_coe R).isInducing
  have hcomp : Topology.IsInducing (c ∘ (Units.val : Rˣ → R)) :=
    (Units.isOpenEmbedding_val (R := UniformSpace.Completion R)).isInducing.comp
      (Topology.IsInducing.units_map (f := c.toMonoidHom) hc)
  exact ⟨Topology.IsInducing.of_comp Units.continuous_val
    UniformSpace.Completion.continuous_coeRingHom hcomp, Units.val_injective⟩
