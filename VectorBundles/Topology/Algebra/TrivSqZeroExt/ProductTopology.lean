module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import VectorBundles.Topology.Algebra.TrivSqZeroExt.Homotopy

/-!
# The coordinate product topology on a square-zero extension

The topology induced by the two coordinates uses the given topologies on both
factors. With the standard value-and-inverse topology on its units, the extension
has the product chart and fiber-preserving homotopy of square-zero units.

## Implementation notes

The topologies on the extension and its units are non-instance data. The chart
and homotopy display these data in their types; neither construction changes a
factor topology or requires continuous addition or multiplication.
-/

@[expose] public section

universe u v w

namespace TrivSqZeroExt

section Coordinates

variable (R : Type u) (M : Type v) [TopologicalSpace R] [TopologicalSpace M]

/-- The topology induced by the coordinates into the product of the given factor spaces. -/
@[instance_reducible]
def coordinateProductTopology : TopologicalSpace (TrivSqZeroExt R M) :=
  TopologicalSpace.induced (fun a : TrivSqZeroExt R M => (a.fst, a.snd)) inferInstance

/-- The coordinate pair induces the coordinate product topology. -/
theorem isInducing_coordinateProductTopology :
    @Topology.IsInducing (TrivSqZeroExt R M) (R × M)
      (coordinateProductTopology R M) inferInstance (fun a => (a.fst, a.snd)) := by
  exact Topology.IsInducing.induced (fun a : TrivSqZeroExt R M => (a.fst, a.snd))

/-- A map into the coordinate product topology is continuous exactly when both
coordinates are continuous in the original factor spaces. -/
theorem continuous_coordinateProductTopology_iff
    {X : Type w} [TopologicalSpace X] (f : X → TrivSqZeroExt R M) :
    @Continuous X (TrivSqZeroExt R M) _ (coordinateProductTopology R M) f ↔
      Continuous (fun x => (f x).fst) ∧ Continuous (fun x => (f x).snd) := by
  let : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  have hA := isInducing_coordinateProductTopology R M
  constructor
  · intro h
    exact ⟨continuous_fst.comp (hA.continuous.comp h),
      continuous_snd.comp (hA.continuous.comp h)⟩
  · rintro ⟨hf, hs⟩
    exact hA.continuous_iff.mpr (hf.prodMk hs)

end Coordinates

section UnitsTopology

variable (R : Type u) (M : Type v)
  [TopologicalSpace R] [TopologicalSpace M] [Monoid (TrivSqZeroExt R M)]

/-- The standard value-and-inverse units topology for the coordinate product topology. -/
@[instance_reducible]
def productUnitsTopology : TopologicalSpace (TrivSqZeroExt R M)ˣ := by
  letI : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact inferInstance

/-- Continuity into the product units topology is tested on the value and inverse
value, both in the coordinate product topology. -/
theorem continuous_productUnitsTopology_iff
    {X : Type w} [TopologicalSpace X] (f : X → (TrivSqZeroExt R M)ˣ) :
    @Continuous X (TrivSqZeroExt R M)ˣ _ (productUnitsTopology R M) f ↔
      @Continuous X (TrivSqZeroExt R M) _ (coordinateProductTopology R M)
        (fun x => (f x : TrivSqZeroExt R M)) ∧
      @Continuous X (TrivSqZeroExt R M) _ (coordinateProductTopology R M)
        (fun x => (↑((f x)⁻¹) : TrivSqZeroExt R M)) := by
  let : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact Units.continuous_iff

end UnitsTopology

variable (R : Type u) (M : Type v)
  [Semiring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]

/-- The product chart for units with the coordinate product topology, retaining the
original topologies of the base and fiber. This is a homeomorphism of spaces. -/
noncomputable def productUnitsHomeomorph
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hneg : Continuous (fun m : M => -m)) :
    @Homeomorph (TrivSqZeroExt R M)ˣ (Rˣ × M)
      (productUnitsTopology R M) inferInstance := by
  letI : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact unitsHomeomorphProd (isInducing_coordinateProductTopology R M) hL hQ hneg

variable
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hneg : Continuous (fun m : M => -m))

@[simp]
theorem productUnitsHomeomorph_apply (z : (TrivSqZeroExt R M)ˣ) :
    productUnitsHomeomorph R M hL hQ hneg z = (unitsFst z, unitsSnd z) := rfl

@[simp]
theorem productUnitsHomeomorph_symm_apply (p : Rˣ × M) :
    (@Homeomorph.symm (TrivSqZeroExt R M)ˣ (Rˣ × M)
      (productUnitsTopology R M) inferInstance
      (productUnitsHomeomorph R M hL hQ hneg)) p = unitsOfProd p := rfl

section Real

variable [Module ℝ M]

/-- The fiber-preserving homotopy for the coordinate product topology. The real
action need not commute with either base action, and supplies continuous negation. -/
noncomputable def productUnitsHomotopy
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hreal : Continuous (fun p : ℝ × M => p.1 • p.2)) :
    @ContinuousMap.Homotopy (TrivSqZeroExt R M)ˣ (TrivSqZeroExt R M)ˣ
      (productUnitsTopology R M) (productUnitsTopology R M)
      (@ContinuousMap.mk (TrivSqZeroExt R M)ˣ (TrivSqZeroExt R M)ˣ
        (productUnitsTopology R M) (productUnitsTopology R M)
        id (@continuous_id (TrivSqZeroExt R M)ˣ (productUnitsTopology R M)))
      (@ContinuousMap.mk (TrivSqZeroExt R M)ˣ (TrivSqZeroExt R M)ˣ
        (productUnitsTopology R M) (productUnitsTopology R M)
        (fun z => unitsSection (unitsFst z))
        (@continuous_unitsSection_unitsFst R M _ _ _ _ _ _ _
          (coordinateProductTopology R M) (isInducing_coordinateProductTopology R M))) := by
  letI : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact unitsHomotopy (isInducing_coordinateProductTopology R M) hL hQ hreal

variable (hreal : Continuous (fun p : ℝ × M => p.1 • p.2))

/-- In the product units topology the homotopy scales only the raw fiber coordinate. -/
@[simp]
theorem productUnitsHomotopy_apply (t : unitInterval) (z : (TrivSqZeroExt R M)ˣ) :
    productUnitsHomotopy R M hL hQ hreal (t, z) =
      unitsOfProd (unitsFst z, ((1 : ℝ) - (t : ℝ)) • unitsSnd z) := by
  let : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact (unitsHomotopy_apply (isInducing_coordinateProductTopology R M) hL hQ hreal t z).trans
    (unitsDeformation_apply (isInducing_coordinateProductTopology R M) hL hQ hreal t z)

/-- The homotopy fixes the zero-fiber section pointwise for the product units topology. -/
theorem productUnitsHomotopy_unitsSection (t : unitInterval) (u : Rˣ) :
    productUnitsHomotopy R M hL hQ hreal (t, unitsSection u) = unitsSection u := by
  let : TopologicalSpace (TrivSqZeroExt R M) := coordinateProductTopology R M
  exact unitsHomotopy_unitsSection (isInducing_coordinateProductTopology R M) hL hQ hreal t u

end Real

end TrivSqZeroExt
