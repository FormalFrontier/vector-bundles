module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import VectorBundles.Topology.Algebra.TrivSqZeroExt.Units
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.UnitInterval

/-!
# A fiber-preserving deformation of square-zero units

If the fiber of a trivial square-zero extension is a real module with jointly
continuous scalar multiplication, its raw second coordinate contracts to zero.
The product chart transports this contraction to the unit space. It fixes the
canonical section pointwise and preserves the first unit coordinate.

No compatibility between the real action and the two base-semiring actions is
required. In particular, the deformation is a homotopy of spaces, not a homotopy
through group homomorphisms.

## Implementation notes

The extension retains its given topology, with the same coordinate-inducing
hypothesis as the product chart. The deformation is provided as a continuous map
on the unit interval times the unit space, together with endpoint, fixed-section,
and fiber identities. No separate continuous-negation hypothesis is used: it
follows from the real action. The deformation is also bundled as a
`ContinuousMap.Homotopy` from the identity to the section after projection.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

variable {R : Type u} {M : Type v}
  [Semiring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalSpace (TrivSqZeroExt R M)] [Module ℝ M]

/-- Contract the raw fiber coordinate of a square-zero unit by the real scalar
`1 - t`, using the inverse of the product chart. Negation continuity follows from
joint continuity of the real action, without a compatibility assumption on actions. -/
noncomputable def unitsDeformation
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hreal : Continuous (fun p : ℝ × M => p.1 • p.2)) :
    C(unitInterval × (TrivSqZeroExt R M)ˣ, (TrivSqZeroExt R M)ˣ) := by
  have hneg : Continuous (fun m : M => -m) := by
    simpa only [Function.comp_def, id_eq, neg_one_smul] using
      hreal.comp
        ((continuous_const : Continuous (fun _ : M => (-1 : ℝ))).prodMk
          (continuous_id : Continuous (fun m : M => m)))
  have htime : Continuous (fun p : unitInterval × (TrivSqZeroExt R M)ˣ =>
      (1 : ℝ) - (p.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hfst : Continuous (fun p : unitInterval × (TrivSqZeroExt R M)ˣ =>
      unitsFst p.2) :=
    (continuous_unitsFst hA).comp continuous_snd
  have hsnd : Continuous (fun p : unitInterval × (TrivSqZeroExt R M)ˣ =>
      unitsSnd p.2) :=
    (continuous_unitsSnd hA).comp continuous_snd
  have hscale : Continuous (fun p : unitInterval × (TrivSqZeroExt R M)ˣ =>
      ((1 : ℝ) - (p.1 : ℝ)) • unitsSnd p.2) :=
    hreal.comp (htime.prodMk hsnd)
  exact
    { toFun := fun p => (unitsHomeomorphProd hA hL hQ hneg).symm
        (unitsFst p.2, ((1 : ℝ) - (p.1 : ℝ)) • unitsSnd p.2)
      continuous_toFun :=
        (unitsHomeomorphProd hA hL hQ hneg).symm.continuous.comp
          (hfst.prodMk hscale) }

variable
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hreal : Continuous (fun p : ℝ × M => p.1 • p.2))

@[simp]
theorem unitsDeformation_apply (t : unitInterval) (z : (TrivSqZeroExt R M)ˣ) :
    unitsDeformation hA hL hQ hreal (t, z) =
      unitsOfProd (unitsFst z, ((1 : ℝ) - (t : ℝ)) • unitsSnd z) := rfl

/-- The deformation starts at the identity of the unit space. -/
theorem unitsDeformation_zero (z : (TrivSqZeroExt R M)ˣ) :
    unitsDeformation hA hL hQ hreal (0, z) = z := by
  rw [unitsDeformation_apply]
  change unitsOfProd (unitsFst z, ((1 : ℝ) - 0) • unitsSnd z) = z
  rw [sub_zero, one_smul, unitsOfProd_unitsFst_unitsSnd]

/-- The deformation ends at the canonical section after the first unit projection. -/
theorem unitsDeformation_one (z : (TrivSqZeroExt R M)ˣ) :
    unitsDeformation hA hL hQ hreal (1, z) = unitsSection (unitsFst z) := by
  rw [unitsDeformation_apply]
  change unitsOfProd (unitsFst z, ((1 : ℝ) - 1) • unitsSnd z) = _
  rw [sub_self, zero_smul]
  rfl

/-- Every point of the canonical section is fixed throughout the deformation. -/
theorem unitsDeformation_unitsSection (t : unitInterval) (u : Rˣ) :
    unitsDeformation hA hL hQ hreal (t, unitsSection u) = unitsSection u := by
  rw [unitsDeformation_apply, unitsFst_unitsSection, unitsSnd_unitsSection, smul_zero]
  rfl

/-- The deformation preserves the first unit coordinate at every parameter. -/
theorem unitsFst_unitsDeformation (t : unitInterval) (z : (TrivSqZeroExt R M)ˣ) :
    unitsFst (unitsDeformation hA hL hQ hreal (t, z)) = unitsFst z := by
  rw [unitsDeformation_apply, unitsFst_unitsOfProd]

/-- The raw fiber coordinate scales by `1 - t` during the deformation. -/
theorem unitsSnd_unitsDeformation (t : unitInterval) (z : (TrivSqZeroExt R M)ˣ) :
    unitsSnd (unitsDeformation hA hL hQ hreal (t, z)) =
      ((1 : ℝ) - (t : ℝ)) • unitsSnd z := by
  rw [unitsDeformation_apply, unitsSnd_unitsOfProd]

/-- The canonical homotopy from the identity on square-zero units to the
zero-fiber section after projection, using the existing continuous deformation. -/
noncomputable def unitsHomotopy
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hreal : Continuous (fun p : ℝ × M => p.1 • p.2)) :
    ContinuousMap.Homotopy
      (⟨id, continuous_id⟩ :
        C((TrivSqZeroExt R M)ˣ, (TrivSqZeroExt R M)ˣ))
      ⟨fun z => unitsSection (unitsFst z), continuous_unitsSection_unitsFst hA⟩ := by
  constructor <;> first
  | exact unitsDeformation hA hL hQ hreal
  | exact (unitsDeformation hA hL hQ hreal).continuous
  | exact unitsDeformation_zero hA hL hQ hreal
  | exact unitsDeformation_one hA hL hQ hreal

/-- The bundled homotopy has the existing continuous deformation as its map. -/
@[simp]
theorem unitsHomotopy_apply (t : unitInterval) (z : (TrivSqZeroExt R M)ˣ) :
    unitsHomotopy hA hL hQ hreal (t, z) =
      unitsDeformation hA hL hQ hreal (t, z) := rfl

/-- The bundled homotopy fixes the canonical section at every parameter. -/
theorem unitsHomotopy_unitsSection (t : unitInterval) (u : Rˣ) :
    unitsHomotopy hA hL hQ hreal (t, unitsSection u) = unitsSection u := by
  rw [unitsHomotopy_apply, unitsDeformation_unitsSection]

end TrivSqZeroExt
