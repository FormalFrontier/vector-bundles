module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Maps.Basic

/-!
# Units of a trivial square-zero extension

The first unit coordinate and the unmodified second coordinate identify the units of
`TrivSqZeroExt R M` with `Rˣ × M` as spaces. Only the actions restricted to units and
negation on `M` need to be continuous. Multiplication on `R` and addition on `M` need
not be continuous.

## Implementation notes

The topology on the extension is an explicit parameter. The hypothesis that the pair
of coordinate projections is inducing says exactly that it is the product topology
of the given topologies on `R` and `M`. No topology on either factor is changed, and
no topological-space instance for the extension is introduced here. The algebraic
constructor uses the existing unit criterion; its inverse-coordinate formula is
then deduced from identities of that unit. The product is a product of spaces, not
a direct-product decomposition of groups.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

variable {R : Type u} {M : Type v}
  [Semiring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

/-- The first coordinate of a unit of a trivial square-zero extension, as a unit. -/
def unitsFst : (TrivSqZeroExt R M)ˣ →* Rˣ :=
  Units.map
    { toFun := fun a : TrivSqZeroExt R M => a.fst
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The unmodified second coordinate of the value of a unit. -/
def unitsSnd (z : (TrivSqZeroExt R M)ˣ) : M :=
  (z : TrivSqZeroExt R M).snd

@[simp]
theorem coe_unitsFst (z : (TrivSqZeroExt R M)ˣ) :
    (unitsFst z : R) = (z : TrivSqZeroExt R M).fst := rfl

@[simp]
theorem coe_inv_unitsFst (z : (TrivSqZeroExt R M)ˣ) :
    (↑((unitsFst z)⁻¹) : R) = (↑(z⁻¹) : TrivSqZeroExt R M).fst := rfl

@[simp]
theorem unitsSnd_mul (z w : (TrivSqZeroExt R M)ˣ) :
    unitsSnd (z * w) = (unitsFst z : R) • unitsSnd w +
      MulOpposite.op (unitsFst w : R) • unitsSnd z := rfl

/-- The unit with prescribed first unit coordinate and raw second coordinate. -/
noncomputable def unitsOfProd (p : Rˣ × M) : (TrivSqZeroExt R M)ˣ :=
  (show @IsUnit (TrivSqZeroExt R M) inferInstance ⟨(p.1 : R), p.2⟩ from
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr p.1.isUnit).unit

@[simp]
theorem coe_unitsOfProd (p : Rˣ × M) :
    (unitsOfProd p : TrivSqZeroExt R M) = ⟨(p.1 : R), p.2⟩ :=
  IsUnit.unit_spec _

@[simp]
theorem unitsFst_unitsOfProd (p : Rˣ × M) : unitsFst (unitsOfProd p) = p.1 := by
  apply Units.ext
  change (unitsOfProd p : TrivSqZeroExt R M).fst = (p.1 : R)
  rw [coe_unitsOfProd]
  rfl

@[simp]
theorem unitsSnd_unitsOfProd (p : Rˣ × M) : unitsSnd (unitsOfProd p) = p.2 := by
  change (unitsOfProd p : TrivSqZeroExt R M).snd = p.2
  rw [coe_unitsOfProd]
  rfl

@[simp]
theorem unitsOfProd_unitsFst_unitsSnd (z : (TrivSqZeroExt R M)ˣ) :
    unitsOfProd (unitsFst z, unitsSnd z) = z := by
  apply Units.ext
  rw [coe_unitsOfProd]
  apply TrivSqZeroExt.ext <;> rfl

/-- The first unit coordinate and the raw second coordinate jointly determine a unit. -/
theorem units_ext {z w : (TrivSqZeroExt R M)ˣ}
    (hfst : unitsFst z = unitsFst w) (hsnd : unitsSnd z = unitsSnd w) : z = w := by
  rw [← unitsOfProd_unitsFst_unitsSnd z, ← unitsOfProd_unitsFst_unitsSnd w]
  exact congrArg unitsOfProd (Prod.ext hfst hsnd)

/-- The second coordinate of inversion, deduced from the existing unit identities. -/
theorem unitsSnd_inv (z : (TrivSqZeroExt R M)ˣ) :
    unitsSnd (z⁻¹) =
      -(MulOpposite.op (↑((unitsFst z)⁻¹) : R) •
        ((↑((unitsFst z)⁻¹) : R) • unitsSnd z)) := by
  have hfst : (z : TrivSqZeroExt R M).fst *
      (↑(z⁻¹) : TrivSqZeroExt R M).fst = 1 :=
    congrArg (fun a : TrivSqZeroExt R M => a.fst) z.val_inv
  have hop : MulOpposite.op (↑(z⁻¹) : TrivSqZeroExt R M).fst *
      MulOpposite.op (z : TrivSqZeroExt R M).fst = (1 : Rᵐᵒᵖ) := by
    change MulOpposite.op ((z : TrivSqZeroExt R M).fst *
      (↑(z⁻¹) : TrivSqZeroExt R M).fst) = MulOpposite.op (1 : R)
    exact congrArg MulOpposite.op hfst
  have hsnd : (↑(z⁻¹) : TrivSqZeroExt R M).fst • unitsSnd z +
      MulOpposite.op (z : TrivSqZeroExt R M).fst • unitsSnd (z⁻¹) = 0 :=
    congrArg (fun a : TrivSqZeroExt R M => a.snd) z.inv_val
  have h := congrArg
    (fun m : M => MulOpposite.op (↑(z⁻¹) : TrivSqZeroExt R M).fst • m) hsnd
  rw [smul_add, ← mul_smul, hop, one_smul, smul_zero] at h
  change MulOpposite.op (↑((unitsFst z)⁻¹) : R) •
    ((↑((unitsFst z)⁻¹) : R) • unitsSnd z) + unitsSnd (z⁻¹) = 0 at h
  calc
    unitsSnd (z⁻¹) =
        -(MulOpposite.op (↑((unitsFst z)⁻¹) : R) •
          ((↑((unitsFst z)⁻¹) : R) • unitsSnd z)) +
        (MulOpposite.op (↑((unitsFst z)⁻¹) : R) •
          ((↑((unitsFst z)⁻¹) : R) • unitsSnd z) + unitsSnd (z⁻¹)) := by
      rw [← add_assoc, neg_add_cancel, zero_add]
    _ = _ := by rw [h, add_zero]

@[simp]
theorem coe_inv_unitsOfProd (p : Rˣ × M) :
    (↑((unitsOfProd p)⁻¹) : TrivSqZeroExt R M) =
      ⟨(↑(p.1⁻¹) : R), -(MulOpposite.op (↑(p.1⁻¹) : R) • ((↑(p.1⁻¹) : R) • p.2))⟩ := by
  apply TrivSqZeroExt.ext
  · change (↑((unitsFst (unitsOfProd p))⁻¹) : R) = (↑(p.1⁻¹) : R)
    rw [unitsFst_unitsOfProd]
  · change unitsSnd ((unitsOfProd p)⁻¹) = _
    rw [unitsSnd_inv, unitsFst_unitsOfProd, unitsSnd_unitsOfProd]
    rfl

/-- The canonical section of the first unit coordinate, with zero second coordinate. -/
noncomputable def unitsSection : Rˣ →* (TrivSqZeroExt R M)ˣ where
  toFun u := unitsOfProd (u, (0 : M))
  map_one' := by
    apply Units.ext
    rw [coe_unitsOfProd]
    rfl
  map_mul' u v := by
    apply Units.ext
    simp only [coe_unitsOfProd, Units.val_mul]
    change (⟨(u : R) * (v : R), (0 : M)⟩ : TrivSqZeroExt R M) =
      ⟨(u : R) * (v : R), (u : R) • (0 : M) + MulOpposite.op (v : R) • (0 : M)⟩
    rw [smul_zero, smul_zero, add_zero]

@[simp]
theorem coe_unitsSection (u : Rˣ) :
    (↑(unitsSection (M := M) u) : TrivSqZeroExt R M) = ⟨(u : R), 0⟩ := coe_unitsOfProd (u, (0 : M))

@[simp]
theorem coe_inv_unitsSection (u : Rˣ) :
    (↑((unitsSection (M := M) u)⁻¹) : TrivSqZeroExt R M) = ⟨(↑(u⁻¹) : R), 0⟩ := by
  change (↑((unitsOfProd (u, (0 : M)))⁻¹) : TrivSqZeroExt R M) = _
  rw [coe_inv_unitsOfProd]
  simp only [smul_zero, neg_zero]
  rfl

@[simp]
theorem unitsFst_unitsSection (u : Rˣ) : unitsFst (unitsSection (M := M) u) = u :=
  unitsFst_unitsOfProd (u, (0 : M))

@[simp]
theorem unitsSnd_unitsSection (u : Rˣ) : unitsSnd (unitsSection (M := M) u) = (0 : M) :=
  unitsSnd_unitsOfProd (u, (0 : M))

theorem unitsSection_unitsFst_unitsSection (u : Rˣ) :
    unitsSection (unitsFst (unitsSection (M := M) u)) =
      (unitsSection u : (TrivSqZeroExt R M)ˣ) := by
  rw [unitsFst_unitsSection]

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalSpace (TrivSqZeroExt R M)]

-- Inversion exchanges the two coordinates defining the topology on units.
private theorem continuous_units_inv : Continuous (fun u : Rˣ => u⁻¹) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_iff.mp
      (continuous_id : Continuous (fun u : Rˣ => u))).2
  · simpa only [inv_inv] using
      (Units.continuous_val : Continuous (fun u : Rˣ => (u : R)))

/-- The first unit coordinate is continuous for the product topology on the extension. -/
theorem continuous_unitsFst
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd))) :
    Continuous (unitsFst : (TrivSqZeroExt R M)ˣ → Rˣ) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun z : (TrivSqZeroExt R M)ˣ => (z : TrivSqZeroExt R M).fst)
    exact continuous_fst.comp (hA.continuous.comp Units.continuous_val)
  · change Continuous (fun z : (TrivSqZeroExt R M)ˣ => (↑(z⁻¹) : TrivSqZeroExt R M).fst)
    exact continuous_fst.comp
      (hA.continuous.comp
        (Units.continuous_val.comp (continuous_units_inv (R := TrivSqZeroExt R M))))

/-- The raw second coordinate is continuous for the product topology on the extension. -/
theorem continuous_unitsSnd
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd))) :
    Continuous (unitsSnd : (TrivSqZeroExt R M)ˣ → M) :=
  continuous_snd.comp (hA.continuous.comp Units.continuous_val)

/-- The unit constructor is continuous under joint unit-restricted action continuity
and continuous negation on the fiber. -/
theorem continuous_unitsOfProd
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hneg : Continuous (fun m : M => -m)) :
    Continuous (unitsOfProd : Rˣ × M → (TrivSqZeroExt R M)ˣ) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply hA.continuous_iff.mpr
    change Continuous (fun p : Rˣ × M =>
      ((↑(unitsOfProd p) : TrivSqZeroExt R M).fst,
        (↑(unitsOfProd p) : TrivSqZeroExt R M).snd))
    simp only [coe_unitsOfProd]
    exact (Units.continuous_val.comp continuous_fst).prodMk
      (continuous_snd : Continuous (fun p : Rˣ × M => p.2))
  · apply hA.continuous_iff.mpr
    change Continuous (fun p : Rˣ × M =>
      ((↑((unitsOfProd p)⁻¹) : TrivSqZeroExt R M).fst,
        (↑((unitsOfProd p)⁻¹) : TrivSqZeroExt R M).snd))
    have hi : Continuous (fun p : Rˣ × M => p.1⁻¹) :=
      continuous_units_inv.comp continuous_fst
    have hleft : Continuous (fun p : Rˣ × M => (↑(p.1⁻¹) : R) • p.2) :=
      hL.comp (hi.prodMk continuous_snd)
    have hright : Continuous (fun p : Rˣ × M =>
        MulOpposite.op (↑(p.1⁻¹) : R) • ((↑(p.1⁻¹) : R) • p.2)) :=
      hQ.comp (hleft.prodMk hi)
    simp only [coe_inv_unitsOfProd]
    exact (Units.continuous_val.comp hi).prodMk (hneg.comp hright)

/-- Units of a trivial square-zero extension with the product topology form the
product of the base unit space and the raw fiber space. This is a homeomorphism of
spaces, without a direct-product group assertion. -/
noncomputable def unitsHomeomorphProd
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hneg : Continuous (fun m : M => -m)) :
    (TrivSqZeroExt R M)ˣ ≃ₜ Rˣ × M where
  toFun z := (unitsFst z, unitsSnd z)
  invFun := unitsOfProd
  left_inv := unitsOfProd_unitsFst_unitsSnd
  right_inv p := Prod.ext (unitsFst_unitsOfProd p) (unitsSnd_unitsOfProd p)
  continuous_toFun := (continuous_unitsFst hA).prodMk (continuous_unitsSnd hA)
  continuous_invFun := continuous_unitsOfProd hA hL hQ hneg

variable
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd)))
    (hL : Continuous (fun p : Rˣ × M => (p.1 : R) • p.2))
    (hQ : Continuous (fun p : M × Rˣ => MulOpposite.op (p.2 : R) • p.1))
    (hneg : Continuous (fun m : M => -m))

@[simp]
theorem unitsHomeomorphProd_apply (z : (TrivSqZeroExt R M)ˣ) :
    unitsHomeomorphProd hA hL hQ hneg z = (unitsFst z, unitsSnd z) := rfl

@[simp]
theorem unitsHomeomorphProd_symm_apply (p : Rˣ × M) :
    (unitsHomeomorphProd hA hL hQ hneg).symm p = unitsOfProd p := rfl

theorem unitsHomeomorphProd_unitsSection (u : Rˣ) :
    unitsHomeomorphProd hA hL hQ hneg (unitsSection u) = (u, (0 : M)) := by
  simp only [unitsHomeomorphProd_apply, unitsFst_unitsSection, unitsSnd_unitsSection]

/-- Multiplication in raw product coordinates has the square-zero bimodule law. -/
theorem unitsHomeomorphProd_mul (p q : Rˣ × M) :
    unitsHomeomorphProd hA hL hQ hneg
        ((unitsHomeomorphProd hA hL hQ hneg).symm p *
          (unitsHomeomorphProd hA hL hQ hneg).symm q) =
      (p.1 * q.1, (p.1 : R) • q.2 + MulOpposite.op (q.1 : R) • p.2) := by
  simp only [unitsHomeomorphProd_apply, unitsHomeomorphProd_symm_apply, map_mul,
    unitsSnd_mul, unitsFst_unitsOfProd, unitsSnd_unitsOfProd]

/-- The canonical zero-fiber section is continuous; no action continuity is needed. -/
theorem continuous_unitsSection
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd))) :
    Continuous (unitsSection : Rˣ → (TrivSqZeroExt R M)ˣ) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply hA.continuous_iff.mpr
    change Continuous (fun u : Rˣ =>
      ((↑(unitsSection (M := M) u) : TrivSqZeroExt R M).fst,
        (↑(unitsSection (M := M) u) : TrivSqZeroExt R M).snd))
    simp only [coe_unitsSection]
    exact Units.continuous_val.prodMk
      (continuous_const : Continuous (fun _ : Rˣ => (0 : M)))
  · apply hA.continuous_iff.mpr
    change Continuous (fun u : Rˣ =>
      ((↑((unitsSection (M := M) u)⁻¹) : TrivSqZeroExt R M).fst,
        (↑((unitsSection (M := M) u)⁻¹) : TrivSqZeroExt R M).snd))
    simp only [coe_inv_unitsSection]
    exact (Units.continuous_val.comp continuous_units_inv).prodMk
      (continuous_const : Continuous (fun _ : Rˣ => (0 : M)))

/-- The zero-fiber section is a topological embedding, without separation hypotheses. -/
theorem isEmbedding_unitsSection
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd))) :
    Topology.IsEmbedding (unitsSection : Rˣ → (TrivSqZeroExt R M)ˣ) :=
  (show Function.LeftInverse
    (unitsFst : (TrivSqZeroExt R M)ˣ → Rˣ) unitsSection from unitsFst_unitsSection).isEmbedding
      (continuous_unitsFst hA) (continuous_unitsSection hA)

/-- Projecting to the first unit coordinate and taking the zero-fiber section is continuous. -/
theorem continuous_unitsSection_unitsFst
    (hA : Topology.IsInducing (fun a : TrivSqZeroExt R M => (a.fst, a.snd))) :
    Continuous (fun z : (TrivSqZeroExt R M)ˣ => unitsSection (M := M) (unitsFst z)) :=
  (continuous_unitsSection hA).comp (continuous_unitsFst hA)

end Topology

end TrivSqZeroExt
