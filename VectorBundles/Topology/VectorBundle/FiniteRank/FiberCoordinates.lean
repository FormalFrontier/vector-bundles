/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Data.Bundle
public import VectorBundles.Topology.VectorBundle.FiniteRank.LinearEquiv

/-!
# Chart coordinates on projection fibres

A finite-rank chart gives a linear equivalence from the equality fibre of the
total-space projection to the chart's finite-dimensional model. It is the composite
of the canonical equivalence with the original fibre and the atlas coordinate
equivalence. Its inverse has the same total-space value as inverse chart coordinates.

Both families are continuous: inverse coordinates vary continuously with the base
point and model vector, and forward coordinates vary continuously on the preimage
of the chart base set. These are the coordinate-family continuity inputs for supported
weighted coordinates and finite chart reconstruction.

The equality fibres retain their subtype topologies and their canonical algebra
transported from the original fibres. No continuity of fibre operations, topology on
the total-space model parameter, or common rank for the charts is required.

## References

* Mathlib's total-space, linear-equivalence and chart-source homeomorphism APIs.
-/

@[expose] public section

open Bundle Topology

universe uK uB uE uP uI

namespace Bundle.FiniteRankAtlas

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)

attribute [local instance] TotalSpace.fiberAddCommMonoid TotalSpace.fiberModule

/-- Chart coordinates on the equality fibre of the total-space projection. -/
noncomputable def coordFiberLinearEquiv (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) :
    {t : TotalSpace P E // t.proj = b} ≃ₗ[K] (Fin (A.rank i) → K) :=
  (TotalSpace.fiberLinearEquivAt (E := E) K P b).symm.trans (A.coordLinearEquiv i hb)

/-- Coordinates on a projection fibre are the second coordinate of the chart. -/
@[simp]
theorem coordFiberLinearEquiv_apply (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (u : {t : TotalSpace P E // t.proj = b}) :
    A.coordFiberLinearEquiv i hb u = (A.chart i u.val).2 := by
  change A.coordLinearEquiv i hb ((TotalSpace.fiberLinearEquivAt (E := E) K P b).symm u) = _
  rw [A.coordLinearEquiv_apply, A.coord_apply,
    TotalSpace.fiberLinearEquivAt_symm_apply, TotalSpace.mk_fiberEquiv_symm]

/-- The inverse coordinate equivalence returns the constructor of the original
fibre vector supplied by the inverse atlas coordinate equivalence. -/
@[simp]
theorem coordFiberLinearEquiv_symm_apply_val_mk (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (w : Fin (A.rank i) → K) :
    ((A.coordFiberLinearEquiv i hb).symm w).val =
      (TotalSpace.mk b ((A.coordLinearEquiv i hb).symm w) : TotalSpace P E) := by
  change (TotalSpace.fiberLinearEquivAt (E := E) K P b
    ((A.coordLinearEquiv i hb).symm w)).val = _
  rw [TotalSpace.fiberLinearEquivAt_apply]

/-- The inverse coordinate equivalence has exactly the inverse chart's total-space value. -/
theorem coordFiberLinearEquiv_symm_apply_val (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (w : Fin (A.rank i) → K) :
    ((A.coordFiberLinearEquiv i hb).symm w).val = A.invCoord i ⟨b, hb⟩ w :=
  (A.coordFiberLinearEquiv_symm_apply_val_mk i hb w).trans
    (A.invCoord_eq_mk_coordLinearEquiv_symm i hb w).symm

/-- Inverse coordinates on projection fibres vary continuously in the chart base
point and model vector, with values in the given total space. -/
theorem continuous_coordFiberLinearEquiv_symm (i : A.Index) :
    Continuous (fun z : (A.chart i).baseSet × (Fin (A.rank i) → K) =>
      ((A.coordFiberLinearEquiv i z.1.property).symm z.2).val) := by
  simpa only [coordFiberLinearEquiv_symm_apply_val] using A.continuous_invCoord i

/-- Forward coordinates on projection fibres vary continuously over the preimage
of the chart base set, for the given total-space topology. -/
theorem continuous_coordFiberLinearEquiv (i : A.Index) :
    Continuous (fun t : {t : TotalSpace P E // t.proj ∈ (A.chart i).baseSet} =>
      A.coordFiberLinearEquiv i t.property ⟨t.val, rfl⟩) := by
  let k : {t : TotalSpace P E // t.proj ∈ (A.chart i).baseSet} → (A.chart i).source :=
    fun t => ⟨t.val, (A.mem_source_iff i t.val).mpr t.property⟩
  have hk : Continuous k :=
    continuous_subtype_val.subtype_mk (fun t => (A.mem_source_iff i t.val).mpr t.property)
  have hchart : Continuous (fun t => (A.sourceHomeomorph i (k t)).2) :=
    continuous_snd.comp ((A.sourceHomeomorph i).continuous.comp hk)
  apply hchart.congr
  intro t
  exact (A.sourceHomeomorph_snd i (k t)).trans
    (A.coordFiberLinearEquiv_apply i t.property ⟨t.val, rfl⟩).symm

end Bundle.FiniteRankAtlas
