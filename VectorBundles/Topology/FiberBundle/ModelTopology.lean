/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Changing the model tag of a bundle total space

`Bundle.TotalSpace.changeModelEquiv` changes only the model tag of a total space: both the
base point and the vector in the original fibre are preserved. Given a topology on the original
total space, `Bundle.TotalSpace.changeModelTopology` names its transport to the new tag, and
`Bundle.TotalSpace.changeModelHomeomorph` identifies these two topological spaces.

No topology on the base, fibres or model tags is needed. An independently specified topology on
the new total space agrees with the transported topology exactly when the tag equivalence is
inducing, or equivalently when both it and its inverse are continuous. Identity and composition
laws make successive changes of tag coherent. The usual `Homeomorph` continuity-composition API
then transports continuity of maps without changing their fibre values.

## References

The total-space representation is Mathlib's `Mathlib.Data.Bundle`. The homeomorphism construction
uses `Equiv.toHomeomorphOfIsInducing` from `Mathlib.Topology.Homeomorph.Defs`.
-/

@[expose] public section

open Topology

universe uB uE uP uQ uR

namespace Bundle.TotalSpace

variable {B : Type uB} (P : Type uP) (Q : Type uQ) (E : B → Type uE)

/-- Change the model tag of a total space, preserving its base point and fibre vector. -/
def changeModelEquiv : TotalSpace Q E ≃ TotalSpace P E where
  toFun z := ⟨z.proj, z.snd⟩
  invFun z := ⟨z.proj, z.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem changeModelEquiv_mk (b : B) (v : E b) :
    changeModelEquiv P Q E (mk b v) = mk b v := rfl

@[simp]
theorem changeModelEquiv_symm_mk (b : B) (v : E b) :
    (changeModelEquiv P Q E).symm (mk b v) = mk b v := rfl

@[simp]
theorem changeModelEquiv_proj (z : TotalSpace Q E) :
    (changeModelEquiv P Q E z).proj = z.proj := rfl

@[simp]
theorem changeModelEquiv_snd (z : TotalSpace Q E) :
    (changeModelEquiv P Q E z).snd = z.snd := rfl

@[simp]
theorem changeModelEquiv_symm_proj (z : TotalSpace P E) :
    ((changeModelEquiv P Q E).symm z).proj = z.proj := rfl

@[simp]
theorem changeModelEquiv_symm_snd (z : TotalSpace P E) :
    ((changeModelEquiv P Q E).symm z).snd = z.snd := rfl

@[simp]
theorem changeModelEquiv_symm :
    (changeModelEquiv P Q E).symm = changeModelEquiv Q P E := by
  apply Equiv.ext
  intro z
  rfl

/-- Changing a total-space model tag to itself is the identity equivalence. -/
@[simp]
theorem changeModelEquiv_self :
    changeModelEquiv P P E = Equiv.refl (TotalSpace P E) := by
  apply Equiv.ext
  intro z
  rfl

/-- Successive changes of model tag give the direct change of tag. -/
@[simp]
theorem changeModelEquiv_trans (R : Type uR) :
    (changeModelEquiv Q R E).trans (changeModelEquiv P Q E) =
      changeModelEquiv P R E := by
  apply Equiv.ext
  intro z
  rfl

/-- Transport a total-space topology to another model tag, retaining the original fibres.
This is a named topology, not a global instance. -/
@[instance_reducible]
def changeModelTopology (tP : TopologicalSpace (TotalSpace P E)) :
    TopologicalSpace (TotalSpace Q E) :=
  TopologicalSpace.induced (changeModelEquiv P Q E) tP

/-- The transported topology is induced by the base- and vector-preserving equivalence. -/
theorem changeModelTopology_eq_induced (tP : TopologicalSpace (TotalSpace P E)) :
    changeModelTopology P Q E tP =
      TopologicalSpace.induced (changeModelEquiv P Q E) tP := rfl

/-- The homeomorphism from the new model tag to the original one, for the transported topology.
It is obtained from Mathlib's inducing-equivalence constructor. -/
def changeModelHomeomorph (tP : TopologicalSpace (TotalSpace P E)) :
    @Homeomorph (TotalSpace Q E) (TotalSpace P E) (changeModelTopology P Q E tP) tP := by
  letI : TopologicalSpace (TotalSpace P E) := tP
  letI : TopologicalSpace (TotalSpace Q E) := changeModelTopology P Q E tP
  exact (changeModelEquiv P Q E).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem changeModelHomeomorph_toEquiv (tP : TopologicalSpace (TotalSpace P E)) :
    @Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP) = changeModelEquiv P Q E := rfl

@[simp]
theorem changeModelHomeomorph_mk (tP : TopologicalSpace (TotalSpace P E))
    (b : B) (v : E b) :
    (@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)) (mk b v) = mk b v := rfl

@[simp]
theorem changeModelHomeomorph_symm_mk (tP : TopologicalSpace (TotalSpace P E))
    (b : B) (v : E b) :
    (@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)).symm (mk b v) = mk b v := rfl

@[simp]
theorem changeModelHomeomorph_proj (tP : TopologicalSpace (TotalSpace P E))
    (z : TotalSpace Q E) :
    ((@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)) z).proj = z.proj := rfl

@[simp]
theorem changeModelHomeomorph_snd (tP : TopologicalSpace (TotalSpace P E))
    (z : TotalSpace Q E) :
    ((@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)) z).snd = z.snd := rfl

@[simp]
theorem changeModelHomeomorph_symm_proj (tP : TopologicalSpace (TotalSpace P E))
    (z : TotalSpace P E) :
    ((@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)).symm z).proj = z.proj := rfl

@[simp]
theorem changeModelHomeomorph_symm_snd (tP : TopologicalSpace (TotalSpace P E))
    (z : TotalSpace P E) :
    ((@Homeomorph.toEquiv _ _ (changeModelTopology P Q E tP) tP
      (changeModelHomeomorph P Q E tP)).symm z).snd = z.snd := rfl

/-- A set in the transported total space is open exactly when its counterpart under the inverse
change of tag is open in the original total space. -/
theorem isOpen_changeModelTopology_iff (tP : TopologicalSpace (TotalSpace P E))
    (s : Set (TotalSpace Q E)) :
    @IsOpen (TotalSpace Q E) (changeModelTopology P Q E tP) s ↔
      @IsOpen (TotalSpace P E) tP ((changeModelEquiv P Q E).symm ⁻¹' s) := by
  let : TopologicalSpace (TotalSpace P E) := tP
  let : TopologicalSpace (TotalSpace Q E) := changeModelTopology P Q E tP
  exact (changeModelHomeomorph P Q E tP).symm.isOpen_preimage.symm

/-- An independently specified topology is the transported topology exactly when the change of
model tag is inducing. -/
theorem eq_changeModelTopology_iff_isInducing (tP : TopologicalSpace (TotalSpace P E))
    (tQ : TopologicalSpace (TotalSpace Q E)) :
    tQ = changeModelTopology P Q E tP ↔
      @IsInducing (TotalSpace Q E) (TotalSpace P E) tQ tP (changeModelEquiv P Q E) :=
  ⟨fun h => ⟨h⟩, fun h => h.eq_induced⟩

/-- An independently specified topology is the transported topology exactly when both directions
of the base- and vector-preserving equivalence are continuous for the specified topologies. -/
theorem eq_changeModelTopology_iff_continuous (tP : TopologicalSpace (TotalSpace P E))
    (tQ : TopologicalSpace (TotalSpace Q E)) :
    tQ = changeModelTopology P Q E tP ↔
      @Continuous (TotalSpace Q E) (TotalSpace P E) tQ tP (changeModelEquiv P Q E) ∧
      @Continuous (TotalSpace P E) (TotalSpace Q E) tP tQ
        (changeModelEquiv P Q E).symm := by
  let : TopologicalSpace (TotalSpace P E) := tP
  constructor
  · intro h
    subst tQ
    let : TopologicalSpace (TotalSpace Q E) := changeModelTopology P Q E tP
    exact ⟨(changeModelHomeomorph P Q E tP).continuous,
      (changeModelHomeomorph P Q E tP).symm.continuous⟩
  · rintro ⟨hf, hg⟩
    let : TopologicalSpace (TotalSpace Q E) := tQ
    exact (@Homeomorph.mk (TotalSpace Q E) (TotalSpace P E) tQ tP
      (changeModelEquiv P Q E) hf hg).induced_eq.symm

/-- Transporting a total-space topology to the same model tag leaves it unchanged. -/
@[simp]
theorem changeModelTopology_self (tP : TopologicalSpace (TotalSpace P E)) :
    changeModelTopology P P E tP = tP := by
  rw [changeModelTopology_eq_induced, changeModelEquiv_self]
  exact @induced_id (TotalSpace P E) tP

/-- Transporting a total-space topology successively agrees with direct transport. -/
@[simp]
theorem changeModelTopology_trans (R : Type uR)
    (tP : TopologicalSpace (TotalSpace P E)) :
    changeModelTopology Q R E (changeModelTopology P Q E tP) =
      changeModelTopology P R E tP := by
  change TopologicalSpace.induced (changeModelEquiv Q R E)
      (TopologicalSpace.induced (changeModelEquiv P Q E) tP) =
    TopologicalSpace.induced (changeModelEquiv P R E) tP
  rw [induced_compose]
  rfl

/-- Changing a model tag to itself acts as the identity on the total space. Together with
`changeModelTopology_self`, this identifies the homeomorphism with the identity homeomorphism. -/
theorem changeModelHomeomorph_self_apply (tP : TopologicalSpace (TotalSpace P E))
    (z : TotalSpace P E) :
    (@Homeomorph.toEquiv _ _ (changeModelTopology P P E tP) tP
      (changeModelHomeomorph P P E tP)) z = z := rfl

end Bundle.TotalSpace
