/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Frame
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Topology.Order

/-!
# Examples of trivializations from finite frames

The standard frame of the real plane gives the standard trivialization over `ℝ`.
An empty frame gives the rank-zero trivialization, and a plane bundle over the empty base
requires no choice of a base point.
-/

-- These bundle clients are intentionally private and export no declarations.
set_option linter.privateModule false

@[expose] public section

open Bundle Module
open scoped Bundle

universe uB

namespace VectorBundleFrameExamples

private abbrev Plane := Fin 2 → ℝ

private noncomputable def planeBasis : Basis (Fin 2) ℝ Plane :=
  Pi.basisFun ℝ (Fin 2)

private theorem continuous_plane_basis (i : Fin 2) :
    Continuous (fun x : ℝ ↦
      TotalSpace.mk' Plane (E := Bundle.Trivial ℝ Plane) x (planeBasis i)) := by
  exact (Bundle.Trivial.homeomorphProd ℝ Plane).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

private noncomputable def planeTrivialization :
    Trivialization Plane (π Plane (Bundle.Trivial ℝ Plane)) :=
  Bundle.Trivialization.ofBasis planeBasis (fun _ : ℝ ↦ planeBasis)
    continuous_plane_basis

private theorem planeBasis_zero_ne_zero : planeBasis 0 ≠ 0 := by
  exact planeBasis.ne_zero 0

private theorem planeTrivialization_eq_trivialization :
    planeTrivialization = Bundle.Trivial.trivialization ℝ Plane := by
  exact Bundle.Trivialization.ofBasis_trivial planeBasis continuous_plane_basis

private theorem planeTrivialization_symm_apply (x : ℝ) (w : Plane) :
    planeTrivialization.toOpenPartialHomeomorph.symm (x, w) =
      TotalSpace.mk' Plane (E := Bundle.Trivial ℝ Plane) x w := by
  rw [show planeTrivialization = Bundle.Trivial.trivialization ℝ Plane from
    Bundle.Trivialization.ofBasis_trivial planeBasis continuous_plane_basis]
  rfl

private theorem continuous_plane_basis_coordinates :
    Continuous (fun z : TotalSpace Plane (Bundle.Trivial ℝ Plane) ↦
      planeBasis.equivFun z.2) := by
  exact VectorBundle.continuous_basis_equivFun
    (F := Plane) (E := Bundle.Trivial ℝ Plane)
    (fun _ : ℝ ↦ planeBasis) continuous_plane_basis

private theorem continuous_plane_section_iff_coordinates (s : ℝ → Plane) :
    Continuous (fun x ↦ TotalSpace.mk' Plane (E := Bundle.Trivial ℝ Plane) x (s x)) ↔
      Continuous (fun x ↦ s x 0) ∧ Continuous (fun x ↦ s x 1) := by
  rw [VectorBundle.continuous_section_iff_basis_coeff
    (F := Plane) (E := Bundle.Trivial ℝ Plane)
    (fun _ : ℝ ↦ planeBasis) continuous_plane_basis s]
  simp [planeBasis, Fin.forall_fin_two]

private theorem exists_plane_global_linear_trivialization :
    ∃ e : Trivialization Plane (π Plane (Bundle.Trivial ℝ Plane)),
      e.baseSet = Set.univ ∧ e.IsLinear ℝ := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ Plane := by simp [Plane]
  apply (VectorBundle.exists_global_trivialization_iff_linearIndependent
    (𝕜 := ℝ) (B := ℝ) (F := Plane) (E := Bundle.Trivial ℝ Plane)
    (ι := Fin 2) hcard).2
  exact ⟨fun i (_ : ℝ) ↦ planeBasis i, continuous_plane_basis,
    fun _ ↦ planeBasis.linearIndependent⟩

private abbrev ZeroFiber := Fin 0 → ℝ

private noncomputable def zeroBasis : Basis (Fin 0) ℝ ZeroFiber :=
  Pi.basisFun ℝ (Fin 0)

private theorem continuous_zero_basis {B : Type uB} [TopologicalSpace B] (i : Fin 0) :
    Continuous (fun x : B ↦
      TotalSpace.mk' ZeroFiber (E := Bundle.Trivial B ZeroFiber) x (zeroBasis i)) := by
  exact Fin.elim0 i

private noncomputable def zeroTrivialization (B : Type uB) [TopologicalSpace B] :
    Trivialization ZeroFiber (π ZeroFiber (Bundle.Trivial B ZeroFiber)) :=
  Bundle.Trivialization.ofBasis zeroBasis (fun _ : B ↦ zeroBasis)
    (continuous_zero_basis (B := B))

private theorem zeroTrivialization_eq_trivialization :
    zeroTrivialization ℝ = Bundle.Trivial.trivialization ℝ ZeroFiber := by
  exact Bundle.Trivialization.ofBasis_trivial zeroBasis (continuous_zero_basis (B := ℝ))

private theorem zeroTrivialization_symm_apply
    {B : Type uB} [TopologicalSpace B] (x : B) (w : ZeroFiber) :
    (zeroTrivialization B).symm x w = 0 := by
  exact Subsingleton.elim _ _

private theorem continuous_empty_plane_basis (i : Fin 2) :
    Continuous (fun x : Empty ↦
      TotalSpace.mk' Plane (E := Bundle.Trivial Empty Plane) x (planeBasis i)) := by
  exact continuous_iff_continuousAt.2 (fun x ↦ nomatch x)

private noncomputable def emptyPlaneTrivialization :
    Trivialization Plane (π Plane (Bundle.Trivial Empty Plane)) :=
  Bundle.Trivialization.ofBasis planeBasis (fun _ : Empty ↦ planeBasis)
    continuous_empty_plane_basis

private theorem emptyPlaneTrivialization_eq_trivialization :
    emptyPlaneTrivialization = Bundle.Trivial.trivialization Empty Plane := by
  exact Bundle.Trivialization.ofBasis_trivial planeBasis continuous_empty_plane_basis

end VectorBundleFrameExamples
