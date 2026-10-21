/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Proper
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.Complex.Circle

/-!
# Properness and compactness of stock trivial bundles

The trivial bundle on the real line with its two-element discrete model has a proper projection.
The projection is not injective: the points with fiber coordinates `0` and `1` over the origin
are distinct. All examples use Mathlib's original trivial-bundle topology and bundle structure.

An empty base needs no compactness of the model, an empty model gives a proper projection,
and a real fiber over a point obstructs properness.

The trivial circle bundle over the circle has compact total space, with the canonical topology
identifying it with the usual torus. Empty-model and empty-base examples show why recovering
compactness of the base and the model from the total space requires the respective nonemptiness
assumptions.
-/

@[expose] public section

-- The two-point model has public projection theorems; compactness and empty cases remain private.

open Bundle

namespace Bundle.Trivial

/-- The trivial bundle on `ℝ` with discrete fiber `Fin 2` has proper projection. -/
public theorem isProperMap_proj_finTwo :
    IsProperMap (TotalSpace.proj (F := Fin 2) (E := Trivial ℝ (Fin 2))) := by
  exact FiberBundle.isProperMap_proj (Fin 2) (Trivial ℝ (Fin 2))

/-- The projection of the trivial bundle on `ℝ` with fiber `Fin 2` is not injective. -/
public theorem not_injective_proj_finTwo :
    ¬ Function.Injective (TotalSpace.proj (F := Fin 2) (E := Trivial ℝ (Fin 2))) := by
  intro h
  have h01 : TotalSpace.mk' (E := Trivial ℝ (Fin 2)) (Fin 2) (0 : ℝ) (0 : Fin 2) =
      TotalSpace.mk' (E := Trivial ℝ (Fin 2)) (Fin 2) (0 : ℝ) (1 : Fin 2) := h rfl
  have hcoord : (0 : Fin 2) = 1 :=
    (TotalSpace.mk_inj (F := Fin 2) (E := Trivial ℝ (Fin 2)) (b := (0 : ℝ))).mp h01
  exact (by decide : (0 : Fin 2) ≠ 1) hcoord

private theorem empty_base_projection :
    IsProperMap (TotalSpace.proj (F := ℝ) (E := Trivial Empty ℝ)) := by
  exact (FiberBundle.isProperMap_proj_iff ℝ (Trivial Empty ℝ)).mpr (fun b ↦ nomatch b)

private theorem empty_model_projection :
    IsProperMap (TotalSpace.proj (F := Empty) (E := Trivial ℝ Empty)) := by
  exact FiberBundle.isProperMap_proj Empty (Trivial ℝ Empty)

private theorem real_point_projection_not_proper :
    ¬ IsProperMap (TotalSpace.proj (F := ℝ) (E := Trivial PUnit ℝ)) := by
  intro h
  have hcompact : CompactSpace ℝ :=
    (FiberBundle.isProperMap_proj_iff ℝ (Trivial PUnit ℝ)).mp h PUnit.unit
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) hcompact

private theorem circle_torus_compact :
    CompactSpace (TotalSpace Circle (Trivial Circle Circle)) ∧
      CompactSpace Circle ∧ CompactSpace Circle := by
  have htotal := FiberBundle.compactSpace_totalSpace Circle (Trivial Circle Circle)
  let : CompactSpace (TotalSpace Circle (Trivial Circle Circle)) := htotal
  have hbase :=
    ((FiberBundle.compactSpace_totalSpace_iff Circle (Trivial Circle Circle)).mp htotal).1
  have hmodel := FiberBundle.compactSpace_model Circle (Trivial Circle Circle) (1 : Circle)
  exact ⟨htotal, hbase, hmodel⟩

private theorem empty_model_compactness_boundary :
    CompactSpace (TotalSpace Empty (Trivial ℝ Empty)) ∧ ¬ CompactSpace ℝ := by
  constructor
  · let : IsEmpty (TotalSpace Empty (Trivial ℝ Empty)) := ⟨fun x ↦ nomatch x.snd⟩
    infer_instance
  · exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)

private theorem empty_base_compactness_boundary :
    CompactSpace (TotalSpace ℝ (Trivial Empty ℝ)) ∧ ¬ CompactSpace ℝ := by
  constructor
  · let : IsEmpty (TotalSpace ℝ (Trivial Empty ℝ)) := ⟨fun x ↦ nomatch x.proj⟩
    infer_instance
  · exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)

end Bundle.Trivial
