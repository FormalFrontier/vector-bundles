/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.FiberBundle.Pullback
import VectorBundles.Topology.VectorBundle.Cylinder
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Cylinder charts on product real bundles

The real line product bundle over `ℝ × unitInterval` supplies the bundle
structures without a cylindrical-chart hypothesis. The chosen chart is used
uniformly at all times, with its inverse, and on closed slab restrictions.
A rank-zero product bundle over `PUnit × unitInterval` includes both endpoints.
-/

-- All fixtures and their statements are named and private.
set_option linter.privateModule false

open Bundle Set TopologicalSpace

namespace VectorBundle.CylinderExamples

private abbrev RealLine := Bundle.Trivial (ℝ × unitInterval) ℝ

private noncomputable def realLineChart (x : ℝ) : Trivialization ℝ (π ℝ RealLine) :=
  VectorBundle.cylinderTrivialization ℝ ℝ RealLine x

private noncomputable def realLineNhds (x : ℝ) : OpenNhdsOf x :=
  VectorBundle.cylinderTrivializationNhds ℝ ℝ RealLine x

private theorem realLine_uniform (x : ℝ) :
    (realLineChart x).IsLinear ℝ ∧ IsOpen (realLineNhds x : Set ℝ) ∧
      x ∈ realLineNhds x ∧
      ∀ y ∈ realLineNhds x, ∀ t : unitInterval, (y, t) ∈ (realLineChart x).baseSet := by
  refine ⟨VectorBundle.cylinderTrivialization_isLinear ℝ ℝ RealLine x,
    (realLineNhds x).isOpen, (realLineNhds x).mem, ?_⟩
  exact fun y hy t ↦ VectorBundle.mem_cylinderTrivialization_baseSet ℝ ℝ RealLine x hy t

private theorem realLine_inverse_allTime (x : ℝ) (t : unitInterval) (v : ℝ) :
    (realLineChart x).symm (x, t)
      ((realLineChart x) (⟨(x, t), v⟩ : TotalSpace ℝ RealLine)).2 = v := by
  exact (realLineChart x).symm_apply_apply_mk
    (VectorBundle.mem_cylinderTrivialization_baseSet_self ℝ ℝ RealLine x t) v

private noncomputable def realLineClosedChart (x : ℝ) (a b : unitInterval) :
    ((π ℝ RealLine) ⁻¹' ((realLineNhds x : Set ℝ) ×ˢ Icc a b)) ≃ₜ
      ((realLineNhds x : Set ℝ) ×ˢ Icc a b) × ℝ :=
  (realLineChart x).preimageHomeomorph
    (fun q hq ↦ VectorBundle.cylinderTrivializationNhds_prod_subset ℝ ℝ RealLine x
      ⟨hq.1, mem_univ q.2⟩)

private theorem realLineClosedChart_linear (x : ℝ) (a b : unitInterval)
    (q : (realLineNhds x : Set ℝ) ×ˢ Icc a b) :
    IsLinearMap ℝ (fun v : ℝ ↦
      (realLineClosedChart x a b
        ⟨(⟨q.val, v⟩ : TotalSpace ℝ RealLine), q.property⟩).2) := by
  let : (realLineChart x).IsLinear ℝ :=
    VectorBundle.cylinderTrivialization_isLinear ℝ ℝ RealLine x
  have happly (v : ℝ) :
      (realLineClosedChart x a b
        ⟨(⟨q.val, v⟩ : TotalSpace ℝ RealLine), q.property⟩).2 =
        ((realLineChart x) (⟨q.val, v⟩ : TotalSpace ℝ RealLine)).2 :=
    congrArg Prod.snd ((realLineChart x).preimageHomeomorph_apply _ _)
  simp_rw [happly]
  exact (realLineChart x).linear ℝ
    (VectorBundle.mem_cylinderTrivialization_baseSet ℝ ℝ RealLine x q.property.1 q.val.2)

private theorem realLine_slice_lift_range :
    Set.range (@Bundle.Pullback.lift (ℝ × unitInterval) ℝ RealLine
      {q : ℝ × unitInterval // q.2 = 0} Subtype.val) =
        (π ℝ RealLine) ⁻¹' {q : ℝ × unitInterval | q.2 = 0} := by
  simpa only [Subtype.range_coe_subtype] using
    (Bundle.Pullback.range_lift ℝ RealLine
      (Subtype.val : {q : ℝ × unitInterval // q.2 = 0} → ℝ × unitInterval))

private theorem realLine_slice_lift_isInducing :
    Topology.IsInducing (@Bundle.Pullback.lift (ℝ × unitInterval) ℝ RealLine
      {q : ℝ × unitInterval // q.2 = 0} Subtype.val) := by
  exact Bundle.Pullback.isInducing_lift ℝ RealLine
    (Subtype.val : {q : ℝ × unitInterval // q.2 = 0} → ℝ × unitInterval)
    Topology.IsInducing.subtypeVal (FiberBundle.continuous_proj ℝ RealLine)

private theorem realLine_slice_lift_isEmbedding :
    Topology.IsEmbedding (@Bundle.Pullback.lift (ℝ × unitInterval) ℝ RealLine
      {q : ℝ × unitInterval // q.2 = 0} Subtype.val) := by
  exact Bundle.Pullback.isEmbedding_lift ℝ RealLine
    (Subtype.val : {q : ℝ × unitInterval // q.2 = 0} → ℝ × unitInterval)
    Topology.IsEmbedding.subtypeVal (FiberBundle.continuous_proj ℝ RealLine)

private theorem realLine_slice_lift_isClosedEmbedding :
    Topology.IsClosedEmbedding (@Bundle.Pullback.lift (ℝ × unitInterval) ℝ RealLine
      {q : ℝ × unitInterval // q.2 = 0} Subtype.val) := by
  exact Bundle.Pullback.isClosedEmbedding_lift ℝ RealLine
    (Subtype.val : {q : ℝ × unitInterval // q.2 = 0} → ℝ × unitInterval)
    (isClosed_eq continuous_snd continuous_const).isClosedEmbedding_subtypeVal
    (FiberBundle.continuous_proj ℝ RealLine)

private theorem realLine_open_lift_isOpenEmbedding :
    Topology.IsOpenEmbedding (@Bundle.Pullback.lift (ℝ × unitInterval) ℝ RealLine
      {q : ℝ × unitInterval // 0 < q.1} Subtype.val) := by
  exact Bundle.Pullback.isOpenEmbedding_lift ℝ RealLine
    (Subtype.val : {q : ℝ × unitInterval // 0 < q.1} → ℝ × unitInterval)
    (isOpen_lt continuous_const continuous_fst).isOpenEmbedding_subtypeVal
    (FiberBundle.continuous_proj ℝ RealLine)

private theorem realLine_restrictions_nonvacuous :
    ((0, 0) : ℝ × unitInterval) ∈ {q : ℝ × unitInterval | q.2 = 0} ∧
      ((0, 1) : ℝ × unitInterval) ∉ {q : ℝ × unitInterval | q.2 = 0} ∧
      ((1, 0) : ℝ × unitInterval) ∈ {q : ℝ × unitInterval | 0 < q.1} ∧
      ((0, 0) : ℝ × unitInterval) ∉ {q : ℝ × unitInterval | 0 < q.1} ∧
      (1 : RealLine ((0 : ℝ), (0 : unitInterval))) ≠ 0 := by
  change (0 : unitInterval) = 0 ∧ (1 : unitInterval) ≠ 0 ∧
    (0 : ℝ) < 1 ∧ ¬ (0 : ℝ) < 0 ∧ (1 : ℝ) ≠ 0
  exact ⟨rfl, one_ne_zero, zero_lt_one, lt_irrefl _, one_ne_zero⟩

private abbrev IntervalLine := Bundle.Trivial unitInterval ℝ

private theorem interval_linear_refinement :
    ∃ e : Trivialization ℝ (π ℝ IntervalLine), e.IsLinear ℝ ∧
      Icc (0 : unitInterval) 1 ⊆ e.baseSet := by
  obtain ⟨e, he, hbase⟩ := VectorBundle.exists_linearTrivialization_unitInterval ℝ ℝ IntervalLine
  exact ⟨e, he, hbase ▸ subset_univ _⟩

private abbrev ZeroModel := Fin 0 → ℝ
private abbrev ZeroBundle := Bundle.Trivial (PUnit × unitInterval) ZeroModel

private noncomputable def zeroChart : Trivialization ZeroModel (π ZeroModel ZeroBundle) :=
  VectorBundle.cylinderTrivialization ℝ ZeroModel ZeroBundle PUnit.unit

private theorem zeroChart_global_endpoints :
    zeroChart.IsLinear ℝ ∧ zeroChart.baseSet = univ ∧
      (PUnit.unit, (0 : unitInterval)) ∈ zeroChart.baseSet ∧
      (PUnit.unit, (1 : unitInterval)) ∈ zeroChart.baseSet := by
  refine ⟨VectorBundle.cylinderTrivialization_isLinear ℝ ZeroModel ZeroBundle PUnit.unit,
    ?_, ?_, ?_⟩
  · apply eq_univ_iff_forall.mpr
    intro q
    exact VectorBundle.mem_cylinderTrivialization_baseSet_self ℝ ZeroModel ZeroBundle
      PUnit.unit q.2
  · exact VectorBundle.mem_cylinderTrivialization_baseSet_self ℝ ZeroModel ZeroBundle
      PUnit.unit 0
  · exact VectorBundle.mem_cylinderTrivialization_baseSet_self ℝ ZeroModel ZeroBundle
      PUnit.unit 1

end VectorBundle.CylinderExamples
