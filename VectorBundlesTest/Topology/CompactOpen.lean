/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.CompactOpen
public import VectorBundles.Topology.FiberBundle.CoordChange
public import VectorBundles.Topology.Maps.Proper
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Compact-open images, coordinate changes and proper projections on standard spaces

The left summand of `PUnit ⊕ PUnit` is a nonempty proper compact open set. Its image
under the constant family `Homeomorph.sumComm PUnit PUnit`, parametrized by the real
line, uses local constancy of compact-open images. This constant family does not test
the sharpness of the joint-continuity hypotheses; the parameter has its usual,
nondiscrete topology.

Both joint coordinate-change theorems are applied to the canonical trivialization of
the trivial real-line bundle over the real line. These self-transitions are identities.
The real strip `ℝ ×ˢ Icc 0 1` has proper first projection by compactness and upper
hemicontinuity of its constant fibers. The sole empty-model boundary checks both images
and projection. All topologies and homeomorphisms are Mathlib's standard ones.
-/

@[expose] public section

open Set TopologicalSpace

private def leftPoint : CompactOpens (PUnit ⊕ PUnit) where
  carrier := range (Sum.inl : PUnit → PUnit ⊕ PUnit)
  isCompact' := isCompact_range continuous_inl
  isOpen' := isOpen_range_inl

private theorem isLocallyConstant_sumComm_images :
    IsLocallyConstant (fun _ : ℝ ↦
      leftPoint.map (Homeomorph.sumComm PUnit PUnit)
        (Homeomorph.sumComm PUnit PUnit).continuous
        (Homeomorph.sumComm PUnit PUnit).isOpenMap) ∧
      (leftPoint : Set (PUnit ⊕ PUnit)).Nonempty ∧
      (leftPoint : Set (PUnit ⊕ PUnit)) ≠ univ := by
  refine ⟨leftPoint.isLocallyConstant_map (fun _ : ℝ ↦ Homeomorph.sumComm PUnit PUnit)
    ((Homeomorph.sumComm PUnit PUnit).continuous.comp continuous_snd)
    ((Homeomorph.sumComm PUnit PUnit).continuous_symm.comp continuous_snd), ?_, ?_⟩
  · exact ⟨Sum.inl PUnit.unit, ⟨PUnit.unit, rfl⟩⟩
  · intro h
    have hmem : (Sum.inr PUnit.unit : PUnit ⊕ PUnit) ∈
        (leftPoint : Set (PUnit ⊕ PUnit)) := by
      rw [h]
      exact mem_univ _
    rcases hmem with ⟨x, hx⟩
    cases hx

private theorem continuous_real_coordChange :
    Continuous (fun q :
      {b : ℝ // b ∈ (Bundle.Trivial.trivialization ℝ ℝ).baseSet ∩
        (Bundle.Trivial.trivialization ℝ ℝ).baseSet} × ℝ ↦
      ((Bundle.Trivial.trivialization ℝ ℝ).coordChangeHomeomorph
        (Bundle.Trivial.trivialization ℝ ℝ) (b := q.1.val)
        q.1.prop.1 q.1.prop.2) q.2) := by
  exact Bundle.Trivialization.continuous_coordChange_uncurry
    (Bundle.Trivial.trivialization ℝ ℝ) (Bundle.Trivial.trivialization ℝ ℝ)

private theorem continuous_real_coordChange_symm :
    Continuous (fun q :
      {b : ℝ // b ∈ (Bundle.Trivial.trivialization ℝ ℝ).baseSet ∩
        (Bundle.Trivial.trivialization ℝ ℝ).baseSet} × ℝ ↦
      ((Bundle.Trivial.trivialization ℝ ℝ).coordChangeHomeomorph
        (Bundle.Trivial.trivialization ℝ ℝ) (b := q.1.val)
        q.1.prop.1 q.1.prop.2).symm q.2) := by
  exact Bundle.Trivialization.continuous_coordChangeHomeomorph_symm_uncurry
    (Bundle.Trivial.trivialization ℝ ℝ) (Bundle.Trivial.trivialization ℝ ℝ)

/-- The first projection of the closed unit strip in the real plane is proper. -/
theorem isProperMap_real_strip :
    IsProperMap (fun z : ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) ↦ z.val.1) := by
  apply Set.isProperMap_fst_of_upperHemicontinuous
  · intro b
    simpa only [mem_prod, mem_univ, true_and, Set.ofPred_mem_eq] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  · simpa only [mem_prod, mem_univ, true_and, Set.ofPred_mem_eq] using
      (UpperHemicontinuous.const : UpperHemicontinuous (fun _ : ℝ ↦ Icc (0 : ℝ) 1))

private theorem empty_model_images_and_projection :
    IsLocallyConstant (fun _ : ℝ ↦
      (⊥ : CompactOpens Empty).map (Homeomorph.refl Empty)
        (Homeomorph.refl Empty).continuous (Homeomorph.refl Empty).isOpenMap) ∧
      IsProperMap (fun z : (univ : Set (ℝ × Empty)) ↦ z.val.1) := by
  constructor
  · exact (⊥ : CompactOpens Empty).isLocallyConstant_map
      (fun _ : ℝ ↦ Homeomorph.refl Empty) continuous_snd continuous_snd
  · apply Set.isProperMap_fst_of_upperHemicontinuous
    · intro b
      exact isCompact_univ
    · exact UpperHemicontinuous.const
