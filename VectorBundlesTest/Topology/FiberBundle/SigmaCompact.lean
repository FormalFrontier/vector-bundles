/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SigmaCompact
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Sigma-compactness of trivial bundles over the real line

The trivial real-line bundle over the real line is the real plane through
`Bundle.Trivial.homeomorphProd ℝ ℝ`. The first example applies
`FiberBundle.sigmaCompactSpace` to this noncompact total space and uses
`isSigmaCompact_univ` to obtain sigma-compactness of its underlying set.

The second example applies the same instance to the trivial bundle with empty model
over the same real base. No nonempty model is needed. Both examples use Mathlib's
trivial-bundle topologies and `Bundle.Trivial.fiberBundle`.
-/

@[expose] public section

open Bundle

example : IsSigmaCompact (Set.univ : Set (TotalSpace ℝ (Trivial ℝ ℝ))) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.sigmaCompactSpace ℝ (Trivial ℝ ℝ)
  exact isSigmaCompact_univ

example : IsSigmaCompact (Set.univ : Set (TotalSpace Empty (Trivial ℝ Empty))) := by
  let : SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) :=
    FiberBundle.sigmaCompactSpace Empty (Trivial ℝ Empty)
  exact isSigmaCompact_univ

/-! The reflection clients below use the same original trivial-bundle topologies and data.
The three real-plane clients apply the chart, specified-point and global characterizations
directly. Empty total spaces give cheap boundaries: an empty base cannot test the model,
and an empty model cannot test the base. -/

public theorem FiberBundle.sigmaCompact_real_model_from_closed_chart :
    IsSigmaCompact (Set.univ : Set ℝ) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.sigmaCompactSpace ℝ (Trivial ℝ ℝ)
  let : SigmaCompactSpace ℝ :=
    (Trivial.trivialization ℝ ℝ).sigmaCompactSpace_model_of_isClosed
      (FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ))
      (s := {(0 : ℝ)}) isClosed_singleton ⟨0, rfl⟩
      (by intro x hx; exact Set.mem_univ x)
  exact isSigmaCompact_univ

private theorem sigmaCompact_real_model_from_totalSpace :
    IsSigmaCompact (Set.univ : Set ℝ) := by
  let : SigmaCompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    FiberBundle.sigmaCompactSpace ℝ (Trivial ℝ ℝ)
  let : SigmaCompactSpace ℝ :=
    FiberBundle.sigmaCompactSpace_model ℝ (Trivial ℝ ℝ) (0 : ℝ)
  exact isSigmaCompact_univ

private theorem sigmaCompact_real_factors_from_totalSpace :
    IsSigmaCompact (Set.univ : Set ℝ) ∧ IsSigmaCompact (Set.univ : Set ℝ) := by
  have hfactors :=
    (FiberBundle.sigmaCompactSpace_totalSpace_iff ℝ (Trivial ℝ ℝ)).mp
      (FiberBundle.sigmaCompactSpace ℝ (Trivial ℝ ℝ))
  exact ⟨isSigmaCompact_univ_iff.mpr hfactors.1,
    isSigmaCompact_univ_iff.mpr hfactors.2⟩

private theorem sigmaCompact_empty_model_from_totalSpace :
    IsSigmaCompact (Set.univ : Set Empty) := by
  let : IsEmpty (TotalSpace Empty (Trivial ℝ Empty)) :=
    ⟨fun p ↦ Empty.elim p.snd⟩
  let : SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) := inferInstance
  let : SigmaCompactSpace Empty :=
    FiberBundle.sigmaCompactSpace_model Empty (Trivial ℝ Empty) (0 : ℝ)
  exact isSigmaCompact_univ

private theorem sigmaCompact_trivial_totalSpace_empty_base
    (F : Type*) [TopologicalSpace F] :
    IsSigmaCompact (Set.univ : Set (TotalSpace F (Trivial Empty F))) := by
  let : IsEmpty (TotalSpace F (Trivial Empty F)) := ⟨fun p ↦ Empty.elim p.proj⟩
  exact isSigmaCompact_univ

private theorem sigmaCompact_trivial_totalSpace_empty_model
    (B : Type*) [TopologicalSpace B] :
    IsSigmaCompact (Set.univ : Set (TotalSpace Empty (Trivial B Empty))) := by
  let : IsEmpty (TotalSpace Empty (Trivial B Empty)) := ⟨fun p ↦ Empty.elim p.snd⟩
  exact isSigmaCompact_univ
