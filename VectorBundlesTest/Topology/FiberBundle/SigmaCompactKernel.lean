/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SigmaCompact
public import Mathlib.Topology.Compactness.NhdsKer
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Sigma-compact trivial bundles with open neighborhood kernels

The real line with its upper set topology has singleton kernels `Ici c`. These kernels
are compact and open, and those at `-n` cover the model. Any two open upper sets are
comparable by inclusion, so intersections of compact opens are compact.

The trivial bundle over the usual real line with this model directly uses both
`FiberBundle.sigmaCompactSpace_of_open_nhdsKer_cover` and
`FiberBundle.sigmaCompactSpace_of_countable_open_compact_cover`. Two further direct
applications use the empty model over the same base. All four applications retain
Mathlib's trivial-bundle topologies and bundle structure.

## References

* Mathlib's `Topology.WithUpperSet`, `Topology.IsUpperSet.nhdsKer_singleton`,
  `IsUpperSet.total` and `IsCompact.nhdsKer` supply the model input APIs.
* Mathlib's `Bundle.Trivial` supplies the bundle data and topology.
-/

@[expose] public section

open Bundle Set Topology.WithUpperSet

private theorem isOpen_nhdsKer_singleton_withUpperSet_real (c : Topology.WithUpperSet ℝ) :
    IsOpen (nhdsKer ({c} : Set (Topology.WithUpperSet ℝ))) := by
  rw [Topology.IsUpperSet.nhdsKer_singleton]
  exact Topology.IsUpperSet.isOpen_iff_isUpperSet.mpr (isUpperSet_Ici c)

private theorem open_nhdsKer_cover_withUpperSet_real :
    ∀ x : Topology.WithUpperSet ℝ, ∃ c : Topology.WithUpperSet ℝ,
      IsOpen (nhdsKer ({c} : Set (Topology.WithUpperSet ℝ))) ∧ x ∈ nhdsKer {c} := by
  intro x
  exact ⟨x, isOpen_nhdsKer_singleton_withUpperSet_real x,
    subset_nhdsKer (mem_singleton x)⟩

private def compactOpenCover_withUpperSet_real (n : ℕ) :
    TopologicalSpace.CompactOpens (Topology.WithUpperSet ℝ) :=
  ⟨⟨nhdsKer ({toUpperSet (-(n : ℝ))} : Set (Topology.WithUpperSet ℝ)),
    isCompact_singleton.nhdsKer⟩, isOpen_nhdsKer_singleton_withUpperSet_real _⟩

private theorem iUnion_compactOpenCover_withUpperSet_real :
    (⋃ n, (compactOpenCover_withUpperSet_real n : Set (Topology.WithUpperSet ℝ))) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (-ofUpperSet x)
  refine mem_iUnion.mpr ⟨n, ?_⟩
  change x ∈ nhdsKer ({toUpperSet (-(n : ℝ))} : Set (Topology.WithUpperSet ℝ))
  rw [Topology.IsUpperSet.nhdsKer_singleton]
  change -(n : ℝ) ≤ ofUpperSet x
  simpa only [neg_neg] using neg_le_neg (le_of_lt hn)

private theorem sigmaCompactSpace_withUpperSet_real :
    SigmaCompactSpace (Topology.WithUpperSet ℝ) := by
  apply isSigmaCompact_univ_iff.mp
  exact ⟨fun n ↦ (compactOpenCover_withUpperSet_real n : Set (Topology.WithUpperSet ℝ)),
    fun n ↦ (compactOpenCover_withUpperSet_real n).isCompact,
    iUnion_compactOpenCover_withUpperSet_real⟩

private theorem quasiSeparatedSpace_withUpperSet_real :
    QuasiSeparatedSpace (Topology.WithUpperSet ℝ) := by
  constructor
  intro U V hU hUc hV hVc
  have hU' : IsUpperSet (toUpperSet ⁻¹' U : Set ℝ) :=
    (Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hU).preimage
      (toUpperSetOrderIso (α := ℝ)).monotone
  have hV' : IsUpperSet (toUpperSet ⁻¹' V : Set ℝ) :=
    (Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hV).preimage
      (toUpperSetOrderIso (α := ℝ)).monotone
  rcases hU'.total hV' with hUV | hVU
  · have hUV' : U ⊆ V :=
      (toUpperSet (α := ℝ)).surjective.preimage_subset_preimage_iff.mp hUV
    simpa only [inter_eq_left.mpr hUV'] using hUc
  · have hVU' : V ⊆ U :=
      (toUpperSet (α := ℝ)).surjective.preimage_subset_preimage_iff.mp hVU
    simpa only [inter_eq_right.mpr hVU'] using hVc

namespace Bundle.Trivial

/-- The trivial bundle over the usual real line with the upper-set real model has
sigma-compact total space, by the open neighborhood-kernel criterion. -/
theorem sigmaCompactSpace_real_upperSet_totalSpace :
    SigmaCompactSpace (TotalSpace (Topology.WithUpperSet ℝ)
      (Trivial ℝ (Topology.WithUpperSet ℝ))) := by
  let : SigmaCompactSpace (Topology.WithUpperSet ℝ) := sigmaCompactSpace_withUpperSet_real
  let : QuasiSeparatedSpace (Topology.WithUpperSet ℝ) := quasiSeparatedSpace_withUpperSet_real
  exact FiberBundle.sigmaCompactSpace_of_open_nhdsKer_cover
    (Topology.WithUpperSet ℝ) (Trivial ℝ (Topology.WithUpperSet ℝ))
    open_nhdsKer_cover_withUpperSet_real

/-- The open neighborhood-kernel criterion permits an empty model over the usual real line. -/
theorem sigmaCompactSpace_real_empty_totalSpace :
    SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact FiberBundle.sigmaCompactSpace_of_open_nhdsKer_cover Empty (Trivial ℝ Empty)
    (fun x ↦ Empty.elim x)

/-- The trivial bundle over the usual real line with the upper-set real model has
sigma-compact total space, by its countable compact-open kernel cover. -/
theorem sigmaCompactSpace_real_upperSet_totalSpace_of_countable_open_compact_cover :
    SigmaCompactSpace (TotalSpace (Topology.WithUpperSet ℝ)
      (Trivial ℝ (Topology.WithUpperSet ℝ))) := by
  let : QuasiSeparatedSpace (Topology.WithUpperSet ℝ) := quasiSeparatedSpace_withUpperSet_real
  exact FiberBundle.sigmaCompactSpace_of_countable_open_compact_cover
    (Topology.WithUpperSet ℝ) (Trivial ℝ (Topology.WithUpperSet ℝ))
    compactOpenCover_withUpperSet_real iUnion_compactOpenCover_withUpperSet_real

/-- The countable compact-open-cover criterion permits an empty model over the usual real line. -/
theorem sigmaCompactSpace_real_empty_totalSpace_of_countable_open_compact_cover :
    SigmaCompactSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  refine FiberBundle.sigmaCompactSpace_of_countable_open_compact_cover
    Empty (Trivial ℝ Empty) (fun _ ↦ ⊥) ?_
  apply Set.eq_univ_of_forall
  intro x
  exact Empty.elim x

end Bundle.Trivial
