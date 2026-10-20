/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Paracompactness under continuous retracts and proper maps

A continuous retract of a paracompact space is paracompact. The ambient space and
its retract may belong to different universes, and neither separation nor
nonemptiness assumptions are needed.

An open cover of the retract pulls back along the retraction to an open cover of
the ambient space. Mathlib's `precise_refinement` gives a locally finite open
refinement indexed by the original cover, even when its index type belongs to a
different universe. Pulling this refinement back along the continuous section
preserves local finiteness; the left-inverse identity gives the required
refinement of the original cover.

Proper maps also reflect paracompactness: a space admitting a proper map to a
paracompact space is paracompact. No surjectivity, separation, or nonemptiness
assumptions are needed.

## References

* Reid Barton, Yury Kudryashov, and Mathlib contributors,
  [`Mathlib.Topology.Compactness.Paracompact`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Paracompact.lean):
  paracompactness and precise locally finite refinements.
-/

@[expose] public section

universe uX uY

/-- A space admitting a proper map to a paracompact space is paracompact, without
surjectivity, separation, or nonemptiness assumptions. -/
theorem IsProperMap.paracompactSpace
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) [ParacompactSpace Y] : ParacompactSpace X := by
  classical
  constructor
  intro α s hsopen hscover
  have hfinite (y : Y) :
      ∃ a : Finset α, f ⁻¹' {y} ⊆ ⋃ i ∈ a, s i := by
    apply (hf.isCompact_preimage (isCompact_singleton : IsCompact ({y} : Set Y))).elim_finite_subcover
      s hsopen
    rw [hscover]
    exact Set.subset_univ _
  choose A hA using hfinite
  let W : Y → Set Y := fun y => Set.kernImage f (⋃ i ∈ A y, s i)
  have hWopen (y : Y) : IsOpen (W y) :=
    (isClosedMap_iff_kernImage.mp hf.isClosedMap)
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => hsopen i)
  have hWcover : ⋃ y, W y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    exact (Set.subset_kernImage_iff.mpr (hA y)) (by simp)
  have hpre (y : Y) : f ⁻¹' W y ⊆ ⋃ i ∈ A y, s i :=
    Set.subset_kernImage_iff.mp (fun _ hx => hx)
  obtain ⟨v, hvopen, hvcover, hvfinite, hvsub⟩ :=
    precise_refinement W hWopen hWcover
  let t : α → Set X := fun i => s i ∩ ⋃ (y : Y) (_ : i ∈ A y), f ⁻¹' v y
  have htopen (i : α) : IsOpen (t i) :=
    (hsopen i).inter
      (isOpen_iUnion fun y => isOpen_iUnion fun _ => (hvopen y).preimage hf.continuous)
  have htcover : ⋃ i, t i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxcover : f x ∈ ⋃ y, v y := by
      rw [hvcover]
      exact Set.mem_univ _
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hxcover
    have hxW : x ∈ f ⁻¹' W y := hvsub y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hpre y hxW)
    obtain ⟨hiA, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr
      ⟨i, hxi, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hiA, hy⟩⟩⟩
  have htfinite : LocallyFinite t := by
    have hvpre : LocallyFinite (fun y => f ⁻¹' v y) :=
      hvfinite.preimage_continuous hf.continuous
    intro x
    obtain ⟨n, hnx, hnfinite⟩ := hvpre x
    refine ⟨n, hnx, (hnfinite.biUnion (fun y _ => (A y).finite_toSet)).subset ?_⟩
    intro i hi
    obtain ⟨z, hzt, hzn⟩ := hi
    obtain ⟨_, hzv⟩ := hzt
    obtain ⟨y, hzv⟩ := Set.mem_iUnion.mp hzv
    obtain ⟨hiy, hzy⟩ := Set.mem_iUnion.mp hzv
    exact Set.mem_iUnion.mpr
      ⟨y, Set.mem_iUnion.mpr ⟨⟨z, hzy, hzn⟩, hiy⟩⟩
  refine ⟨α, t, htopen, htcover, htfinite, ?_⟩
  intro i
  exact ⟨i, Set.inter_subset_left⟩

/-- A continuous retract of a paracompact space is paracompact, without separation
or nonemptiness assumptions. -/
theorem ParacompactSpace.of_continuous_leftInverse
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    [ParacompactSpace X] {r : X → Y} {j : Y → X}
    (hr : Continuous r) (hj : Continuous j) (hjr : Function.LeftInverse r j) :
    ParacompactSpace Y := by
  constructor
  intro α s hsopen hscover
  obtain ⟨t, htopen, htcover, htfinite, htrefine⟩ :=
    precise_refinement (fun a => r ⁻¹' s a) (fun a => (hsopen a).preimage hr)
      (by rw [← Set.preimage_iUnion, hscover, Set.preimage_univ])
  refine ⟨α, (fun a => j ⁻¹' t a), (fun a => (htopen a).preimage hj), ?_,
    htfinite.preimage_continuous hj, ?_⟩
  · rw [← Set.preimage_iUnion, htcover, Set.preimage_univ]
  · intro a
    refine ⟨a, ?_⟩
    intro y hy
    have hmem : r (j y) ∈ s a := htrefine a hy
    simpa only [hjr y] using hmem
