/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.SeparatedMap

/-!
# Separated projections of fiber bundles

The projection of a fiber bundle with Hausdorff model fiber is a separated map.
Consequently, two sections with continuous total-space graphs have a closed equality
set. The base need not be Hausdorff, and no separation hypothesis on the entire total
space is required.

## References

* Mathlib's `IsSeparatedMap` and `IsSeparatedMap.isClosed_eqLocus` APIs.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- The projection of a fiber bundle with Hausdorff model fiber is a separated map. -/
theorem isSeparatedMap_proj
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [T2Space F] :
    IsSeparatedMap (TotalSpace.proj (F := F) (E := E)) := by
  intro x y hxy hne
  -- One chart contains the entire fibers over its base set, hence both points.
  let e := trivializationAt F E x.proj
  have hx : x ∈ e.source :=
    e.mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  have hy : y ∈ e.source := by
    apply e.mem_source.mpr
    rw [← hxy]
    exact mem_baseSet_trivializationAt F E x.proj
  have hcoord : (e x).2 ≠ (e y).2 := by
    intro h
    apply hne
    apply e.toPartialEquiv.injOn hx hy
    exact Prod.ext ((e.coe_fst hx).trans (hxy.trans (e.coe_fst hy).symm)) h
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hcoord
  refine ⟨e.source ∩ e ⁻¹' (Prod.snd ⁻¹' u),
    e.source ∩ e ⁻¹' (Prod.snd ⁻¹' v), ?_, ?_, ⟨hx, hxu⟩, ⟨hy, hyv⟩, ?_⟩
  · exact e.toOpenPartialHomeomorph.isOpen_inter_preimage (hu.preimage continuous_snd)
  · exact e.toOpenPartialHomeomorph.isOpen_inter_preimage (hv.preimage continuous_snd)
  · exact Set.disjoint_left.mpr fun z hzu hzv ↦ Set.disjoint_left.mp huv hzu.2 hzv.2

/-- Two sections with continuous total-space graphs agree on a closed set when the
model fiber is Hausdorff. -/
theorem isClosed_eq
    {B : Type uB} (F : Type uF) {E : B → Type uE}
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [T2Space F] {s t : ∀ b, E b}
    (hs : Continuous (fun b ↦ TotalSpace.mk' F b (s b)))
    (ht : Continuous (fun b ↦ TotalSpace.mk' F b (t b))) :
    IsClosed {b | s b = t b} := by
  simpa only [TotalSpace.mk_inj] using
    (IsSeparatedMap.isClosed_eqLocus hs ht (isSeparatedMap_proj F E) rfl)

end FiberBundle
