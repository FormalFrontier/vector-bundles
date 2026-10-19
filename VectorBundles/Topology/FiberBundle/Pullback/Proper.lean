/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import VectorBundles.Topology.FiberBundle.Pullback

/-!
# Properness of pullback lifts

A proper map of bases induces a proper canonical lift from the pullback total space
when the original bundle projection is continuous. The source carries the canonical
pullback topology and the target retains its given total-space topology. No topology
on the model fiber or on the individual fibers, and no local triviality, is required.

The theorem `Bundle.Pullback.isProperMap_lift` uses Mathlib's `IsProperMap`, without
separation or nonemptiness assumptions. Its proof lifts an ultrafilter limit first
to the new base and then to the compatible-pair description of the pullback total space.

## References

* Mathlib's `Mathlib.Topology.Maps.Proper.Basic`, by Anatole Dedecker and Etienne Marion,
  supplies `isProperMap_iff_ultrafilter` and `IsProperMap.ultrafilter_le_nhds_of_tendsto`.
* Mathlib's `Mathlib.Topology.FiberBundle.Constructions`, by Nicolò Cavalleri,
  Sébastien Gouëzel, Heather Macbeth and Floris van Doorn, supplies the canonical
  pullback total-space topology and its continuity and inducing-map APIs.
* `VectorBundles.Topology.FiberBundle.Pullback` supplies
  `Bundle.Pullback.homeomorphProdSubtype` and its inverse projection and lift equations.
-/

@[expose] public section

open Bundle

universe uA uB uF uE

namespace Bundle.Pullback

/-- A proper base map induces a proper canonical pullback lift when the original
projection is continuous. -/
theorem isProperMap_lift {A : Type uA} {B : Type uB}
    (F : Type uF) (E : B → Type uE) (f : A → B)
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
    (hf : IsProperMap f) (hπ : Continuous (π F E)) :
    IsProperMap (@Bundle.Pullback.lift B F E A f) := by
  refine isProperMap_iff_ultrafilter.mpr ⟨_root_.Pullback.continuous_lift F E f, ?_⟩
  intro U e he
  have hbase : Filter.Tendsto f (U.map (π F (f *ᵖ E))) (nhds e.proj) := by
    rw [_root_.Ultrafilter.coe_map, Filter.tendsto_map'_iff]
    exact (hπ.tendsto e).comp he
  obtain ⟨a, ha, hUa⟩ := hf.ultrafilter_le_nhds_of_tendsto hbase
  let p : {p : A × TotalSpace F E // f p.1 = p.2.proj} := ⟨(a, e), ha⟩
  refine ⟨(homeomorphProdSubtype F E f).symm p,
    lift_homeomorphProdSubtype_symm F E f p, ?_⟩
  have hproj : Filter.Tendsto (π F (f *ᵖ E)) (U : Filter _) (nhds a) := by
    apply Filter.tendsto_iff_comap.mpr
    apply Filter.map_le_iff_le_comap.mp
    simpa only [_root_.Ultrafilter.coe_map] using hUa
  -- The canonical pullback topology detects convergence through both projections.
  apply Filter.tendsto_id'.mp
  apply (inducing_pullbackTotalSpaceEmbedding F E f).tendsto_nhds_iff.mpr
  change Filter.Tendsto
    (fun z : TotalSpace F (f *ᵖ E) ↦ (z.proj, Bundle.Pullback.lift f z))
    (U : Filter _) (nhds
      (((homeomorphProdSubtype F E f).symm p).proj,
        Bundle.Pullback.lift f ((homeomorphProdSubtype F E f).symm p)))
  rw [homeomorphProdSubtype_symm_proj, lift_homeomorphProdSubtype_symm]
  exact hproj.prodMk_nhds he

end Bundle.Pullback
