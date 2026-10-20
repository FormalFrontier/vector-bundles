/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Compact-open images in families of homeomorphisms

A compact open set has locally constant image under a family of homeomorphisms
whose forward and inverse evaluations are jointly continuous. The parameter,
source and target spaces are arbitrary topological spaces.

The proof uses Mathlib's compact-open topology on continuous maps. At a fixed
parameter, compactness and openness give one image inclusion nearby; applying
the same argument to the inverse family gives the reverse inclusion. No local
compactness or separation assumption is needed.

## References

* Mathlib contributors, `Mathlib.Topology.CompactOpen`: continuity of currying
  and compact-to-open neighborhoods in the compact-open topology.
* Mathlib contributors, `Mathlib.Topology.Sets.Compacts`: compact open sets
  and their images under continuous open maps.
-/

@[expose] public section

universe uT uF uG

open Set Filter
open scoped Topology

namespace TopologicalSpace.CompactOpens

variable {T : Type uT} {F : Type uF} {G : Type uG}
  [TopologicalSpace T] [TopologicalSpace F] [TopologicalSpace G]

private theorem eventually_mapsTo_of_continuous_uncurry (f : T → F → G)
    (h : Continuous (Function.uncurry f)) {t : T} {K : Set F} {V : Set G}
    (hK : IsCompact K) (hV : IsOpen V) (hf : MapsTo (f t) K V) :
    ∀ᶠ t' in 𝓝 t, MapsTo (f t') K V := by
  let f' : T → C(F, G) := fun t' ↦
    ⟨f t', h.comp (continuous_const.prodMk continuous_id)⟩
  have hf' : Continuous f' :=
    ContinuousMap.continuous_of_continuous_uncurry f' h
  exact hf'.continuousAt.eventually
    (ContinuousMap.eventually_mapsTo (f := f' t) hK hV hf)

/-- The image of a compact open set is locally constant in a family of
homeomorphisms with jointly continuous forward and inverse evaluations. -/
theorem isLocallyConstant_map (U : CompactOpens F) (e : T → (F ≃ₜ G))
    (hforward : Continuous (fun p : T × F ↦ e p.1 p.2))
    (hinverse : Continuous (fun p : T × G ↦ (e p.1).symm p.2)) :
    IsLocallyConstant (fun t ↦ U.map (e t) (e t).continuous (e t).isOpenMap) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ ↦ ?_
  let V : CompactOpens G := U.map (e t₀) (e t₀).continuous (e t₀).isOpenMap
  have hV : (V : Set G) = e t₀ '' (U : Set F) :=
    coe_map (e t₀).continuous (e t₀).isOpenMap U
  have hforward₀ : MapsTo (e t₀) (U : Set F) (V : Set G) :=
    mapsTo_iff_image_subset.mpr hV.symm.subset
  have hinverse₀ : MapsTo (e t₀).symm (V : Set G) (U : Set F) := by
    rw [hV]
    rintro y ⟨x, hx, rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using hx
  have hforward' : ∀ᶠ t in 𝓝 t₀, MapsTo (e t) (U : Set F) (V : Set G) :=
    eventually_mapsTo_of_continuous_uncurry (fun t x ↦ e t x)
      hforward U.isCompact V.isOpen hforward₀
  have hinverse' : ∀ᶠ t in 𝓝 t₀, MapsTo (e t).symm (V : Set G) (U : Set F) :=
    eventually_mapsTo_of_continuous_uncurry (fun t y ↦ (e t).symm y)
      hinverse V.isCompact U.isOpen hinverse₀
  filter_upwards [hforward', hinverse'] with t htforward htinverse
  change U.map (e t) (e t).continuous (e t).isOpenMap = V
  apply CompactOpens.ext
  rw [coe_map]
  refine Subset.antisymm (mapsTo_iff_image_subset.mp htforward) ?_
  intro y hy
  exact ⟨(e t).symm y, htinverse hy, (e t).apply_symm_apply y⟩

end TopologicalSpace.CompactOpens
