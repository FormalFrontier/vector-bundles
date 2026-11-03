/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Von Neumann boundedness and inducing linear maps

A linear map inducing the topology on its domain reflects von Neumann boundedness.
Injectivity and continuity of the algebraic operations are not required.
-/

@[expose] public section

open Set Filter
open scoped Topology Pointwise

universe uL uE uF

namespace Bornology

/-- A set is von Neumann bounded if its image under a topology-inducing linear map is
von Neumann bounded. The map need not be injective, and the module topologies need not
make addition or scalar multiplication continuous. -/
theorem IsVonNBounded.of_image_of_isInducing
    {L : Type uL} {E : Type uE} {F : Type uF} [NormedDivisionRing L]
    [AddCommMonoid E] [AddCommMonoid F] [Module L E] [Module L F]
    [TopologicalSpace E] [TopologicalSpace F]
    (f : E →ₗ[L] F) (hf : Topology.IsInducing f) {s : Set E}
    (hs : IsVonNBounded L (f '' s)) : IsVonNBounded L s := by
  intro U hU
  have hU' : U ∈ comap f (𝓝 (0 : F)) := by
    simpa only [hf.nhds_eq_comap (0 : E), map_zero] using hU
  rcases hU' with ⟨V, hV, hVU⟩
  refine absorbs_iff_eventually_cobounded_mapsTo.mpr ?_
  refine (absorbs_iff_eventually_cobounded_mapsTo.mp (hs hV)).mono ?_
  intro c hc x hx
  apply hVU
  change f (c⁻¹ • x) ∈ V
  rw [f.map_smul]
  exact hc ⟨x, hx, rfl⟩

end Bornology
