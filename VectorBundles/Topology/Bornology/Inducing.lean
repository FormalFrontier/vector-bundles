/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Maps.Basic

/-!
# Von Neumann boundedness and inducing linear maps

The preimage of a von Neumann bounded set under an inducing linear map is bounded for the
original source topology. Injectivity and continuity of the fiber operations are not needed.
The statement uses Mathlib's absorption definition of `Bornology.IsVonNBounded`.
-/

@[expose] public section

namespace Bornology

universe uκ uD uE

/-- An inducing linear map pulls von Neumann bounded sets back to bounded sets.
There is no injectivity or topological vector-space hypothesis. -/
theorem IsVonNBounded.preimage_of_isInducing
    {κ : Type uκ} [NormedDivisionRing κ]
    {D : Type uD} [AddCommGroup D] [Module κ D] [TopologicalSpace D]
    {E : Type uE} [AddCommGroup E] [Module κ E] [TopologicalSpace E]
    {s : Set E} (hs : IsVonNBounded κ s) (a : D →ₗ[κ] E)
    (ha : Topology.IsInducing a) : IsVonNBounded κ (a ⁻¹' s) := by
  intro U hU
  rw [ha.nhds_eq_comap (0 : D), a.map_zero] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  suffices h : Absorbs κ (a ⁻¹' V) (a ⁻¹' s) from h.mono_left hVU
  apply absorbs_iff_eventually_cobounded_mapsTo.2
  refine (absorbs_iff_eventually_cobounded_mapsTo.1 (hs hV)).mono ?_
  intro c hc x hx
  change a (c⁻¹ • x) ∈ V
  rw [a.map_smul]
  exact hc hx

end Bornology
