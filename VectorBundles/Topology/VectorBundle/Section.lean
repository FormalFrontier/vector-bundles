/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Scalar multiplication of continuous sections

A continuous scalar function times a continuous section is continuous in the original
vector-bundle total topology. Only the model fiber is normed; no continuity of scalar
multiplication on the individual fibers is assumed separately.

## Credits

The section-closure argument is due to Formal Frontier Agents. It checks continuity in a
preferred linear trivialization using Mathlib's `FiberBundle.continuousAt_section`.
The underlying bundle constructions are due to Nicolò Cavalleri, Sébastien Gouëzel,
Heather Macbeth and Floris van Doorn.
-/

@[expose] public section

open Bundle

namespace VectorBundle

universe uκ uB uF uE

/-- A continuous scalar function times a continuous section is a continuous section,
with respect to the given fiber and total-space topologies and bundle structures. -/
theorem continuous_smul_section {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
    {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle κ F E]
    {c : B → κ} {s : ∀ b, E b}
    (hc : Continuous c) (hs : Continuous (fun b ↦ TotalSpace.mk' F b (s b))) :
    Continuous (fun b ↦ TotalSpace.mk' F b (c b • s b)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [FiberBundle.continuousAt_section]
  have hs' := (FiberBundle.continuousAt_section F x₀).mp hs.continuousAt
  apply (hc.continuousAt.smul hs').congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F E x₀)] with x hx
  exact ((trivializationAt F E x₀).linear κ hx).map_smul (c x) (s x)

end VectorBundle
