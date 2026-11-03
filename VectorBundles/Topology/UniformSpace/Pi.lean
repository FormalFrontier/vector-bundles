/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Total boundedness in products of uniform spaces

A subset of a dependent product is totally bounded for the product uniformity if and only if
all its coordinate images are totally bounded. The proof uses Mathlib's characterization of
total boundedness by ultrafilters and its coordinatewise criterion for Cauchy filters.
-/

@[expose] public section

open Filter

universe uι uα

/-- A subset of a dependent product of uniform spaces is totally bounded if and only if
its image under each coordinate projection is totally bounded. -/
theorem totallyBounded_pi_iff
    {ι : Type uι} {α : ι → Type uα} [∀ i, UniformSpace (α i)]
    (s : Set (∀ i, α i)) :
    TotallyBounded s ↔ ∀ i, TotallyBounded ((fun f : ∀ j, α j => f i) '' s) := by
  constructor
  · intro hs i
    exact hs.image (Pi.uniformContinuous_proj α i)
  · intro hs
    refine totallyBounded_iff_ultrafilter.2 ?_
    intro f hf
    apply (cauchy_pi_iff' α).2
    intro i
    exact (Ultrafilter.map (fun g : ∀ j, α j => g i) f).cauchy_of_totallyBounded
      (hs i) (by
        simpa only [Ultrafilter.coe_map, Filter.map_principal] using
          (Filter.map_mono (m := fun g : ∀ j, α j => g i) hf))
