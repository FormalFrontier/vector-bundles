/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.FiberBundle.Connected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Order.IntermediateValue

/-!
# Preconnected strips and connected trivial bundles

The first-coordinate projection on `ℝ × ℝ` illustrates preconnected preimages for a
noninjective open map. Its fibers are continuous ranges of copies of `ℝ`.

The trivial real-line bundle over `ℝ` illustrates the projection-preimage and both
total-space conclusions on the given bundle topologies. The empty trivial bundle
over the same base illustrates that preconnectedness needs no model inhabitation.

The injective-open-map example recovers Mathlib's preconnected-preimage criterion
from the preconnected-fiber criterion under exactly the former's hypotheses.

## References

* Mathlib's real intervals, product projections and `Bundle.Trivial` APIs.
* Mathlib's `IsPreconnected.preimage_of_isOpenMap`.
-/

@[expose] public section

universe u v

open Bundle

-- The fibers of this noninjective projection are ranges of continuous real lines.
example : IsPreconnected ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) := by
  refine isPreconnected_Icc.preimage_of_isOpenMap_of_isPreconnected_fibers
    isOpenMap_fst ?_ ?_
  · intro r _
    exact ⟨(r, 0), rfl⟩
  · intro r _
    have hRange : Set.range (fun x : ℝ => (r, x)) =
        (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {r} := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        rfl
      · intro hp
        change p.1 = r at hp
        exact ⟨p.2, Prod.ext hp.symm rfl⟩
    rw [← hRange]
    exact isPreconnected_range (continuous_const.prodMk continuous_id)

-- All three conclusions use the original trivial real-line bundle over the real line.
example :
    IsPreconnected ((TotalSpace.proj (F := ℝ) (E := Trivial ℝ ℝ)) ⁻¹'
      Set.Icc (0 : ℝ) 1) ∧
    PreconnectedSpace (TotalSpace ℝ (Trivial ℝ ℝ)) ∧
    ConnectedSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := by
  exact ⟨FiberBundle.isPreconnected_preimage_proj ℝ (Trivial ℝ ℝ) isPreconnected_Icc,
    FiberBundle.preconnectedSpace_totalSpace ℝ (Trivial ℝ ℝ),
    FiberBundle.connectedSpace_totalSpace ℝ (Trivial ℝ ℝ)⟩

-- The same nonempty base interval imposes no nonemptiness requirement on the model.
example :
    IsPreconnected ((TotalSpace.proj (F := Empty) (E := Trivial ℝ Empty)) ⁻¹'
      Set.Icc (0 : ℝ) 1) ∧
    PreconnectedSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact ⟨FiberBundle.isPreconnected_preimage_proj Empty (Trivial ℝ Empty) isPreconnected_Icc,
    FiberBundle.preconnectedSpace_totalSpace Empty (Trivial ℝ Empty)⟩

-- Specialization to exactly the hypotheses of Mathlib's injective-open-map theorem.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hs : IsPreconnected s) (hinj : Function.Injective f)
    (hf : IsOpenMap f) (hsf : s ⊆ Set.range f) : IsPreconnected (f ⁻¹' s) := by
  exact hs.preimage_of_isOpenMap_of_isPreconnected_fibers hf hsf
    (fun _ _ => (Set.subsingleton_singleton.preimage hinj).isPreconnected)
