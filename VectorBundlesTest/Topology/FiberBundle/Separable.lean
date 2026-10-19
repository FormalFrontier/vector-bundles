/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.Separable.Basic
import VectorBundles.Topology.FiberBundle.Separable
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Separable real planes and trivial bundles

The noninjective first-coordinate projection on `ℝ × ℝ` has separable fibers:
each fiber is the range of a continuous map from `ℝ`. This proves separability of
the plane by the whole-codomain criterion and ambient separability of the strip
above `Set.Icc (0 : ℝ) 1` by the set-preimage criterion. For the latter, only the
target interval's ambient separability is taken from separability of `ℝ`; neither
fiber argument uses separability of the plane.

The usual trivial real-line bundle over `ℝ` has separable total space. The trivial
bundle with empty model over the same nonempty base also has separable total space.
Both statements retain the given trivial-bundle topologies.

For an injective open map into a separable space, singleton preimages are countable,
so the separable-fiber criterion recovers separability of the domain.

## References

* Mathlib's `TopologicalSpace.isSeparable_range`,
  `TopologicalSpace.IsSeparable.of_separableSpace` and `Bundle.Trivial` APIs.
* Mathlib's `IsOpenMap.separableSpace_of_injective`, `Set.Subsingleton.preimage`
  and `Set.Countable.isSeparable` APIs.
* `VectorBundlesTest.Topology.FiberBundle.Connected` for the real-fiber
  parametrization shared by the two projection examples here.
-/

@[expose] public section

universe u v

open Bundle TopologicalSpace

-- Each fiber is shown separable as a continuous range, not as a subset of a separable plane.
private theorem isSeparable_fst_fiber (y : ℝ) :
    TopologicalSpace.IsSeparable ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {y}) := by
  have hRange : Set.range (fun t : ℝ => (y, t)) =
      (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {y} := by
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      rfl
    · intro hp
      change p.1 = y at hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [← hRange]
  exact isSeparable_range (continuous_const.prodMk continuous_id)

example : SeparableSpace (ℝ × ℝ) := by
  exact IsOpenMap.separableSpace_of_isSeparable_fibers
    (f := (Prod.fst : ℝ × ℝ → ℝ)) isOpenMap_fst isSeparable_fst_fiber

-- Only the target interval is obtained from a global separability instance.
example : TopologicalSpace.IsSeparable
    ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) := by
  have hs : TopologicalSpace.IsSeparable (Set.Icc (0 : ℝ) 1) :=
    TopologicalSpace.IsSeparable.of_separableSpace (Set.Icc (0 : ℝ) 1)
  exact hs.preimage_of_isOpenMap_of_isSeparable_fibers isOpenMap_fst isSeparable_fst_fiber

-- The original trivial real-line bundle over the real line.
example : SeparableSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := by
  exact FiberBundle.separableSpace_totalSpace ℝ (Trivial ℝ ℝ)

-- The same nonempty base, with empty model and the original trivial-bundle topology.
example : SeparableSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact FiberBundle.separableSpace_totalSpace Empty (Trivial ℝ Empty)

-- Exactly the hypotheses of Mathlib's separability theorem for injective open maps.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace Y] {f : X → Y} (h : IsOpenMap f) (h' : Function.Injective f) :
    SeparableSpace X := by
  exact h.separableSpace_of_isSeparable_fibers
    (fun _ => (Set.subsingleton_singleton.preimage h').countable.isSeparable)
