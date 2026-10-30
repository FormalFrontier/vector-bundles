/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Continuity from pairwise distances

Maps into independent pseudometric spaces have equivalent convergence and continuity
properties whenever their pairwise distances agree. No separation assumption is needed
on either target, and the domain topology can be arbitrary.

## References

* Mathlib's `Metric.tendsto_nhds` characterizes convergence by distances to the limit.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Metric

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [PseudoMetricSpace Y] [PseudoMetricSpace Z] {f : X → Y} {g : X → Z}

/-- Maps with equal pairwise distances converge to their respective values at a point
along the same filter simultaneously. -/
theorem tendsto_nhds_iff_of_pairwise_dist_eq
    (hdist : ∀ a b, dist (f a) (f b) = dist (g a) (g b))
    {l : Filter X} {x : X} :
    Tendsto f l (𝓝 (f x)) ↔ Tendsto g l (𝓝 (g x)) := by
  simp only [Metric.tendsto_nhds, hdist]

/-- Maps with equal pairwise distances are continuous at the same points of any
topological domain. -/
theorem continuousAt_iff_of_pairwise_dist_eq [TopologicalSpace X]
    (hdist : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) {x : X} :
    ContinuousAt f x ↔ ContinuousAt g x :=
  tendsto_nhds_iff_of_pairwise_dist_eq hdist

/-- Maps with equal pairwise distances have equivalent continuity on any topological
domain. -/
theorem continuous_iff_of_pairwise_dist_eq [TopologicalSpace X]
    (hdist : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) :
    Continuous f ↔ Continuous g := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_of_pairwise_dist_eq hdist]

end Metric
