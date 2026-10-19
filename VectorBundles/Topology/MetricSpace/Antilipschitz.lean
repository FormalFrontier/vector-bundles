/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Embeddings from locally uniform antilipschitz bounds

A jointly continuous family of maps from a metric space to a pseudometric space
induces a base-preserving embedding of products if its antilipschitz constants can
be chosen uniformly on a neighborhood of each base point. The base is an arbitrary
topological space.

The proof recovers source neighborhoods from pulled-back target neighborhoods.
Along that filter, the output and the image of a fixed fiber point have the same
limit; the uniform antilipschitz bound then forces the fiber coordinate to converge.
No positivity of the antilipschitz constant is required.

## References

* Mathlib's `AntilipschitzWith` and neighborhood-filter APIs.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace Topology

universe u v w

/-- A jointly continuous family with locally uniform antilipschitz bounds gives an
embedding after pairing the output with the base point. The bound is uniform over
all fiber points, but its constant may depend on the base neighborhood. -/
theorem isEmbedding_prodMk_of_locally_antilipschitz
    {B : Type u} {F : Type v} {G : Type w}
    [TopologicalSpace B] [MetricSpace F] [PseudoMetricSpace G]
    {f : B → F → G} (hf : Continuous (fun p : B × F => f p.1 p.2))
    (hanti : ∀ b, ∃ s ∈ 𝓝 b, ∃ K : ℝ≥0, ∀ b' ∈ s, AntilipschitzWith K (f b')) :
    IsEmbedding (fun p : B × F => (p.1, f p.1 p.2)) := by
  let g : B × F → B × G := fun p => (p.1, f p.1 p.2)
  have hg : Continuous g := continuous_fst.prodMk hf
  change IsEmbedding g
  refine ⟨isInducing_iff_nhds.mpr (fun p => ?_), ?_⟩
  · apply le_antisymm hg.continuousAt.le_comap
    let l := comap g (𝓝 (g p))
    have ht : Tendsto g l (𝓝 (g p)) := tendsto_comap
    have hb : Tendsto (Prod.fst : B × F → B) l (𝓝 p.1) := ht.fst_nhds
    have hout : Tendsto (fun q : B × F => f q.1 q.2) l (𝓝 (f p.1 p.2)) :=
      ht.snd_nhds
    have hfixed : Tendsto (fun q : B × F => f q.1 p.2) l (𝓝 (f p.1 p.2)) :=
      (hf.tendsto p).comp (hb.prodMk_nhds tendsto_const_nhds)
    obtain ⟨s, hs, K, hK⟩ := hanti p.1
    have hdist : Tendsto (fun q : B × F =>
        (K : ℝ) * dist (f q.1 q.2) (f q.1 p.2)) l (𝓝 0) := by
      simpa only [dist_self, mul_zero] using (hout.dist hfixed).const_mul (K : ℝ)
    have hx : Tendsto (Prod.snd : B × F → F) l (𝓝 p.2) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hdist
      -- The bound holds along the pulled-back target filter, not just along `𝓝 p`.
      filter_upwards [hb.eventually hs] with q hq
      exact (hK q.1 hq).le_mul_dist q.2 p.2
    have hid : Tendsto (id : B × F → B × F) l (𝓝 p) := hb.prodMk_nhds hx
    simpa only [Tendsto, map_id] using hid
  · rintro ⟨b, x⟩ ⟨c, y⟩ h
    have hbc : b = c := congrArg Prod.fst h
    cases hbc
    obtain ⟨s, hs, K, hK⟩ := hanti b
    exact Prod.ext rfl ((hK b (mem_of_mem_nhds hs)).injective (congrArg Prod.snd h))

end Topology
