/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Continuity from local fiber coordinates

For charts preserving a projection to a base space, continuity of a map into the total space
can be tested by continuity of its base map and its model coordinates. The open base sets need
only cover the image of the map in the base, and the projection itself need not be continuous.
-/

public section

universe uX uE uT uJ uM

/-- Given a continuous base map and open base sets covering its image, a map to the total space
is continuous if and only if its model coordinate in every chart is continuous on the corresponding
preimage subtype. The charts preserve the base coordinate; no continuity of the projection itself
is assumed. -/
theorem continuous_iff_continuous_chart_snd
    {X : Type uX} {E : Type uE} {T : Type uT} {J : Sort uJ}
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace T]
    {M : J → Type uM} [∀ j, TopologicalSpace (M j)]
    {p : E → X} {W : J → Set X}
    (chart : ∀ j, (p ⁻¹' W j) ≃ₜ (W j × M j))
    (chart_base : ∀ j (u : p ⁻¹' W j), ((chart j u).1 : X) = p u.val)
    {f : T → E} (hbase : Continuous (p ∘ f))
    (hopen : ∀ j, IsOpen (W j))
    (hcover : ∀ t : T, ∃ j, p (f t) ∈ W j) :
    Continuous f ↔ ∀ j, Continuous
      (fun t : {t : T // p (f t) ∈ W j} => (chart j ⟨f t.val, t.property⟩).2) := by
  constructor
  · intro hf j
    have hlift : Continuous
        (fun t : {t : T // p (f t) ∈ W j} =>
          (⟨f t.val, t.property⟩ : p ⁻¹' W j)) :=
      (hf.comp continuous_subtype_val).subtype_mk (fun t => t.property)
    exact ((chart j).continuous_toFun.comp hlift).snd
  · intro hcoord
    apply continuous_of_cover_nhds (s := fun j => {t : T | p (f t) ∈ W j})
    · intro t
      obtain ⟨j, hj⟩ := hcover t
      exact ⟨j, ((hopen j).preimage hbase).mem_nhds hj⟩
    · intro j
      apply continuousOn_iff_continuous_domRestrict.mpr
      -- Recover the whole chart map from its base and model coordinates.
      have hfst : Continuous
          (fun t : {t : T // p (f t) ∈ W j} =>
            (chart j ⟨f t.val, t.property⟩).1) := by
        have hb : Continuous
            (fun t : {t : T // p (f t) ∈ W j} =>
              (⟨p (f t.val), t.property⟩ : W j)) :=
          (hbase.comp continuous_subtype_val).subtype_mk (fun t => t.property)
        apply hb.congr
        intro t
        exact Subtype.ext (chart_base j ⟨f t.val, t.property⟩).symm
      have hchart : Continuous
          (fun t : {t : T // p (f t) ∈ W j} =>
            chart j ⟨f t.val, t.property⟩) :=
        hfst.prodMk (hcoord j)
      have hlift : Continuous
          (fun t : {t : T // p (f t) ∈ W j} =>
            (⟨f t.val, t.property⟩ : p ⁻¹' W j)) :=
        (chart j).comp_continuous_iff.mp hchart
      exact continuous_subtype_val.comp hlift
