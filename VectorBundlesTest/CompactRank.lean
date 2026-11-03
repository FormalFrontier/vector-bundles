/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.Compactness.Compact
import VectorBundles.Topology.VectorBundle.FiniteRank.LinearEquiv

/-!
# Compact rank buckets

Compact sets admit finite covers by original chart rank buckets. For compact bases,
finite selection and reindexing retain the original fibres and charts.
-/

open Bundle Topology

universe uK uB uP uE uI

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]

example (a : FiniteRankAtlas.{_, _, _, _, uI} K P E) :
    (∀ n : ℕ, IsClopen {b : B | Module.finrank K (E b) = n}) ∧
    ∀ (S : Set B), IsCompact S →
      ∃ T : Finset a.Index,
        (S = ∅ → T = ∅) ∧
        ((fun b : B => Module.finrank K (E b)) '' S).Finite ∧
        (∀ b ∈ S, Module.finrank K (E b) ≤ T.sup a.rank) ∧
        ∀ n : ℕ,
          IsClopen {b : S | Module.finrank K (E b.1) = n} ∧
          IsCompact {b : S | Module.finrank K (E b.1) = n} ∧
          ∀ b : S, Module.finrank K (E b.1) = n →
            ∃ i ∈ T.filter (fun i => a.rank i = n), b.1 ∈ (a.chart i).baseSet := by
  classical
  have hclopen : ∀ n : ℕ, IsClopen {b : B | Module.finrank K (E b) = n} := by
    intro n
    have hopen := a.isLocallyConstant_finrank {n}
    have hcomp := a.isLocallyConstant_finrank ({n}ᶜ)
    have hlevel : (fun b : B => Module.finrank K (E b)) ⁻¹' {n} =
        {b : B | Module.finrank K (E b) = n} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [← hlevel]
    refine ⟨?_, hopen⟩
    simpa only [Set.preimage_compl, compl_compl] using hcomp.isClosed_compl
  refine ⟨hclopen, ?_⟩
  intro S hS
  have hselect : ∃ T : Finset a.Index,
      (S = ∅ → T = ∅) ∧
      ∀ b ∈ S, ∃ i ∈ T, b ∈ (a.chart i).baseSet := by
    by_cases hempty : S = ∅
    · subst S
      refine ⟨∅, fun h => rfl, ?_⟩
      intro b hb
      exact hb.elim
    · obtain ⟨T, hT⟩ := hS.elim_finite_subcover
        (fun i : a.Index => (a.chart i).baseSet)
        (fun i => (a.chart i).open_baseSet) (by
          intro b hb
          simpa only [Set.mem_iUnion] using a.cover b)
      refine ⟨T, fun h => (hempty h).elim, ?_⟩
      intro b hb
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hb)
      obtain ⟨hiT, hbi⟩ := Set.mem_iUnion.mp hi
      exact ⟨i, hiT, hbi⟩
  obtain ⟨T, hEmpty, hT⟩ := hselect
  refine ⟨T, hEmpty, ?_, ?_, ?_⟩
  · refine (T.finite_toSet.image a.rank).subset ?_
    rintro n ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := hT b hb
    exact ⟨i, hi, (a.finrank_eq_rank i b hbi).symm⟩
  · intro b hb
    obtain ⟨i, hi, hbi⟩ := hT b hb
    calc
      Module.finrank K (E b) = a.rank i := a.finrank_eq_rank i b hbi
      _ ≤ T.sup a.rank := Finset.le_sup hi
  · intro n
    have hrel : IsClopen {b : S | Module.finrank K (E b.1) = n} :=
      (hclopen n).preimage continuous_subtype_val
    let : CompactSpace S := isCompact_iff_compactSpace.mp hS
    refine ⟨hrel, hrel.isClosed.isCompact, ?_⟩
    intro b hbn
    obtain ⟨i, hi, hbi⟩ := hT b.1 b.2
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hbi⟩
    exact (a.finrank_eq_rank i b.1 hbi).symm.trans hbn

example (a : FiniteRankAtlas.{_, _, _, _, uI} K P E) [CompactSpace B] :
    ∃ (T : Finset a.Index)
      (hcover : ∀ b : B, ∃ j : {i : a.Index // i ∈ T},
        b ∈ (a.chart j.1).baseSet),
      ((Set.univ : Set B) = ∅ → T = ∅) ∧
      let aT := a.reindex (fun j : {i : a.Index // i ∈ T} => j.1) hcover;
      Finite aT.Index ∧
        ∀ j : {i : a.Index // i ∈ T},
          aT.rank j = a.rank j.1 ∧
          aT.chart j = a.chart j.1 ∧
          ∀ (b : B) (v : E b), aT.coord j b v = a.coord j.1 b v := by
  classical
  have hselect : ∃ T : Finset a.Index,
      ((Set.univ : Set B) = ∅ → T = ∅) ∧
      ∀ b : B, ∃ i ∈ T, b ∈ (a.chart i).baseSet := by
    by_cases hempty : (Set.univ : Set B) = ∅
    · refine ⟨∅, fun h => rfl, ?_⟩
      intro b
      have hb : b ∈ (∅ : Set B) := hempty ▸ Set.mem_univ b
      exact hb.elim
    · obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
        (fun i : a.Index => (a.chart i).baseSet)
        (fun i => (a.chart i).open_baseSet) (by
          intro b hb
          simpa only [Set.mem_iUnion] using a.cover b)
      refine ⟨T, fun h => (hempty h).elim, ?_⟩
      have hselected : ∀ b ∈ (Set.univ : Set B),
          ∃ i ∈ T, b ∈ (a.chart i).baseSet := by
        intro b hb
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hb)
        obtain ⟨hiT, hbi⟩ := Set.mem_iUnion.mp hi
        exact ⟨i, hiT, hbi⟩
      intro b
      exact hselected b (Set.mem_univ b)
  obtain ⟨T, hEmpty, hT⟩ := hselect
  let J := {i : a.Index // i ∈ T}
  let f : J → a.Index := Subtype.val
  let : Fintype J := inferInstance
  have hcover : ∀ b : B, ∃ j : J, b ∈ (a.chart (f j)).baseSet := by
    intro b
    obtain ⟨i, hi, hbi⟩ := hT b
    exact ⟨⟨i, hi⟩, hbi⟩
  let aT := a.reindex f hcover
  have hfinite : Finite aT.Index := by
    change Finite J
    infer_instance
  refine ⟨T, hcover, hEmpty, hfinite, ?_⟩
  intro j
  exact ⟨a.reindex_rank f hcover j, a.reindex_chart f hcover j,
    fun b v => a.reindex_coord f hcover j b v⟩
