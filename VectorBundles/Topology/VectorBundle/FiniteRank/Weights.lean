/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Topology.Compactness.Compact
public import VectorBundles.Topology.FiniteNormalWeights
public import VectorBundles.Topology.FiniteScalarWeights
public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Finite chart covers and subordinate weights

On a compact base, a finite-rank atlas admits a finite family of its original charts,
indexed injectively by `Fin m`, whose base sets cover the base. On a normal base this
family admits nonnegative continuous real weights with sum one everywhere and closed
supports contained in the corresponding chart base sets.

For an `RCLike` scalar field, casting these real weights gives a family without a
common zero. The existing scalar dual coefficients are continuous, have the same
closed supports, and satisfy the reconstruction normalization. The scalar field and
topology in this specialization are both the ones supplied by `RCLike`.

The original chart index type need not be finite or inhabited. Chart ranks may vary
and may be zero; no selected chart or coordinate is removed according to its rank.
The finite family is chosen before any weighted coordinate map is formed.

## References

* Mathlib's compactness and finite-type enumeration APIs.
* The finite normal-space weights and finite scalar dual-coefficient APIs of this library.
-/

@[expose] public section

open Bundle Topology
open scoped BigOperators

universe uK uB uE uP uI

namespace Bundle.FiniteRankAtlas

section Field

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)

/-- A finite family of original charts covers a compact base. The enumeration has
no repeated indices and does not impose any condition on the selected ranks. -/
theorem exists_finite_chart_cover [CompactSpace B] :
    ∃ (m : ℕ) (j : Fin m → A.Index), Function.Injective j ∧
      ∀ b : B, ∃ i : Fin m, b ∈ (A.chart (j i)).baseSet := by
  classical
  have hcover : (Set.univ : Set B) ⊆ ⋃ i : A.Index, (A.chart i).baseSet := by
    intro b _
    exact Set.mem_iUnion.mpr (A.cover b)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : A.Index => (A.chart i).baseSet)
    (fun i => (A.chart i).open_baseSet) hcover
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => (e i).1, ?_, ?_⟩
  · intro i k hik
    exact e.injective (Subtype.ext hik)
  · intro b
    obtain ⟨i, hi, hbi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ b))
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    exact (congrArg (fun t : s => b ∈ (A.chart t.val).baseSet)
      (e.apply_symm_apply ⟨i, hi⟩)).mpr hbi

/-- A finite family of original charts on a compact normal base admits nonnegative
continuous real weights, with sum one at every base point and closed supports in the
selected chart base sets. The original scalar field needs only its given topology. -/
theorem exists_finite_continuous_weights [CompactSpace B] [NormalSpace B] :
    ∃ (m : ℕ) (j : Fin m → A.Index) (w : Fin m → B → ℝ),
      Function.Injective j ∧
      (∀ b : B, ∃ i : Fin m, b ∈ (A.chart (j i)).baseSet) ∧
      (∀ i, Continuous (w i)) ∧
      (∀ i b, 0 ≤ w i b) ∧
      (∀ b, ∑ i, w i b = 1) ∧
      (∀ i, tsupport (w i) ⊆ (A.chart (j i)).baseSet) := by
  obtain ⟨m, j, hj, hcover⟩ := A.exists_finite_chart_cover
  have hU (i : Fin m) : IsOpen (A.chart (j i)).baseSet :=
    (A.chart (j i)).open_baseSet
  have hcover' : (Set.univ : Set B) ⊆ ⋃ i : Fin m, (A.chart (j i)).baseSet := by
    intro b _
    exact Set.mem_iUnion.mpr (hcover b)
  obtain ⟨w, hw, hw₀, _, hsum, hsupp⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set B)).exists_finite_continuous_partition_of_unity
      hU hcover'
  exact ⟨m, j, w, hj, hcover, hw, hw₀, fun b => hsum b (Set.mem_univ b), hsupp⟩

end Field

section RCLike

variable {K : Type uK} [RCLike K]
variable {B : Type uB} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)

/-- Casting subordinate real weights to an `RCLike` field gives continuous scalar
weights without a common zero. Their scalar dual coefficients have the same closed
supports and their products with the weights sum to one. Only the weights themselves
are cast; the dual coefficients are formed in the scalar field. -/
theorem exists_finite_continuous_dual_weights :
    ∃ (m : ℕ) (j : Fin m → A.Index) (w₀ : Fin m → B → ℝ),
      Function.Injective j ∧
      (∀ b : B, ∃ i : Fin m, b ∈ (A.chart (j i)).baseSet) ∧
      (∀ i, Continuous (w₀ i)) ∧
      (∀ i b, 0 ≤ w₀ i b) ∧
      (∀ b, ∑ i, w₀ i b = 1) ∧
      (∀ i, tsupport (w₀ i) ⊆ (A.chart (j i)).baseSet) ∧
      let w : Fin m → B → K := fun i b => (w₀ i b : K)
      let a : Fin m → B → K := FiniteScalarWeights.dualCoeff Finset.univ w
      (∀ b, ∃ i ∈ Finset.univ, w i b ≠ 0) ∧
      (∀ i, Continuous (w i)) ∧
      (∀ i, tsupport (w i) = tsupport (w₀ i)) ∧
      (∀ i, tsupport (w i) ⊆ (A.chart (j i)).baseSet) ∧
      (∀ i, Continuous (a i)) ∧
      (∀ i, tsupport (a i) = tsupport (w i)) ∧
      (∀ i, tsupport (a i) ⊆ (A.chart (j i)).baseSet) ∧
      (∀ b, ∑ i, a i b * w i b = 1) := by
  classical
  obtain ⟨m, j, w₀, hj, hU, hw₀, hnonneg, hsum, hsupp⟩ :=
    A.exists_finite_continuous_weights
  let w : Fin m → B → K := fun i b => (w₀ i b : K)
  let a : Fin m → B → K := FiniteScalarWeights.dualCoeff Finset.univ w
  have hcover (b : B) : ∃ i ∈ Finset.univ, w i b ≠ 0 := by
    have hex : ∃ i : Fin m, w₀ i b ≠ 0 := by
      by_contra h
      have hall (i : Fin m) : w₀ i b = 0 := by
        by_contra hi
        exact h ⟨i, hi⟩
      have hzero : (∑ i, w₀ i b) = 0 :=
        Finset.sum_eq_zero (fun i _ => hall i)
      exact (zero_ne_one : (0 : ℝ) ≠ 1) (hzero.symm.trans (hsum b))
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, RCLike.ofReal_ne_zero.mpr hi⟩
  have hw (i : Fin m) : Continuous (w i) :=
    RCLike.continuous_ofReal.comp (hw₀ i)
  have hsuppw (i : Fin m) : tsupport (w i) = tsupport (w₀ i) := by
    simpa only [w, tsupport, Function.comp_def] using
      congrArg (closure : Set B → Set B)
        (Function.support_comp_eq (RCLike.ofReal : ℝ → K)
          RCLike.ofReal_eq_zero (w₀ i))
  have hsubw (i : Fin m) : tsupport (w i) ⊆ (A.chart (j i)).baseSet :=
    (hsuppw i).subset.trans (hsupp i)
  have ha (i : Fin m) : Continuous (a i) :=
    FiniteScalarWeights.continuous_dualCoeff Finset.univ w
      (fun i _ => hw i) hcover i (Finset.mem_univ i)
  have hsuppa (i : Fin m) : tsupport (a i) = tsupport (w i) :=
    FiniteScalarWeights.tsupport_dualCoeff Finset.univ w hcover i
  have hsumaw (b : B) : (∑ i, a i b * w i b) = 1 :=
    FiniteScalarWeights.sum_dualCoeff_mul Finset.univ w hcover b
  refine ⟨m, j, w₀, hj, hU, hw₀, hnonneg, hsum, hsupp, ?_⟩
  exact ⟨hcover, hw, hsuppw, hsubw, ha, hsuppa,
    fun i => (hsuppa i).subset.trans (hsubw i), hsumaw⟩

end RCLike

end Bundle.FiniteRankAtlas
