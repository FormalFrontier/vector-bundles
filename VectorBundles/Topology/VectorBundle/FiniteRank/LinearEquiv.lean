/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Basic
public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Linear coordinate equivalences on chart fibres

On the base set of a finite-rank chart, its coordinate linear map is a linear
equivalence from the original fibre to the chart's standard finite-dimensional model.
Its inverse gives exactly the original total-space point specified by inverse
coordinates. No fibre operations or topologies are changed.

Atlas coverage and Mathlib's finite-module transport show that every original fibre
is finitely generated over the scalar field. The chart ranks may vary without a
global bound.
-/

@[expose] public section

open Bundle Topology

universe uK uB uE uP

namespace Bundle.FiniteRankAtlas

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas K P E)

/-- Chart coordinates distinguish vectors in every fibre over the chart base set. -/
theorem coord_injective (i : A.Index) {b : B} (hb : b ∈ (A.chart i).baseSet) :
    Function.Injective (A.coord i b) :=
  ((A.linear i).linearMap_bijective hb).1

/-- Every standard coordinate vector is realized by a vector in the original fibre. -/
theorem coord_surjective (i : A.Index) {b : B} (hb : b ∈ (A.chart i).baseSet) :
    Function.Surjective (A.coord i b) :=
  ((A.linear i).linearMap_bijective hb).2

/-- The coordinate linear map is bijective on every fibre in its chart domain. -/
theorem coordLinearMap_bijective (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) : Function.Bijective (A.coordLinearMap i hb) :=
  (A.linear i).linearMap_bijective hb

/-- A chart identifies each original fibre over its base set linearly with its own
standard finite-dimensional coordinate space. -/
noncomputable def coordLinearEquiv (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) : E b ≃ₗ[K] (Fin (A.rank i) → K) :=
  (A.linear i).linearEquiv hb

/-- The coordinate equivalence has the original coordinate linear map as its forward map. -/
@[simp] theorem coordLinearEquiv_toLinearMap (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) :
    (A.coordLinearEquiv i hb).toLinearMap = A.coordLinearMap i hb := rfl

/-- The coordinate equivalence evaluates to the original chart coordinate. -/
@[simp] theorem coordLinearEquiv_apply (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    A.coordLinearEquiv i hb v = A.coord i b v := rfl

/-- The original chart of a fibre vector consists of its original base point and
its coordinate linear equivalence. -/
theorem chart_mk_eq_coordLinearEquiv (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    A.chart i (TotalSpace.mk b v) = (b, A.coordLinearEquiv i hb v) := by
  apply Prod.ext
  · exact A.chart_proj i (TotalSpace.mk b v) ((A.mk_mem_source_iff i b v).mpr hb)
  · rfl

/-- Applying the coordinate equivalence's inverse to original chart coordinates
recovers the original fibre vector. -/
@[simp] theorem coordLinearEquiv_symm_coord (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (v : E b) :
    (A.coordLinearEquiv i hb).symm (A.chart i (TotalSpace.mk b v)).2 = v :=
  (A.coordLinearEquiv i hb).symm_apply_apply v

/-- Original chart coordinates recover the input of the inverse coordinate equivalence. -/
@[simp] theorem coord_coordLinearEquiv_symm (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (w : Fin (A.rank i) → K) :
    (A.chart i (TotalSpace.mk b ((A.coordLinearEquiv i hb).symm w))).2 = w :=
  (A.coordLinearEquiv i hb).apply_symm_apply w

/-- The inverse linear equivalence is exactly inverse coordinates in the original
total space, not merely an abstract inverse between the fibre and its model. -/
@[simp] theorem invCoord_eq_mk_coordLinearEquiv_symm (i : A.Index) {b : B}
    (hb : b ∈ (A.chart i).baseSet) (w : Fin (A.rank i) → K) :
    A.invCoord i ⟨b, hb⟩ w = TotalSpace.mk b ((A.coordLinearEquiv i hb).symm w) :=
  ((A.linear i).mk_linearEquiv_symm hb w).symm

universe uI

/-- Each original fibre of a finite-rank atlas is finitely generated over the scalar field. -/
theorem moduleFinite_fiber (A : FiniteRankAtlas.{_, _, _, _, uI} K P E) (b : B) :
    Module.Finite K (E b) := by
  obtain ⟨i, hb⟩ := A.exists_mem_baseSet b
  exact Module.Finite.of_surjective (A.coordLinearEquiv i hb).symm.toLinearMap
    (A.coordLinearEquiv i hb).symm.surjective

/-- The finrank of a fibre in a chart domain is the rank of that chart. -/
theorem finrank_eq_rank (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    (i : A.Index) (b : B) (hb : b ∈ (A.chart i).baseSet) :
    Module.finrank K (E b) = A.rank i :=
  (A.coordLinearEquiv i hb).finrank_eq.trans (Module.finrank_fin_fun K)

/-- In a constant-finrank family, a chart containing a base point has that finrank. -/
theorem rank_eq_of_mem (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    (n : ℕ) (hn : ∀ b, Module.finrank K (E b) = n)
    (i : A.Index) (b : B) (hb : b ∈ (A.chart i).baseSet) : A.rank i = n :=
  (A.finrank_eq_rank i b hb).symm.trans (hn b)

/-- In a constant-finrank family, every chart with a nonempty base set has that rank. -/
theorem rank_eq_of_nonempty_baseSet (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    (n : ℕ) (hn : ∀ b, Module.finrank K (E b) = n)
    (i : A.Index) (h : (A.chart i).baseSet.Nonempty) : A.rank i = n := by
  obtain ⟨b, hb⟩ := h
  exact A.rank_eq_of_mem n hn i b hb

/-- A chart of rank different from the constant fibre finrank has empty base set. -/
theorem baseSet_eq_empty_of_rank_ne (A : FiniteRankAtlas.{_, _, _, _, uI} K P E)
    (n : ℕ) (hn : ∀ b, Module.finrank K (E b) = n)
    (i : A.Index) (h : A.rank i ≠ n) : (A.chart i).baseSet = ∅ := by
  ext b
  constructor
  · intro hb
    exact h (A.rank_eq_of_mem n hn i b hb)
  · intro hb
    exact hb.elim

end Bundle.FiniteRankAtlas
