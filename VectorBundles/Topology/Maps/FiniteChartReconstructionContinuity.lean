/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.LinearAlgebra.WeightedCoordinates
public import VectorBundles.Topology.ContinuousMap.WeightedExtension
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.ContinuousOn

/-!
# Continuity of finite chart reconstruction

Finite chart reconstruction is jointly continuous in the base point and the full
product of model coordinates when its coefficients are continuous and supported
in their chart domains. The domains need not be open: it suffices that their
interiors cover the base.

The fibre modules are the given equality subtypes of the original total space,
with their canonical subtype topologies. The proof takes finite sums only in a
fixed model, extends weighted transition maps using
`ContinuousMap.smulExtend`, and returns to the original total space through a
chart. In particular it needs neither continuity of the projection nor continuous
operations on the original fibres, and makes no separation assumption.
-/

@[expose] public section

open Set
open scoped BigOperators Topology

universe uR uX uT uI uG

namespace LinearMap

variable {R : Type uR} [CommSemiring R]
  {X : Type uX} {T : Type uT} {I : Type uI} {G : I → Type uG} {p : T → X}
  [∀ x, AddCommMonoid {t : T // p t = x}]
  [∀ x, Module R {t : T // p t = x}]
  [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]

variable (U : I → Set X)
  (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[R] {t : T // p t = x})

private theorem chart_symm_apply_eq (j : I) (x : X) (hx : x ∈ U j)
    (u : {t : T // p t = x}) (hu : p u.val ∈ U j) :
    (c j (p u.val) hu).symm ⟨u.val, rfl⟩ = (c j x hx).symm u := by
  rcases u with ⟨t, ht⟩
  cases ht
  rfl

-- Keep the fibrewise sum identity separate from the topological argument. This
-- avoids unfolding the reconstruction's linear-map sum through local aliases.
open Classical in
private theorem chart_finiteChartReconstruction_eq (j : I) (x : X) (hx : x ∈ U j)
    (s : Finset I) (a : I → R) (z : ∀ i, G i) :
    c j x hx (∑ i ∈ s, if hi : x ∈ U i then
      a i • (c j x hx).symm (c i x hi (z i)) else 0) =
      finiteChartReconstruction U c x (s.filter (fun i => x ∈ U i)) a
        (fun _ hi => (Finset.mem_filter.mp hi).2) z := by
  classical
  rw [finiteChartReconstruction_filter_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ U i
  · simp only [dite_eq_left hi, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  · simp only [dite_eq_right hi, map_zero]

variable [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace T]
  [∀ i, TopologicalSpace (G i)]

omit [TopologicalSpace R] in
private theorem continuous_chartTransition {E : Type*} [TopologicalSpace E]
    (i j : I) (q : E → X) (v : E → G i)
    (hqi : ∀ z, q z ∈ U i) (hqj : ∀ z, q z ∈ U j)
    (hPhi : Continuous (fun z : U i × G i =>
      (c i z.1.val z.1.property z.2).val))
    (hSigma : Continuous (fun t : {t : T // p t ∈ U j} =>
      (c j (p t.val) t.property).symm ⟨t.val, rfl⟩))
    (hq : Continuous q) (hv : Continuous v) :
    Continuous (fun z => (c j (q z) (hqj z)).symm
      (c i (q z) (hqi z) (v z))) := by
  let t : E → T := fun z => (c i (q z) (hqi z) (v z)).val
  have ht : Continuous t := hPhi.comp ((hq.subtype_mk hqi).prodMk hv)
  have hpt (z : E) : p (t z) = q z :=
    (c i (q z) (hqi z) (v z)).property
  let k : E → {t : T // p t ∈ U j} :=
    fun z => ⟨t z, (hpt z).symm ▸ hqj z⟩
  have hk : Continuous k := ht.subtype_mk (fun z => (hpt z).symm ▸ hqj z)
  apply (hSigma.comp hk).congr
  intro z
  exact chart_symm_apply_eq U c j (q z) (hqj z)
    (c i (q z) (hqi z) (v z)) (k z).property

variable [∀ i, ContinuousAdd (G i)] [∀ i, ContinuousSMul R (G i)]

-- The fixed-chart calculation has its own proof boundary: the global argument
-- below only glues these restrictions using the interior cover.
open Classical in
private theorem continuous_finiteChartReconstruction_chart
    (s : Finset I) (a : I → X → R) (j : I)
    (hPhi : ∀ i, Continuous (fun z : U i × G i =>
      (c i z.1.val z.1.property z.2).val))
    (hSigma : Continuous (fun t : {t : T // p t ∈ U j} =>
      (c j (p t.val) t.property).symm ⟨t.val, rfl⟩))
    (ha_cont : ∀ i ∈ s, Continuous (a i))
    (ha_support : ∀ i ∈ s, tsupport (a i) ⊆ U i) :
    Continuous (fun z : U j × (∀ i, G i) =>
      (finiteChartReconstruction U c z.1.val (s.filter (fun i => z.1.val ∈ U i))
        (fun i => a i z.1.val) (fun _ hi => (Finset.mem_filter.mp hi).2) z.2).val) := by
  classical
  let D := U j × (∀ i, G i)
  let q : D → X := fun z => z.1.val
  have hq : Continuous q := continuous_subtype_val.comp continuous_fst
  -- All sums in this local argument take values in the single model `G j`.
  let b : I → D → G j := fun i z =>
    if hi : q z ∈ U i then
      a i (q z) • (c j (q z) z.1.property).symm (c i (q z) hi (z.2 i))
    else 0
  have hb : ∀ i ∈ s, Continuous (b i) := by
    intro i hi
    let A : Set D := {z | q z ∈ U i}
    let g : A → G j := fun z =>
      (c j (q z.val) z.val.1.property).symm
        (c i (q z.val) z.property (z.val.2 i))
    have hg : Continuous g :=
      continuous_chartTransition U c i j (fun z : A => q z.val)
        (fun z : A => z.val.2 i) (fun z => z.property)
        (fun z => z.val.1.property) (hPhi i) hSigma
        (hq.comp continuous_subtype_val)
        ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))
    let w : C(D, R) := ⟨fun z => a i (q z), (ha_cont i hi).comp hq⟩
    have hsupp : closure {z : D | w z ≠ 0} ⊆ A := by
      intro z hz
      exact ha_support i hi (tsupport_comp_subset_preimage (a i) hq hz)
    have he := (w.smulExtend hsupp ⟨g, hg⟩).continuous
    apply he.congr
    intro z
    by_cases hz : q z ∈ U i
    · rw [ContinuousMap.smulExtend_apply_of_mem _ _ _ z hz]
      simp only [b, dite_eq_left hz]
      rfl
    · rw [ContinuousMap.smulExtend_apply_of_notMem _ _ _ z hz]
      simp only [b, dite_eq_right hz]
  have hsum : Continuous (fun z : D => ∑ i ∈ s, b i z) :=
    continuous_finsetSum s hb
  have hreturn : Continuous (fun z : D =>
      (c j (q z) z.1.property (∑ i ∈ s, b i z)).val) :=
    (hPhi j).comp (continuous_fst.prodMk hsum)
  apply hreturn.congr
  intro z
  exact congrArg (Subtype.val : {t : T // p t = q z} → T)
    (chart_finiteChartReconstruction_eq U c j (q z) z.1.property s
      (fun i => a i (q z)) z.2)

open Classical in
/-- Finite supported chart reconstruction is jointly continuous into the original
total space. Only the model additions and joint scalar actions must be continuous;
the chart domains may be arbitrary subsets whose interiors cover the base. -/
theorem continuous_finiteChartReconstruction (s : Finset I) (a : I → X → R)
    (hU : ∀ x, ∃ j : I, x ∈ interior (U j))
    (hPhi : ∀ i, Continuous (fun z : U i × G i =>
      (c i z.1.val z.1.property z.2).val))
    (hSigma : ∀ i, Continuous (fun t : {t : T // p t ∈ U i} =>
      (c i (p t.val) t.property).symm ⟨t.val, rfl⟩))
    (ha_cont : ∀ i ∈ s, Continuous (a i))
    (ha_support : ∀ i ∈ s, tsupport (a i) ⊆ U i) :
    Continuous (fun z : X × (∀ i, G i) =>
      (finiteChartReconstruction U c z.1 (s.filter (fun i => z.1 ∈ U i))
        (fun i => a i z.1) (fun _ hi => (Finset.mem_filter.mp hi).2) z.2).val) := by
  classical
  let r : X × (∀ i, G i) → T := fun z =>
    (finiteChartReconstruction U c z.1 (s.filter (fun i => z.1 ∈ U i))
      (fun i => a i z.1) (fun _ hi => (Finset.mem_filter.mp hi).2) z.2).val
  change Continuous r
  let A : I → Set (X × (∀ i, G i)) := fun j => {y | y.1 ∈ U j}
  refine continuous_of_cover_nhds (f := r) (s := A) ?_ ?_
  · intro z
    obtain ⟨j, hj⟩ := hU z.1
    refine ⟨j, ?_⟩
    have hopen : IsOpen {y : X × (∀ i, G i) | y.1 ∈ interior (U j)} :=
      isOpen_interior.preimage continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds hj)
    intro y hy
    change y.1 ∈ U j
    exact interior_subset (show y.1 ∈ interior (U j) from hy)
  · intro j
    -- Separate the chart map from the map restricting the global domain to it.
    -- The dependent reconstruction expressions are then compared pointwise.
    let g : U j × (∀ i, G i) → T := fun y =>
      (finiteChartReconstruction U c y.1.val (s.filter (fun i => y.1.val ∈ U i))
        (fun i => a i y.1.val) (fun _ hi => (Finset.mem_filter.mp hi).2) y.2).val
    have hg : Continuous g :=
      continuous_finiteChartReconstruction_chart
        (R := R) (X := X) (T := T) (I := I) (G := G) (p := p)
        U c s a j hPhi (hSigma j) ha_cont ha_support
    let k : A j → U j × (∀ i, G i) :=
      fun y => (⟨y.val.1, y.property⟩, y.val.2)
    have hbase : Continuous (fun y : A j => y.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have hcoords : Continuous (fun y : A j => y.val.2) :=
      continuous_snd.comp continuous_subtype_val
    have hchartBase : Continuous (fun y : A j =>
        (⟨y.val.1, y.property⟩ : U j)) :=
      hbase.subtype_mk (fun y : A j => y.property)
    have hk : Continuous k := hchartBase.prodMk hcoords
    have hres : Continuous ((A j).domRestrict r) := by
      apply (hg.comp hk).congr
      intro y
      rfl
    exact (continuousOn_iff_continuous_domRestrict (f := r) (s := A j)).mpr hres

end LinearMap
