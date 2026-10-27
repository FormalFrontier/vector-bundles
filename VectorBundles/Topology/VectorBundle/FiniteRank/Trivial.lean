/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Product models of finite rank

The standard constant family with fibre `Fin n → K` over an arbitrary topological
base has a finite-rank atlas with one global chart. Its total-space topology is the
named topology `Bundle.TrivialFiniteRank.topology`, induced from the usual product
by `Bundle.TotalSpace.toProd`. This topology is not registered as an instance.

This is a product model, not a construction changing a given bundle's topology.
No agreement with another total-space topology or fixed-model bundle instance is
asserted. The fibres retain their usual function-space algebra and topology.

Only a topology on the scalar field is needed: no continuity of its operations or
norm is assumed. The rank may be zero; in that case the fibre consists of its single
zero vector, and the same construction applies without any positivity hypothesis.
-/

@[expose] public section

open Bundle Topology

universe uK uB

namespace Bundle.TrivialFiniteRank

variable (K : Type uK) (B : Type uB) (n : ℕ)
variable [TopologicalSpace K] [TopologicalSpace B]

/-- The declared product topology on the total space of the standard constant family.
It is a named topology, not a typeclass instance. -/
@[instance_reducible] def topology :
    TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
  TopologicalSpace.induced (TotalSpace.toProd B (Fin n → K)) inferInstance

/-- The product model, with its declared topology, is homeomorphic to the usual
product of the base and the standard coordinate space. -/
def homeomorphProd :
    @Homeomorph
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
      (topology K B n) inferInstance :=
  @Homeomorph.mk
    (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
    (topology K B n) (inferInstance : TopologicalSpace (B × (Fin n → K)))
    (TotalSpace.toProd B (Fin n → K))
    (by
      rw [continuous_def]
      intro s hs
      exact ⟨s, hs, rfl⟩)
    (by
      rw [continuous_def]
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      change IsOpen ((TotalSpace.toProd B (Fin n → K)).symm ⁻¹'
        ((TotalSpace.toProd B (Fin n → K)) ⁻¹' t))
      have hpre : (TotalSpace.toProd B (Fin n → K)).symm ⁻¹'
          ((TotalSpace.toProd B (Fin n → K)) ⁻¹' t) = t := by
        ext q
        change (TotalSpace.toProd B (Fin n → K)
          ((TotalSpace.toProd B (Fin n → K)).symm q) ∈ t) ↔ q ∈ t
        rw [(TotalSpace.toProd B (Fin n → K)).apply_symm_apply]
      rw [hpre]
      exact ht)

/-- The product homeomorphism preserves the base and the original coordinate vector. -/
@[simp] theorem homeomorphProd_mk (b : B) (v : Fin n → K) :
    homeomorphProd K B n (TotalSpace.mk b v) = (b, v) := rfl

/-- Inverse product coordinates give the vector in the indicated original fibre. -/
@[simp] theorem homeomorphProd_symm_pair (b : B) (v : Fin n → K) :
    (@Homeomorph.symm
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
      (topology K B n) inferInstance (homeomorphProd K B n)) (b, v) =
        @TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v := rfl

/-- The original projection is continuous for the declared product topology. -/
theorem continuous_proj :
    @Continuous (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) B
      (topology K B n) inferInstance TotalSpace.proj := by
  let : TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
    topology K B n
  exact continuous_fst.comp (homeomorphProd K B n).continuous

/-- Each fibre injection is continuous for the declared product topology. -/
theorem continuous_mk (b : B) :
    @Continuous (Fin n → K) (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
      inferInstance (topology K B n)
      (fun v : Fin n → K =>
        @TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v) := by
  let : TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
    topology K B n
  exact (homeomorphProd K B n).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The given function-space topology on each fibre is induced by its inclusion
into the product model. -/
theorem inducing_mk (b : B) :
    @IsInducing (Fin n → K) (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
      inferInstance (topology K B n)
      (fun v : Fin n → K =>
        @TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v) := by
  let : TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
    topology K B n
  have hind :
      TopologicalSpace.induced
          (fun v : Fin n → K =>
            @TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v)
          (topology K B n) =
        (inferInstance : TopologicalSpace (Fin n → K)) := by
    apply TopologicalSpace.ext
    funext s
    apply propext
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (continuous_mk K B n b).isOpen_preimage u hu
    · intro hs
      refine ⟨(TotalSpace.toProd B (Fin n → K)) ⁻¹' (Set.univ ×ˢ s), ?_, ?_⟩
      · exact ⟨Set.univ ×ˢ s, isOpen_univ.prod hs, rfl⟩
      · ext v
        change (b ∈ (Set.univ : Set B) ∧ v ∈ s) ↔ v ∈ s
        constructor
        · intro hv
          exact hv.2
        · intro hv
          exact ⟨Set.mem_univ b, hv⟩
  first
  | exact ⟨hind⟩
  | exact ⟨hind.symm⟩

/-- The global standard-coordinate chart of the declared product model. -/
def chart :
    @Trivialization B (Fin n → K)
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
      inferInstance inferInstance (topology K B n) TotalSpace.proj := by
  letI : TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
    topology K B n
  exact
    { toFun := TotalSpace.toProd B (Fin n → K)
      invFun := (TotalSpace.toProd B (Fin n → K)).symm
      source := Set.univ
      target := Set.univ ×ˢ Set.univ
      map_source' := by
        intro p hp
        exact ⟨Set.mem_univ _, Set.mem_univ _⟩
      map_target' := by
        intro q hq
        exact Set.mem_univ _
      left_inv' := by
        intro p hp
        exact (TotalSpace.toProd B (Fin n → K)).symm_apply_apply p
      right_inv' := by
        intro q hq
        exact (TotalSpace.toProd B (Fin n → K)).apply_symm_apply q
      open_source := isOpen_univ
      open_target := isOpen_univ.prod isOpen_univ
      continuousOn_toFun := (homeomorphProd K B n).continuous.continuousOn
      continuousOn_invFun := (homeomorphProd K B n).symm.continuous.continuousOn
      baseSet := Set.univ
      open_baseSet := isOpen_univ
      source_eq := rfl
      target_eq := rfl
      proj_toFun p hp := rfl }

/-- The standard chart is defined over the whole base. -/
@[simp] theorem chart_baseSet :
    @Trivialization.baseSet B (Fin n → K)
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
      inferInstance inferInstance (topology K B n) TotalSpace.proj
      (chart K B n) = Set.univ := rfl

/-- The standard chart has the whole total space as source. -/
@[simp] theorem chart_source :
    @PartialEquiv.source
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
        (topology K B n) inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
          (topology K B n) inferInstance
          (@Trivialization.toOpenPartialHomeomorph B (Fin n → K)
            (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
            inferInstance inferInstance (topology K B n) TotalSpace.proj
            (chart K B n)))) = Set.univ := rfl

/-- The standard chart reads the original base point and fibre vector. -/
@[simp] theorem chart_mk (b : B) (v : Fin n → K) :
    chart K B n (@TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v) =
      (b, v) := rfl

section Algebra

variable [Field K]

/-- The global standard chart is fibrewise linear on its base set. -/
theorem chart_isFiberwiseLinear :
    @Trivialization.IsFiberwiseLinear K inferInstance B inferInstance
      (Trivial B (Fin n → K)) (Fin n → K)
      inferInstance inferInstance (topology K B n)
      (Fin n → K) inferInstance inferInstance inferInstance (chart K B n) := by
  let : TopologicalSpace (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :=
    topology K B n
  constructor
  · intro b hb v w
    simp only [chart_mk]
  · intro b hb c v
    simp only [chart_mk]

/-- A finite-rank atlas on the declared product model over an arbitrary topological
base. The single global chart has rank `n`, including when `n = 0`. -/
def atlas :
    @FiniteRankAtlas K inferInstance inferInstance B inferInstance
      (Fin n → K) (Trivial B (Fin n → K))
      inferInstance inferInstance inferInstance (topology K B n) :=
  @FiniteRankAtlas.mk K inferInstance inferInstance B inferInstance
    (Fin n → K) (Trivial B (Fin n → K))
    inferInstance inferInstance inferInstance (topology K B n)
    Unit (fun _ => n) (fun _ => chart K B n)
    (fun _ => chart_isFiberwiseLinear K B n)
    (fun b => ⟨(), Set.mem_univ b⟩) (inducing_mk K B n)

/-- Every chart in the singleton atlas has the prescribed finite rank. -/
@[simp] theorem atlas_rank (i : Unit) :
    @FiniteRankAtlas.rank K inferInstance inferInstance B inferInstance
      (Fin n → K) (Trivial B (Fin n → K))
      inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i = n := rfl

/-- The singleton atlas uses the global standard-coordinate chart. -/
@[simp] theorem atlas_chart (i : Unit) :
    @FiniteRankAtlas.chart K inferInstance inferInstance B inferInstance
      (Fin n → K) (Trivial B (Fin n → K))
      inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i =
        chart K B n := rfl

/-- Each base point belongs to the global chart of the singleton atlas. -/
@[simp] theorem mem_atlas_chart_baseSet (i : Unit) (b : B) :
    b ∈ @Trivialization.baseSet B (Fin n → K)
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
      inferInstance inferInstance (topology K B n) TotalSpace.proj
      (@FiniteRankAtlas.chart K inferInstance inferInstance B inferInstance
        (Fin n → K) (Trivial B (Fin n → K))
        inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i) :=
  Set.mem_univ b

/-- Every total-space point lies in the chart of the singleton atlas. -/
@[simp] theorem mem_atlas_chart_source (i : Unit)
    (p : TotalSpace (Fin n → K) (Trivial B (Fin n → K))) :
    p ∈ @PartialEquiv.source
      (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
        (topology K B n) inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin n → K) (Trivial B (Fin n → K))) (B × (Fin n → K))
          (topology K B n) inferInstance
          (@Trivialization.toOpenPartialHomeomorph B (Fin n → K)
            (TotalSpace (Fin n → K) (Trivial B (Fin n → K)))
            inferInstance inferInstance (topology K B n) TotalSpace.proj
            (@FiniteRankAtlas.chart K inferInstance inferInstance B inferInstance
              (Fin n → K) (Trivial B (Fin n → K))
              inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i)))) :=
  Set.mem_univ p

/-- The atlas chart returns the original coordinates of every fibre vector. -/
@[simp] theorem atlas_chart_mk (i : Unit) (b : B) (v : Fin n → K) :
    @FiniteRankAtlas.chart K inferInstance inferInstance B inferInstance
      (Fin n → K) (Trivial B (Fin n → K))
      inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i
      (@TotalSpace.mk B (Fin n → K) (Trivial B (Fin n → K)) b v) = (b, v) := rfl

/-- Atlas fibre coordinates are the original standard coordinates. -/
@[simp] theorem atlas_coord (i : Unit) (b : B) (v : Fin n → K) :
    @FiniteRankAtlas.coord K inferInstance inferInstance B inferInstance
      (Fin n → K) (Trivial B (Fin n → K))
      inferInstance inferInstance inferInstance (topology K B n) (atlas K B n) i b v = v := rfl

omit [TopologicalSpace K] [TopologicalSpace B] in
/-- A rank-zero fibre has just its zero vector; it is not an empty fibre. -/
theorem zero_fiber_eq (b : B) (v : Trivial B (Fin 0 → K) b) : v = 0 :=
  Subsingleton.elim _ _

end Algebra
end Bundle.TrivialFiniteRank
