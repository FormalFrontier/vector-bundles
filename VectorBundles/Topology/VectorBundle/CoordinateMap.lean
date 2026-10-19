/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import VectorBundles.Topology.Algebra.Module.FiniteDimensionalOperator

/-!
# Linear maps in bundle coordinates and linear atlases

A continuous total-space map given by algebraic linear maps on the fibers has jointly
continuous evaluations in any pair of linear trivializations. If the source model is
finite dimensional and has the module topology, the resulting family of continuous linear
maps between the fixed models is continuous in the topology of bounded convergence. For
normed models this is their given operator norm topology.

The coordinate expression uses `Bundle.Trivialization.linearMapAt` and
`Bundle.Trivialization.symmₗ`, with their zero extensions outside the chart domains.
Continuity is asserted only on the intersection of the two base sets. The fibers need not
be normed, and the field need not be complete. The target model only needs to be a topological
vector space; it need not be normed, finite dimensional or have the module topology. No
hypothesis on the base beyond its topology is required.

For a finite-dimensional normed model with the module topology, the coordinate changes
between two linear trivializations are continuous in the operator norm topology.
`VectorBundle.of_isLinear` therefore equips a given fiber bundle with a vector-bundle mixin
when every chart in its chosen atlas is fiberwise linear. The model norm, fiber and total-space
topologies, fiber modules and chosen atlas are unchanged.

## Implementation notes

The joint evaluation result uses only the total-space topologies and the linearity of the
two trivializations; it does not require a choice of fiber-bundle data. The source and target
bases may differ, and the fiber maps may cover any common base map. Thus it applies to
trivializations from any given vector-bundle atlases with those same total-space topologies.
The fixed-model operators use the given model topologies. Their continuity follows from
`IsModuleTopology.continuous_of_linearMap`, and continuity of their family follows from
`continuousWithinAt_clm_apply_of_isModuleTopology`. The coordinate-change specialization
uses the identity total-space map, so it does not require a vector-bundle mixin in advance.

## References

The coordinate expressions and chart-continuity argument use Mathlib's vector-bundle and
fiber-bundle APIs by Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Patrick Massot and
Floris van Doorn, and its module-topology API by Kevin Buzzard and Will Sawin.
The linear-atlas criterion corresponds to the linear local charts in Allen Hatcher,
*Vector Bundles and K-Theory*, version 2.2 (November 2017), §1.1, printed pp. 4–6.
-/

public section

open Bundle Set

universe uκ uB uC uF uG uE uE'

namespace Bundle.Trivialization

section Evaluation

variable {κ : Type uκ} [Semiring κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [TopologicalSpace F] [AddCommMonoid F] [Module κ F]
  {G : Type uG} [TopologicalSpace G] [AddCommMonoid G] [Module κ G]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {C : Type uC} [TopologicalSpace C]
  {E' : C → Type uE'} [∀ c, AddCommMonoid (E' c)] [∀ c, Module κ (E' c)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]

/-- A continuous total-space map given by algebraic linear maps covering `f` has jointly
continuous evaluations in linear trivializations where both charts are defined. The bases
are independent, and no separate continuity hypothesis on `f` is needed. -/
theorem continuousOn_linearMapAt_comp_apply_over
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (f : B → C) (φ : ∀ b, E b →ₗ[κ] E' (f b))
    (hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G (f p.proj) (φ p.proj p.snd))) :
    ContinuousOn (fun p : B × F ↦
      e'.linearMapAt κ (f p.1) (φ p.1 (e.symmₗ κ p.1 p.2)))
      ((e.baseSet ∩ f ⁻¹' e'.baseSet) ×ˢ (univ : Set F)) := by
  have hs : ContinuousOn (fun p : B × F ↦
      TotalSpace.mk' F p.1 (e.symmₗ κ p.1 p.2))
      ((e.baseSet ∩ f ⁻¹' e'.baseSet) ×ˢ (univ : Set F)) := by
    refine (e.continuousOn_symm.mono (fun p hp ↦ ⟨hp.1.1, hp.2⟩)).congr ?_
    intro p hp
    change TotalSpace.mk' F p.1 (e.symmₗ κ p.1 p.2) =
      TotalSpace.mk' F p.1 (e.symm p.1 p.2)
    exact congrArg (TotalSpace.mk' F p.1) (e.symmₗ_apply (R := κ) hp.1.1 p.2)
  have hc := (e'.continuousOn.comp (hφ.comp_continuousOn hs)
    (fun p hp ↦ e'.mem_source.mpr hp.1.2)).snd
  refine hc.congr ?_
  intro p hp
  change e'.linearMapAt κ (f p.1) (φ p.1 (e.symmₗ κ p.1 p.2)) =
    (e' (TotalSpace.mk' G (f p.1) (φ p.1 (e.symmₗ κ p.1 p.2)))).2
  exact congrFun (e'.coe_linearMapAt_of_mem (R := κ) hp.1.2)
    (φ p.1 (e.symmₗ κ p.1 p.2))

end Evaluation

section IdentityBase

variable {κ : Type uκ} [Semiring κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [TopologicalSpace F] [AddCommMonoid F] [Module κ F]
  {G : Type uG} [TopologicalSpace G] [AddCommMonoid G] [Module κ G]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {E' : B → Type uE'} [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]

/-- A continuous total-space map given by algebraic linear maps on the fibers has jointly
continuous evaluations in linear trivializations on the overlap of their base sets.
This is `continuousOn_linearMapAt_comp_apply_over` for the identity base map. -/
theorem continuousOn_linearMapAt_comp_apply
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b)
    (hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (φ p.proj p.snd))) :
    ContinuousOn (fun p : B × F ↦
      e'.linearMapAt κ p.1 (φ p.1 (e.symmₗ κ p.1 p.2)))
      ((e.baseSet ∩ e'.baseSet) ×ˢ (univ : Set F)) :=
  continuousOn_linearMapAt_comp_apply_over e e' id φ hφ

end IdentityBase

section Operators

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [AddCommGroup F] [Module κ F] [TopologicalSpace F] [FiniteDimensional κ F]
  {G : Type uG} [AddCommGroup G] [Module κ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul κ G]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {E' : B → Type uE'} [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]

/-- In linear trivializations, a continuous total-space map given by algebraic linear maps
on the fibers yields a continuous family of fixed-model operators, when the source model is
finite dimensional and has the module topology. The operators carry the topology of bounded
convergence, which for normed models is their given operator norm topology. No completeness
hypothesis is needed. -/
theorem continuousOn_linearMapAt_comp_of_isModuleTopology [IsModuleTopology κ F]
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b)
    (hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (φ p.proj p.snd))) :
    ContinuousOn (fun b ↦
      (⟨(e'.linearMapAt κ b).comp ((φ b).comp (e.symmₗ κ b)),
        IsModuleTopology.continuous_of_linearMap _⟩ : F →L[κ] G))
      (e.baseSet ∩ e'.baseSet) := by
  intro b hb
  apply continuousWithinAt_clm_apply_of_isModuleTopology.mpr
  intro v
  exact (continuousOn_linearMapAt_comp_apply e e' φ hφ).comp
    (continuousOn_id.prodMk (continuousOn_const (c := v)))
    (fun c hc ↦ ⟨hc, mem_univ v⟩) b hb

end Operators

section CoordinateChanges

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  [FiniteDimensional κ F] [IsModuleTopology κ F]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- Coordinate changes between two fiberwise linear trivializations are continuous in the
operator norm topology on their overlap, when the model is finite dimensional and has the
module topology. No fiber-bundle or vector-bundle structure is required. -/
theorem continuousOn_coordChangeL_of_isModuleTopology
    (e e' : Trivialization F (π F E)) [e.IsLinear κ] [e'.IsLinear κ] :
    ContinuousOn (fun b ↦ (e.coordChangeL κ e' b : F →L[κ] F))
      (e.baseSet ∩ e'.baseSet) := by
  have h := continuousOn_linearMapAt_comp_of_isModuleTopology e e'
    (fun b ↦ (LinearMap.id : E b →ₗ[κ] E b)) continuous_id
  refine h.congr ?_
  intro b hb
  ext v
  change e.coordChangeL κ e' b v = e'.linearMapAt κ b (e.symmₗ κ b v)
  rw [e.coordChangeL_apply e' hb, e.symmₗ_apply (R := κ) hb.1]
  exact (congrFun (e'.coe_linearMapAt_of_mem (R := κ) hb.2) (e.symm b v)).symm

end CoordinateChanges

end Bundle.Trivialization

namespace VectorBundle

/-- A fiber bundle whose chosen atlas is fiberwise linear is a vector bundle, provided its
original normed model is finite dimensional and has the module topology. This retains the
chosen atlas and all given topologies and module structures; continuity of the operator-valued
coordinate changes is a conclusion. No scalar completeness or norms on the fibers are needed. -/
theorem of_isLinear
    {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
    [FiniteDimensional κ F] [IsModuleTopology κ F]
    {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    (hlinear : ∀ e ∈ trivializationAtlas F E, e.IsLinear κ) :
    VectorBundle κ F E := by
  refine
    { trivialization_linear' := ?_
      continuousOn_coordChange' := ?_ }
  · intro e he
    exact hlinear e he.out
  · intro e e' he he'
    let : e.IsLinear κ := hlinear e he.out
    let : e'.IsLinear κ := hlinear e' he'.out
    exact e.continuousOn_coordChangeL_of_isModuleTopology e'

end VectorBundle
