/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

public import VectorBundles.Analysis.Normed.Operator.NearbyIdempotent
public import VectorBundles.Topology.Module.Basis
public import VectorBundles.Topology.VectorBundle.FiniteRank
public import VectorBundles.Topology.VectorBundle.Range

/-!
# Coordinates for finite-dimensional projector ranges

A fixed system of coordinates on the range of an idempotent gives coordinate maps
on the ranges of nearby idempotents. The inverse coordinate map applies the varying
projector to the fixed coordinate vector. The forward coordinate map uses the
fixed-range compression inverse.

Both formulas are jointly continuous in the base point and the vector. The forward
formula is defined on the strict unit-gap neighborhood of the fixed projector; the
inverse formula is continuous on the whole product.
These maps define local trivializations on the strict unit-gap neighborhoods.

A finite-dimensional range carrying its module topology admits the required
coordinate equivalence over any nontrivially normed field.
The range-induced total-space topology restricts to the original subtype topology
on each fibre.
-/

@[expose] public section

universe uK uA uX uE

namespace ContinuousLinearMap

open Topology

variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
variable {X : Type uX} [TopologicalSpace X]

attribute [local instance] VectorBundle.rangeTotalSpaceTopology

/-- A local trivialization of projector ranges near a fixed anchor projector. -/
noncomputable def rangeAnchorChart (F : Type uE)
    (P : A →L[K] A) [FiniteDimensional K (LinearMap.range P.toLinearMap)]
    (Q : X → A →L[K] A) (hP : IsIdempotentElem P)
    (hid : ∀ x, IsIdempotentElem (Q x)) (hQ : Continuous Q) {d : ℕ}
    (b : LinearMap.range P.toLinearMap ≃L[K] (Fin d → K)) :
    let E : X → Type uA := fun x => ↥(LinearMap.range (Q x).toLinearMap)
    letI : TopologicalSpace (Bundle.TotalSpace F E) :=
      VectorBundle.rangeTotalSpaceTopology (fun x => (Q x).toLinearMap)
    Bundle.Trivialization (Fin d → K) (fun p : Bundle.TotalSpace F E => p.proj) := by
  classical
  let E : X → Type uA := fun x => ↥(LinearMap.range (Q x).toLinearMap)
  let T := Bundle.TotalSpace F E
  letI : TopologicalSpace T :=
    VectorBundle.rangeTotalSpaceTopology (fun x => (Q x).toLinearMap)
  let U : Set X := {x | ‖Q x - P‖ < 1}
  let coord (x : X) (a : E x) : Fin d → K :=
    if hx : x ∈ U then
      b (fixedRangeCompressionInverse P (Q x) hP (hid x) hx
        (⟨P (a : A), ⟨(a : A), rfl⟩⟩ : LinearMap.range P.toLinearMap))
    else 0
  let inv (x : X) (v : Fin d → K) : E x :=
    ⟨Q x (b.symm v), ⟨(b.symm v : A), rfl⟩⟩
  let φ : T → X × (Fin d → K) := fun p => (p.proj, coord p.proj p.2)
  let ψ : X × (Fin d → K) → T := fun p => ⟨p.1, inv p.1 p.2⟩
  have hg : Topology.IsEmbedding (fun p : T => (p.proj, (p.2 : A))) :=
    VectorBundle.rangeInclusion_isEmbedding (fun x => (Q x).toLinearMap)
  have hfst : Continuous (fun p : T => p.proj) := hg.continuous.fst
  have hU : IsOpen U :=
    isOpen_lt ((hQ.sub continuous_const).norm) continuous_const
  have hψ : Continuous ψ := by
    apply hg.isInducing.continuous_iff.mpr
    exact continuous_fst.prodMk
      ((hQ.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp (b.symm.continuous.comp continuous_snd)))
  have hφ : ContinuousOn φ {p : T | p.proj ∈ U} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hs : Continuous (fun p : {p : T // p.proj ∈ U} =>
        (⟨p.val.proj, p.property⟩ : {x : X // ‖Q x - P‖ < 1})) :=
      (hfst.comp continuous_subtype_val).subtype_mk (fun p => p.property)
    have ha : Continuous (fun p : {p : T // p.proj ∈ U} => (p.val.2 : A)) :=
      hg.continuous.snd.comp continuous_subtype_val
    have hP_range : Continuous (fun a : A =>
        (⟨P a, ⟨a, rfl⟩⟩ : LinearMap.range P.toLinearMap)) :=
      P.continuous.subtype_mk (fun a => ⟨a, rfl⟩)
    have hc := (b.continuous.comp
      (((continuous_fixedRangeCompressionInverse P Q hP hid hQ).comp continuous_fst).clm_apply
        (hP_range.comp continuous_snd))).comp (hs.prodMk ha)
    change Continuous (fun p : {p : T // p.proj ∈ U} => φ p.val)
    refine ((hfst.comp continuous_subtype_val).prodMk hc).congr ?_
    intro p
    have hpU : p.val.proj ∈ U := p.property
    simp only [φ, coord, Function.comp_apply, dite_eq_left hpU]
  refine
    { toFun := φ
      invFun := ψ
      source := {p : T | p.proj ∈ U}
      target := U ×ˢ Set.univ
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hU.preimage hfst
      open_target := hU.prod isOpen_univ
      continuousOn_toFun := hφ
      continuousOn_invFun := hψ.continuousOn
      baseSet := U
      open_baseSet := hU
      source_eq := rfl
      target_eq := rfl
      proj_toFun := ?_ }
  · intro p hp
    exact ⟨hp, Set.mem_univ _⟩
  · intro p hp
    exact hp.1
  · rintro ⟨x, a⟩ hx
    have hxU : x ∈ U := hx
    have hf : inv x (coord x a) = a := by
      apply Subtype.ext
      have he := congrArg (fun z : E x => (z : A))
        ((nearbyRangeEquiv P (Q x) hP (hid x) hxU).apply_symm_apply a)
      simp only [nearbyRangeEquiv_apply, nearbyRangeEquiv_symm_apply] at he
      change Q x
        (fixedRangeCompressionInverse P (Q x) hP (hid x) hxU
          (⟨P (a : A), ⟨(a : A), rfl⟩⟩ : LinearMap.range P.toLinearMap) : A) =
        (a : A) at he
      simpa only [inv, coord, dite_eq_left hxU, b.symm_apply_apply] using he
    exact congrArg (fun z : E x => (⟨x, z⟩ : T)) hf
  · rintro ⟨x, v⟩ hx
    have hxU : x ∈ U := hx.1
    have hf : coord x (inv x v) = v := by
      have he :=
        ((nearbyRangeEquiv P (Q x) hP (hid x) hxU).symm_apply_apply (b.symm v))
      simp only [nearbyRangeEquiv_apply, nearbyRangeEquiv_symm_apply] at he
      change fixedRangeCompressionInverse P (Q x) hP (hid x) hxU
        (⟨P (Q x (b.symm v : A)), ⟨Q x (b.symm v : A), rfl⟩⟩ :
          LinearMap.range P.toLinearMap) = b.symm v at he
      have hb := congrArg b he
      simpa only [coord, inv, dite_eq_left hxU, b.apply_symm_apply] using hb
    exact congrArg (fun w => (x, w)) hf
  · intro p hp
    rfl

/-- The base set, fibre equivalences, inverse formula, and coverage of a range chart. -/
theorem rangeAnchorChart_spec (F : Type uE)
    (P : A →L[K] A) [FiniteDimensional K (LinearMap.range P.toLinearMap)]
    (Q : X → A →L[K] A) (hP : IsIdempotentElem P)
    (hid : ∀ x, IsIdempotentElem (Q x)) (hQ : Continuous Q) {d : ℕ}
    (b : LinearMap.range P.toLinearMap ≃L[K] (Fin d → K)) :
    let E : X → Type uA := fun x => ↥(LinearMap.range (Q x).toLinearMap)
    let e := rangeAnchorChart F P Q hP hid hQ b
    e.baseSet = {x | ‖Q x - P‖ < 1} ∧
      (∀ (x : X) (hx : ‖Q x - P‖ < 1),
        (fun a : E x => (e ⟨x, a⟩).2) =
          ((nearbyRangeEquiv P (Q x) hP (hid x) hx).symm.trans b : E x → (Fin d → K))) ∧
      (∀ (x : X) (v : Fin d → K),
        ((e.invFun (x, v)).2 : A) = Q x (b.symm v)) ∧
      ∀ x, Q x = P → x ∈ e.baseSet := by
  classical
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x hx
    funext a
    change (if h : ‖Q x - P‖ < 1 then
      b (fixedRangeCompressionInverse P (Q x) hP (hid x) h
        (⟨P (a : A), ⟨(a : A), rfl⟩⟩ : LinearMap.range P.toLinearMap))
      else 0) = _
    rw [dite_eq_left hx]
    change b (fixedRangeCompressionInverse P (Q x) hP (hid x) hx
      (⟨P (a : A), ⟨(a : A), rfl⟩⟩ : LinearMap.range P.toLinearMap)) =
      b ((nearbyRangeEquiv P (Q x) hP (hid x) hx).symm a)
    rw [nearbyRangeEquiv_symm_apply]
    rfl
  · intro x v
    rfl
  · intro x hx
    change ‖Q x - P‖ < 1
    simp [hx]

/-- A finite-rank atlas for the ranges of a norm-continuous family of idempotents.
The chart at `c` has the strict unit-gap base set and uses
`Module.finrank K (LinearMap.range (Q c).toLinearMap)` scalar coordinates.
The fibres retain their original subtype topologies, and the total space carries
`VectorBundle.rangeTotalSpaceTopology`. No completeness or finite-dimensionality
of the ambient space is required. -/
noncomputable def finiteRankRangeAtlas (F : Type uE)
    (Q : X → A →L[K] A) (hQ : Continuous Q)
    (hid : ∀ x, IsIdempotentElem (Q x))
    (hfd : ∀ x, FiniteDimensional K (LinearMap.range (Q x).toLinearMap))
    (hmt : ∀ x, IsModuleTopology K (LinearMap.range (Q x).toLinearMap)) :
    let E : X → Type uA := fun x => ↥(LinearMap.range (Q x).toLinearMap)
    letI : TopologicalSpace (Bundle.TotalSpace F E) :=
      VectorBundle.rangeTotalSpaceTopology (fun x => (Q x).toLinearMap)
    Bundle.FiniteRankAtlas K F E := by
  classical
  let E : X → Type uA := fun x => ↥(LinearMap.range (Q x).toLinearMap)
  let T := Bundle.TotalSpace F E
  letI : TopologicalSpace T :=
    VectorBundle.rangeTotalSpaceTopology (fun x => (Q x).toLinearMap)
  let rank : X → ℕ := fun c => Module.finrank K (E c)
  let b (c : X) : E c ≃L[K] (Fin (rank c) → K) := by
    letI : FiniteDimensional K (E c) := hfd c
    letI : IsModuleTopology K (E c) := hmt c
    exact (Module.finBasis K (E c)).equivFunLOfIsModuleTopology
  let chart (c : X) :
      Bundle.Trivialization (Fin (rank c) → K) (fun p : T => p.proj) := by
    letI : FiniteDimensional K (E c) := hfd c
    exact rangeAnchorChart F (Q c) Q (hid c) hid hQ (b c)
  refine ⟨X, rank, chart, ?_, ?_, ?_⟩
  · intro c
    let : FiniteDimensional K (E c) := hfd c
    constructor
    · intro x hx a a'
      have hxU : ‖Q x - Q c‖ < 1 := hx
      let e : E x ≃L[K] (Fin (rank c) → K) :=
        (nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hxU).symm.trans (b c)
      have hc (a : E x) : (chart c ⟨x, a⟩).2 = e a :=
        congrFun ((rangeAnchorChart_spec F (Q c) Q (hid c) hid hQ (b c)).2.1 x hxU) a
      change (chart c ⟨x, a + a'⟩).2 =
        (chart c ⟨x, a⟩).2 + (chart c ⟨x, a'⟩).2
      rw [hc (a + a'), hc a, hc a']
      exact e.map_add a a'
    · intro x hx r a
      have hxU : ‖Q x - Q c‖ < 1 := hx
      let e : E x ≃L[K] (Fin (rank c) → K) :=
        (nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hxU).symm.trans (b c)
      have hc (a : E x) : (chart c ⟨x, a⟩).2 = e a :=
        congrFun ((rangeAnchorChart_spec F (Q c) Q (hid c) hid hQ (b c)).2.1 x hxU) a
      change (chart c ⟨x, r • a⟩).2 = r • (chart c ⟨x, a⟩).2
      rw [hc (r • a), hc a]
      exact e.map_smul r a
  · intro x
    refine ⟨x, ?_⟩
    let : FiniteDimensional K (E x) := hfd x
    exact (rangeAnchorChart_spec F (Q x) Q (hid x) hid hQ (b x)).2.2.2 x rfl
  · intro x
    have hf : IsEmbedding (fun a : E x => (⟨x, a⟩ : T)) := by
      let E : X → Type uA := fun y => ↥(LinearMap.range (Q y).toLinearMap)
      let : TopologicalSpace (Bundle.TotalSpace F E) :=
        VectorBundle.rangeTotalSpaceTopology (fun y => (Q y).toLinearMap)
      have hg : Topology.IsEmbedding
          (fun p : Bundle.TotalSpace F E => (p.proj, (p.2 : A))) :=
        VectorBundle.rangeInclusion_isEmbedding (fun y => (Q y).toLinearMap)
      have hf : Topology.IsEmbedding (fun a : E x => (x, (a : A))) := by
        let f : E x → X × A := fun a => (x, (a : A))
        have hc : Continuous f := continuous_const.prodMk continuous_subtype_val
        have hd : @Continuous (E x) A (TopologicalSpace.induced f inferInstance)
            inferInstance (fun a : E x => (a : A)) := by
          let : TopologicalSpace (E x) := TopologicalSpace.induced f inferInstance
          exact (continuous_snd : Continuous (Prod.snd : X × A → A)).comp
            (continuous_induced_dom : @Continuous (E x) (X × A)
              (TopologicalSpace.induced f inferInstance) inferInstance f)
        refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hc) ?_⟩, ?_⟩
        · exact continuous_iff_le_induced.mp hd
        · intro a b h
          exact Subtype.ext (congrArg Prod.snd h)
      exact hg.of_comp_iff.mp hf
    exact hf.isInducing

section

variable (F : Type uE) (Q : X → A →L[K] A) (hQ : Continuous Q)
variable (hid : ∀ x, IsIdempotentElem (Q x))
variable [hfd : ∀ x, FiniteDimensional K (LinearMap.range (Q x).toLinearMap)]
variable [hmt : ∀ x, IsModuleTopology K (LinearMap.range (Q x).toLinearMap)]

/-- The chart rank is the dimension of its anchor range. -/
theorem finiteRankRangeAtlas_rank (c : X) :
    (finiteRankRangeAtlas F Q hQ hid hfd hmt).rank c =
      Module.finrank K (LinearMap.range (Q c).toLinearMap) := rfl

/-- The chart at an anchor has its strict unit-gap neighborhood as base set. -/
theorem finiteRankRangeAtlas_baseSet (c : X) :
    ((finiteRankRangeAtlas F Q hQ hid hfd hmt).chart c).baseSet =
      {x | ‖Q x - Q c‖ < 1} := rfl

/-- Coordinates at a nearby fibre are obtained by transporting to the anchor. -/
theorem finiteRankRangeAtlas_anchor_transport (c x : X) (hx : ‖Q x - Q c‖ < 1)
    (a : LinearMap.range (Q x).toLinearMap) :
    ((finiteRankRangeAtlas F Q hQ hid hfd hmt).chart c ⟨x, a⟩).2 =
      ((finiteRankRangeAtlas F Q hQ hid hfd hmt).chart c
        ⟨c, (nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hx).symm a⟩).2 := by
  classical
  let : FiniteDimensional K (LinearMap.range (Q c).toLinearMap) := hfd c
  let : IsModuleTopology K (LinearMap.range (Q c).toLinearMap) := hmt c
  let R : Type uA := ↥(LinearMap.range (Q c).toLinearMap)
  let b : R ≃L[K] (Fin (Module.finrank K R) → K) := by
    exact (Module.finBasis K R).equivFunLOfIsModuleTopology
  have hcc : ‖Q c - Q c‖ < 1 := by simp
  have hs (z : LinearMap.range (Q c).toLinearMap) :
      (nearbyRangeEquiv (Q c) (Q c) (hid c) (hid c) hcc).symm z = z := by
    apply (nearbyRangeEquiv (Q c) (Q c) (hid c) (hid c) hcc).injective
    rw [(nearbyRangeEquiv (Q c) (Q c) (hid c) (hid c) hcc).apply_symm_apply]
    apply Subtype.ext
    simp only [nearbyRangeEquiv_apply]
    rcases z.property with ⟨y, hy⟩
    rw [← hy]
    exact (congrArg (fun f : A →L[K] A => f y) (hid c)).symm
  change (rangeAnchorChart F (Q c) Q (hid c) hid hQ b ⟨x, a⟩).2 =
    (rangeAnchorChart F (Q c) Q (hid c) hid hQ b
      ⟨c, (nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hx).symm a⟩).2
  have hc := (rangeAnchorChart_spec F (Q c) Q (hid c) hid hQ b).2.1
  rw [congrFun (hc x hx) a,
    congrFun (hc c hcc) ((nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hx).symm a)]
  change b ((nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hx).symm a) =
    b ((nearbyRangeEquiv (Q c) (Q c) (hid c) (hid c) hcc).symm
      ((nearbyRangeEquiv (Q c) (Q x) (hid c) (hid x) hx).symm a))
  rw [hs]

/-- The ambient inverse vector is the projector applied to the anchor inverse. -/
theorem finiteRankRangeAtlas_inverse_ambient (c x : X)
    (v : Fin (Module.finrank K (LinearMap.range (Q c).toLinearMap)) → K) :
    ((((finiteRankRangeAtlas F Q hQ hid hfd hmt).chart c).invFun (x, v)).2 : A) =
      Q x ((((finiteRankRangeAtlas F Q hQ hid hfd hmt).chart c).invFun (c, v)).2 : A) := by
  classical
  let : FiniteDimensional K (LinearMap.range (Q c).toLinearMap) := hfd c
  let : IsModuleTopology K (LinearMap.range (Q c).toLinearMap) := hmt c
  let R : Type uA := ↥(LinearMap.range (Q c).toLinearMap)
  let b : R ≃L[K] (Fin (Module.finrank K R) → K) := by
    exact (Module.finBasis K R).equivFunLOfIsModuleTopology
  change Q x (b.symm v : A) = Q x (Q c (b.symm v : A))
  apply congrArg (Q x)
  rcases (b.symm v).property with ⟨y, hy⟩
  rw [← hy]
  exact (congrArg (fun f : A →L[K] A => f y) (hid c)).symm

end

end ContinuousLinearMap
