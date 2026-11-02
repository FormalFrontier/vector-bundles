/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Module.JointEvaluation
public import VectorBundles.Topology.Module.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous linear maps in finite coordinates

For a finite index type, `ContinuousLinearEquiv.piRingOfFinite` identifies continuous linear
maps from a scalar product with their columns. This generalizes Mathlib's
`ContinuousLinearEquiv.piRing` to topological target modules without a completeness assumption
on the scalar field. Its algebraic representation is `LinearEquiv.piRing`.

A supplied continuous linear equivalence with a finite scalar product gives continuity criteria
for operator-valued functions in terms of finitely many evaluations. It also equates continuity
of an operator-valued function with joint continuity of its evaluation. These criteria use the
given product topologies and the bounded-convergence topology on continuous linear maps. In
normed spaces this is the operator-norm topology, with the given norms and scalar actions.

For a finite basis in a module with `IsModuleTopology`, the coordinate equivalence is
`Module.Basis.equivFunLOfIsModuleTopology`. The basis criteria use this equivalence without
introducing another coordinate construction. A supplied coordinate equivalence, or a module
topology together with a finite basis, is sufficient for the criteria here.

## References

The algebraic finite-source representation and the operator-space continuity interfaces are
from Mathlib, in `Mathlib.LinearAlgebra.Pi` and
`Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap`.
The joint-evaluation criterion uses
`Module.Basis.continuous_uncurry_iff_semilinear`.
-/

@[expose] public section

universe uK uE uF uι uX

open scoped BigOperators

namespace ContinuousLinearEquiv

/-- Continuous linear maps from a finite scalar product, identified with their columns.

This is the continuous refinement of `LinearEquiv.piRing` for topological target modules,
using the bounded-convergence topology on the space of continuous linear maps. -/
noncomputable def piRingOfFinite (K : Type uK) [NontriviallyNormedField K]
    (F : Type uF) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] (ι : Type uι) [Finite ι] :
    ((ι → K) →L[K] F) ≃L[K] (ι → F) := by
  classical
  letI := Fintype.ofFinite ι
  let e := LinearEquiv.piRing K F ι K
  -- The operator constructions supply continuity; `e` supplies the algebraic data.
  let reconstruct : (ι → F) →L[K] ((ι → K) →L[K] F) :=
    ∑ i, (ContinuousLinearMap.precomp (𝕜₃ := K) F
        (ContinuousLinearMap.proj (R := K) (φ := fun _ : ι => K) i)).comp
      ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := K) (E := F)).toContinuousLinearMap.comp
        (ContinuousLinearMap.proj (R := K) (φ := fun _ : ι => F) i))
  have hReconstruct (v : ι → F) (a : ι → K) :
      reconstruct v a = e.symm v a := by
    let ev₁ : ((ι → F) →L[K] ((ι → K) →L[K] F)) →+
        ((ι → K) →L[K] F) :=
      { toFun := fun L => L v
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let ev₂ : ((ι → K) →L[K] F) →+ F :=
      { toFun := fun L => L a
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev₂ (ev₁ reconstruct) = _
    dsimp only [reconstruct]
    rw [map_sum, map_sum]
    change (∑ i, a i • v i) = e.symm v a
    exact (LinearEquiv.piRing_symm_apply K v a).symm
  let inverse (v : ι → F) : (ι → K) →L[K] F :=
    { toLinearMap := e.symm v
      cont := (reconstruct v).continuous.congr (fun a => hReconstruct v a) }
  have hInverse (v : ι → F) : inverse v = reconstruct v := by
    ext a
    exact (hReconstruct v a).symm
  let columns : ((ι → K) →L[K] F) →L[K] (ι → F) :=
    ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := K) (E := F)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.precomp (𝕜₃ := K) F
          (ContinuousLinearMap.toSpanSingleton (R₁ := K) (Pi.single i (1 : K))))
  exact
    { toLinearEquiv :=
        { toFun := fun T => e T.toLinearMap
          invFun := inverse
          left_inv := fun T => by
            ext a
            exact congrArg (fun L : (ι → K) →ₗ[K] F => L a)
              (e.symm_apply_apply T.toLinearMap)
          right_inv := fun v => e.apply_symm_apply v
          map_add' := fun T U => e.map_add T.toLinearMap U.toLinearMap
          map_smul' := fun c T => e.map_smul c T.toLinearMap }
      continuous_toFun := columns.continuous.congr (fun T => by
        ext i
        simp [columns, e])
      continuous_invFun := reconstruct.continuous.congr (fun v => (hInverse v).symm) }

section PiRing

variable (K : Type uK) [NontriviallyNormedField K]
variable (F : Type uF) [AddCommGroup F] [Module K F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul K F]
variable (ι : Type uι)

/-- The columns of a continuous linear map are its values on the coordinate vectors. -/
@[simp]
theorem piRingOfFinite_apply [Finite ι] [DecidableEq ι]
    (T : (ι → K) →L[K] F) (i : ι) :
    piRingOfFinite K F ι T i = T (Pi.single i (1 : K)) := by
  classical
  change T _ = T _
  apply congrArg T
  funext j
  by_cases h : j = i <;> simp_all

/-- A continuous linear map is reconstructed from its columns by a finite sum. -/
@[simp]
theorem piRingOfFinite_symm_apply [Fintype ι] (v : ι → F) (a : ι → K) :
    (piRingOfFinite K F ι).symm v a = ∑ i, a i • v i := by
  classical
  let e := LinearEquiv.piRing K F ι K
  have h : e (((piRingOfFinite K F ι).symm v).toLinearMap) = v := by
    ext i
    simpa only [e, LinearEquiv.piRing_apply, ContinuousLinearMap.coe_coe,
      piRingOfFinite_apply] using
      congrFun ((piRingOfFinite K F ι).apply_symm_apply v) i
  have h' : ((piRingOfFinite K F ι).symm v).toLinearMap = e.symm v := by
    apply e.injective
    exact h.trans (e.apply_symm_apply v).symm
  change (((piRingOfFinite K F ι).symm v).toLinearMap) a = _
  rw [h']
  exact LinearEquiv.piRing_symm_apply K v a

/-- Taking columns agrees with `LinearEquiv.piRing` after forgetting continuity. -/
theorem piRingOfFinite_apply_eq_piRing [Fintype ι] [DecidableEq ι]
    (T : (ι → K) →L[K] F) :
    piRingOfFinite K F ι T = LinearEquiv.piRing K F ι K T.toLinearMap := by
  ext i
  simp only [piRingOfFinite_apply, LinearEquiv.piRing_apply, ContinuousLinearMap.coe_coe]

/-- Reconstruction agrees with the inverse of `LinearEquiv.piRing` after forgetting
continuity. -/
theorem piRingOfFinite_symm_toLinearMap [Fintype ι] [DecidableEq ι] (v : ι → F) :
    ((piRingOfFinite K F ι).symm v).toLinearMap = (LinearEquiv.piRing K F ι K).symm v := by
  apply LinearMap.ext
  intro a
  simp only [ContinuousLinearMap.coe_coe, piRingOfFinite_symm_apply,
    LinearEquiv.piRing_symm_apply]

end PiRing

section Coordinates

variable {K : Type uK} [NontriviallyNormedField K]
variable {E : Type uE} [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable {F : Type uF} [AddCommGroup F] [Module K F] [TopologicalSpace F]
variable {ι : Type uι}
variable {X : Type uX} [TopologicalSpace X]

/-- Continuity within a set of an operator-valued function is detected by the finitely many
columns of a supplied coordinate equivalence. -/
theorem continuousWithinAt_clm_apply_iff_piSingle
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι] [DecidableEq ι]
    (e : E ≃L[K] (ι → K)) {f : X → E →L[K] F} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔
      ∀ i, ContinuousWithinAt (fun q => f q (e.symm (Pi.single i (1 : K)))) s x := by
  let c := e.arrowCongr (ContinuousLinearEquiv.refl K F)
  let p := piRingOfFinite K F ι
  constructor
  · intro hf i
    have h : ContinuousWithinAt (fun q => p (c (f q))) s x :=
      p.continuousAt.comp_continuousWithinAt
        (c.continuousAt.comp_continuousWithinAt hf)
    simpa only [p, c, piRingOfFinite_apply, arrowCongr_apply, refl_apply] using
      (continuousWithinAt_pi.mp h i)
  · intro hf
    have h : ContinuousWithinAt (fun q => p (c (f q))) s x := by
      apply continuousWithinAt_pi.mpr
      intro i
      simpa only [p, c, piRingOfFinite_apply, arrowCongr_apply, refl_apply] using hf i
    have hc : ContinuousWithinAt (fun q => c (f q)) s x := by
      have h' : ContinuousWithinAt (fun q => p.symm (p (c (f q)))) s x :=
        p.symm.continuousAt.comp_continuousWithinAt h
      simpa only [symm_apply_apply] using h'
    have hf' : ContinuousWithinAt (fun q => c.symm (c (f q))) s x :=
      c.symm.continuousAt.comp_continuousWithinAt hc
    simpa only [symm_apply_apply] using hf'

/-- Continuity at a point of an operator-valued function is detected by the finitely many
columns of a supplied coordinate equivalence. -/
theorem continuousAt_clm_apply_iff_piSingle
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι] [DecidableEq ι]
    (e : E ≃L[K] (ι → K)) {f : X → E →L[K] F} {x : X} :
    ContinuousAt f x ↔
      ∀ i, ContinuousAt (fun q => f q (e.symm (Pi.single i (1 : K)))) x := by
  simpa only [continuousWithinAt_univ] using (continuousWithinAt_clm_apply_iff_piSingle e
    (f := f) (s := Set.univ) (x := x))

/-- Continuity on a set of an operator-valued function is detected by the finitely many
columns of a supplied coordinate equivalence. -/
theorem continuousOn_clm_apply_iff_piSingle
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι] [DecidableEq ι]
    (e : E ≃L[K] (ι → K)) {f : X → E →L[K] F} {s : Set X} :
    ContinuousOn f s ↔
      ∀ i, ContinuousOn (fun q => f q (e.symm (Pi.single i (1 : K)))) s := by
  constructor
  · intro hf i q hq
    exact (continuousWithinAt_clm_apply_iff_piSingle e).mp (hf q hq) i
  · intro hf q hq
    exact (continuousWithinAt_clm_apply_iff_piSingle e).mpr (fun i => hf i q hq)

/-- Continuity of an operator-valued function is detected by the finitely many columns of a
supplied coordinate equivalence. -/
theorem continuous_clm_apply_iff_piSingle
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι] [DecidableEq ι]
    (e : E ≃L[K] (ι → K)) {f : X → E →L[K] F} :
    Continuous f ↔ ∀ i, Continuous (fun q => f q (e.symm (Pi.single i (1 : K)))) := by
  simp only [continuous_iff_continuousAt,
    continuousAt_clm_apply_iff_piSingle e (f := f)]
  exact forall_comm

/-- For topological modules with supplied finite continuous source coordinates, continuity of
an operator-valued function is equivalent to joint continuity of its evaluation.

The finite-coordinate expansion expresses evaluation as a finite sum of products of continuous
scalar coordinates and continuous column functions. Joint continuity uses `ContinuousSMul K F`;
no norm on either module or algebraic structure on the parameter space is required. -/
theorem continuous_clm_apply_iff_uncurry
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K))
    {f : X → E →L[K] F} :
    Continuous f ↔ Continuous (fun p : X × E => f p.1 p.2) := by
  classical
  let b : Module.Basis ι K E := Module.Basis.ofEquivFun e.toLinearEquiv
  have hcoord : ∀ i, Continuous (fun v : E => (RingHom.id K) (b.repr v i)) := by
    intro i
    simpa only [b, RingHom.id_apply, Module.Basis.ofEquivFun_repr_apply,
      coe_toLinearEquiv] using (continuous_apply i).comp' e.continuous
  have hjoint :
      Continuous (fun p : X × E => f p.1 p.2) ↔
        ∀ i, Continuous (fun q => f q (b i)) :=
    b.continuous_uncurry_iff_semilinear (σ := RingHom.id K) hcoord
      (L := fun q => (f q).toLinearMap)
  exact (continuous_clm_apply_iff_piSingle e).trans (by
    simpa only [b, Module.Basis.coe_ofEquivFun, coe_symm_toLinearEquiv] using hjoint.symm)

private theorem continuous_clm_eval_const
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K)) (v : E) :
    Continuous (fun T : E →L[K] F => T v) := by
  have h : Continuous (fun p : (E →L[K] F) × E => p.1 p.2) :=
    (continuous_clm_apply_iff_uncurry e
      (f := fun T : E →L[K] F => T)).mp continuous_id
  exact h.comp (continuous_id.prodMk continuous_const)

/-- For a source with supplied finite continuous coordinates, continuity within a set of an
operator-valued function is equivalent to continuity of every fixed-vector evaluation. -/
theorem continuousWithinAt_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K))
    {f : X → E →L[K] F} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ ∀ v, ContinuousWithinAt (fun q => f q v) s x := by
  classical
  constructor
  · intro h v
    exact (continuous_clm_eval_const e v).continuousAt.comp_continuousWithinAt h
  · intro h
    exact (continuousWithinAt_clm_apply_iff_piSingle e).mpr
      (fun i => h (e.symm (Pi.single i (1 : K))))

/-- For a source with supplied finite continuous coordinates, continuity at a point of an
operator-valued function is equivalent to continuity of every fixed-vector evaluation. -/
theorem continuousAt_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K))
    {f : X → E →L[K] F} {x : X} :
    ContinuousAt f x ↔ ∀ v, ContinuousAt (fun q => f q v) x := by
  classical
  constructor
  · intro h v
    exact (continuous_clm_eval_const e v).continuousAt.comp h
  · intro h
    exact (continuousAt_clm_apply_iff_piSingle e).mpr
      (fun i => h (e.symm (Pi.single i (1 : K))))

/-- For a source with supplied finite continuous coordinates, continuity on a set of an
operator-valued function is equivalent to continuity of every fixed-vector evaluation. -/
theorem continuousOn_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K))
    {f : X → E →L[K] F} {s : Set X} :
    ContinuousOn f s ↔ ∀ v, ContinuousOn (fun q => f q v) s := by
  classical
  constructor
  · intro h v
    exact (continuous_clm_eval_const e v).comp_continuousOn h
  · intro h
    exact (continuousOn_clm_apply_iff_piSingle e).mpr
      (fun i => h (e.symm (Pi.single i (1 : K))))

/-- For a source with supplied finite continuous coordinates, continuity of an operator-valued
function is equivalent to continuity of every fixed-vector evaluation. -/
theorem continuous_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (e : E ≃L[K] (ι → K)) {f : X → E →L[K] F} :
    Continuous f ↔ ∀ v, Continuous (fun q => f q v) := by
  classical
  constructor
  · intro h v
    exact (continuous_clm_eval_const e v).comp h
  · intro h
    exact (continuous_clm_apply_iff_piSingle e).mpr
      (fun i => h (e.symm (Pi.single i (1 : K))))

end Coordinates

end ContinuousLinearEquiv

namespace Module.Basis

section FiniteCoordinates

variable {K : Type uK} [NontriviallyNormedField K]
variable {E : Type uE} [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable {F : Type uF} [AddCommGroup F] [Module K F] [TopologicalSpace F]
variable {ι : Type uι}
variable {X : Type uX} [TopologicalSpace X]

/-- In the given module topology, a finite basis detects continuity within a set of an
operator-valued function. The source coordinates are `b.equivFunLOfIsModuleTopology`. -/
theorem continuousWithinAt_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsModuleTopology K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (b : Module.Basis ι K E)
    {f : X → E →L[K] F} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun q => f q (b i)) s x := by
  classical
  simpa only [equivFunLOfIsModuleTopology_symm_single] using
    (ContinuousLinearEquiv.continuousWithinAt_clm_apply_iff_piSingle
      b.equivFunLOfIsModuleTopology (f := f) (s := s) (x := x))

/-- In the given module topology, a finite basis detects continuity at a point of an
operator-valued function. The source coordinates are `b.equivFunLOfIsModuleTopology`. -/
theorem continuousAt_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsModuleTopology K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (b : Module.Basis ι K E)
    {f : X → E →L[K] F} {x : X} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun q => f q (b i)) x := by
  classical
  simpa only [equivFunLOfIsModuleTopology_symm_single] using
    (ContinuousLinearEquiv.continuousAt_clm_apply_iff_piSingle
      b.equivFunLOfIsModuleTopology (f := f) (x := x))

/-- In the given module topology, a finite basis detects continuity on a set of an
operator-valued function. The source coordinates are `b.equivFunLOfIsModuleTopology`. -/
theorem continuousOn_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsModuleTopology K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (b : Module.Basis ι K E)
    {f : X → E →L[K] F} {s : Set X} :
    ContinuousOn f s ↔ ∀ i, ContinuousOn (fun q => f q (b i)) s := by
  classical
  simpa only [equivFunLOfIsModuleTopology_symm_single] using
    (ContinuousLinearEquiv.continuousOn_clm_apply_iff_piSingle
      b.equivFunLOfIsModuleTopology (f := f) (s := s))

/-- In the given module topology, a finite basis detects continuity of an operator-valued
function. The source coordinates are `b.equivFunLOfIsModuleTopology`. -/
theorem continuous_clm_apply_iff
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsModuleTopology K E]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [Finite ι]
    (b : Module.Basis ι K E) {f : X → E →L[K] F} :
    Continuous f ↔ ∀ i, Continuous (fun q => f q (b i)) := by
  classical
  simpa only [equivFunLOfIsModuleTopology_symm_single] using
    (ContinuousLinearEquiv.continuous_clm_apply_iff_piSingle
      b.equivFunLOfIsModuleTopology (f := f))

end FiniteCoordinates

end Module.Basis
