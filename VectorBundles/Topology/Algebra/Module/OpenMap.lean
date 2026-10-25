/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Algebra.Module.FiniteDimensionalOperator
import VectorBundles.Topology.VectorBundle.KernelProjection
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions

/-!
# Open maps from surjective linear families

A jointly continuous family of surjective algebraic linear maps is open as a map of total
spaces when the target has finitely many continuous linear coordinates. The source needs only
a topological vector space structure; no norm or finite-dimensionality is required on it.

The proof chooses an algebraic section at a single parameter. On its finite-dimensional
coordinate domain, evaluation continuity implies operator continuity. The local inverse
construction in `ContinuousLinearMap.exists_local_section_inverse` then supplies local right
sections. Translating these sections through any prescribed preimage proves openness.
-/

@[expose] public section

open Filter Topology

universe uκ uX uF uG

namespace LinearMap

variable {𝕜 : Type uκ} [NontriviallyNormedField 𝕜]
  {X : Type uX} [TopologicalSpace X]
  {F : Type uF} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
  {G : Type uG} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [ContinuousAdd G] [ContinuousSMul 𝕜 G]

omit [ContinuousAdd G] [ContinuousSMul 𝕜 G] in
private theorem exists_local_rightSection_of_finiteCoordinates
    {n : ℕ} (e : G ≃L[𝕜] (Fin n → 𝕜)) (A : X → F →ₗ[𝕜] G)
    (hA : Continuous (fun p : X × F ↦ A p.1 p.2))
    (x0 : X) (hSurj : Function.Surjective (A x0)) :
    ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
      ∃ S : U → G →ₗ[𝕜] F,
        Continuous (fun p : U × G ↦ S p.1 p.2) ∧
        ∀ (x : U) (y : G), A x.1 (S x y) = y := by
  classical
  let B0 : F →ₗ[𝕜] (Fin n → 𝕜) := e.toLinearMap.comp (A x0)
  have hB0 : Function.Surjective B0 := e.surjective.comp hSurj
  obtain ⟨j, hj⟩ := B0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hB0)
  have hjcont : Continuous j := IsModuleTopology.continuous_of_linearMap j
  let C : X → (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) := fun x ↦
    ⟨e.toLinearMap.comp ((A x).comp j),
      IsModuleTopology.continuous_of_linearMap _⟩
  have hC : Continuous C := by
    rw [continuous_iff_continuousAt]
    intro x
    apply ContinuousLinearMap.tendsto_iff_forall_apply_of_isModuleTopology.mpr
    intro w
    change ContinuousAt (fun z : X ↦ e (A z (j w))) x
    exact (e.continuous.comp
      (hA.comp (continuous_id.prodMk continuous_const))).continuousAt
  have hC0 : (C x0).comp (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) =
      ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) := by
    apply ContinuousLinearMap.ext
    intro w
    change (B0.comp j) w = w
    rw [hj, LinearMap.id_apply]
  obtain ⟨U, hU, hx0, K, hK, hright, _⟩ :=
    ContinuousLinearMap.exists_local_section_inverse C hC x0
      (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) hC0
  let S : U → G →ₗ[𝕜] F := fun x ↦
    j.comp ((K x).toLinearMap.comp e.toLinearMap)
  refine ⟨U, hU, hx0, S, ?_, ?_⟩
  · exact hjcont.comp (hK.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro x y
    apply e.injective
    exact hright x (e y)

/-- A jointly continuous family of surjective algebraic linear maps induces an open map on
products if the target admits continuous linear coordinates in a finite power of the field.
No norm, finite-dimensionality, or module-topology assumption is required on the source. -/
private theorem isOpenMap_prodMap_of_finiteCoordinates
    {n : ℕ} (e : G ≃L[𝕜] (Fin n → 𝕜)) (A : X → F →ₗ[𝕜] G)
    (hA : Continuous (fun p : X × F ↦ A p.1 p.2))
    (hSurj : ∀ x, Function.Surjective (A x)) :
    IsOpenMap (fun p : X × F ↦ (p.1, A p.1 p.2)) := by
  apply IsOpenMap.of_nhds_le
  rintro ⟨x0, v0⟩
  obtain ⟨U, hU, hx0, S, hS, hright⟩ :=
    exists_local_rightSection_of_finiteCoordinates e A hA x0 (hSurj x0)
  let q : U × G → X × F := fun p ↦
    (p.1.1, v0 + S p.1 (p.2 - A p.1.1 v0))
  have hdiff : Continuous (fun p : U × G ↦ p.2 - A p.1.1 v0) := by
    have heq : (fun p : U × G ↦ p.2 - A p.1.1 v0) =
        (fun p : U × G ↦ p.2 + (-1 : 𝕜) • A p.1.1 v0) := by
      funext p
      simp only [sub_eq_add_neg, neg_one_smul]
    rw [heq]
    exact continuous_snd.add
      (continuous_const.smul (hA.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)))
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.add (hS.comp (continuous_fst.prodMk hdiff)))
  have hq0 : q (⟨x0, hx0⟩, A x0 v0) = (x0, v0) := by
    simp [q]
  have hcomp : (fun p : X × F ↦ (p.1, A p.1 p.2)) ∘ q =
      (fun p : U × G ↦ (p.1.1, p.2)) := by
    funext p
    apply Prod.ext
    · rfl
    · change A p.1.1 (v0 + S p.1 (p.2 - A p.1.1 v0)) = p.2
      rw [map_add, hright, add_comm, sub_add_cancel]
  let p0 : U × G := (⟨x0, hx0⟩, A x0 v0)
  have hqAt : Tendsto q (𝓝 p0) (𝓝 (x0, v0)) := by
    simpa only [ContinuousAt, p0, hq0] using (hq.continuousAt (x := p0))
  have hi : IsOpenMap (fun p : U × G ↦ (p.1.1, p.2)) :=
    hU.isOpenMap_subtype_val.prodMap
      (show IsOpenMap (fun y : G ↦ y) from fun V hV ↦ by simpa using hV)
  change 𝓝 (x0, A x0 v0) ≤
    Filter.map (fun p : X × F ↦ (p.1, A p.1 p.2)) (𝓝 (x0, v0))
  have hm : Filter.map (fun p : X × F ↦ (p.1, A p.1 p.2))
      (Filter.map q (𝓝 p0)) ≤
      Filter.map (fun p : X × F ↦ (p.1, A p.1 p.2)) (𝓝 (x0, v0)) :=
    Filter.map_mono hqAt
  rw [Filter.map_map, hcomp] at hm
  exact (hi.nhds_le p0).trans hm

/-- A jointly continuous family of surjective algebraic linear maps induces an open map on
products when the finite-dimensional target carries its given module topology.
No norm, finite-dimensionality, or module-topology assumption is required on the source. -/
theorem isOpenMap_prodMap [FiniteDimensional 𝕜 G] [IsModuleTopology 𝕜 G]
    (A : X → F →ₗ[𝕜] G)
    (hA : Continuous (fun p : X × F ↦ A p.1 p.2))
    (hSurj : ∀ x, Function.Surjective (A x)) :
    IsOpenMap (fun p : X × F ↦ (p.1, A p.1 p.2)) := by
  classical
  let b := Module.finBasis 𝕜 G
  let e : G ≃L[𝕜] (Fin (Module.finrank 𝕜 G) → 𝕜) :=
    ContinuousLinearEquiv.mk b.equivFun
      (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
  exact isOpenMap_prodMap_of_finiteCoordinates e A hA hSurj

end LinearMap
