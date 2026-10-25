/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Algebra.Module.FiniteDimensionalOperator
import VectorBundles.Topology.VectorBundle.KernelProjection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Matrix

/-!
# Surjectivity loci and open maps of linear families

For a pointwise-continuous family of algebraic linear maps into a finite-dimensional target
with its given module topology, the surjectivity locus is open. The source module needs no
topology. Local persistence uses determinants in finite coordinates, continuous scalar ring
operations, and the fact that zero is closed. Neither a norm nor continuous inversion is required
for this persistence statement.

A jointly continuous family of surjective algebraic linear maps is open as a map of total
spaces when the target has finitely many continuous linear coordinates. The source needs only
a topological vector space structure; no norm or finite-dimensionality is required on it.

The total-space proof chooses an algebraic section at a single parameter. On its finite-dimensional
coordinate domain, evaluation continuity implies operator continuity. The local inverse
construction in `ContinuousLinearMap.exists_local_section_inverse` then supplies local right
sections. Translating these sections through any prescribed preimage proves openness.
-/

@[expose] public section

open Filter Topology

universe uκ uX uF uG

namespace LinearMap

section SurjectivityLocus

open scoped Topology

/-- Surjectivity persists near a parameter where an algebraic linear family is surjective,
provided evaluation at every fixed vector is continuous there. The source module needs no
topology. The finite-dimensional target carries its given module topology. -/
theorem eventually_surjective_of_continuousAt
    {κ : Type uκ} [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ]
    {B : Type uX} [TopologicalSpace B]
    {F : Type uF} [AddCommGroup F] [Module κ F]
    {G : Type uG} [AddCommGroup G] [Module κ G] [TopologicalSpace G]
    [FiniteDimensional κ G] [IsModuleTopology κ G]
    (f : B → F →ₗ[κ] G) {b₀ : B}
    (hf : ∀ v, ContinuousAt (fun b ↦ f b v) b₀)
    (hsurj : Function.Surjective (f b₀)) :
    ∀ᶠ b in 𝓝 b₀, Function.Surjective (f b) := by
  classical
  let n := Module.finrank κ G
  let e : G ≃ₗ[κ] (Fin n → κ) := (Module.finBasis κ G).equivFun
  let B₀ : F →ₗ[κ] (Fin n → κ) := e.toLinearMap.comp (f b₀)
  have hB₀ : Function.Surjective B₀ := e.surjective.comp hsurj
  obtain ⟨j, hj⟩ := B₀.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hB₀)
  let A : B → (Fin n → κ) →ₗ[κ] (Fin n → κ) := fun b ↦
    e.toLinearMap.comp ((f b).comp j)
  have hA₀ : A b₀ = LinearMap.id := by
    apply LinearMap.ext
    intro w
    change (B₀.comp j) w = w
    rw [hj, LinearMap.id_apply]
  let M : B → Matrix (Fin n) (Fin n) κ := fun b ↦ LinearMap.toMatrix' (A b)
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hM : ContinuousAt M b₀ := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    change ContinuousAt (fun b ↦ LinearMap.toMatrix' (A b) i k) b₀
    simp only [LinearMap.toMatrix'_apply]
    change ContinuousAt (fun b ↦ e (f b (j (Pi.single k 1))) i) b₀
    exact ((continuous_apply i).comp he).continuousAt.comp (hf _)
  have hM₀ : M b₀ = 1 := by
    simp only [M, hA₀, LinearMap.toMatrix'_id]
  have hdet : Continuous (fun N : Matrix (Fin n) (Fin n) κ ↦ N.det) :=
    (continuous_id : Continuous (fun N : Matrix (Fin n) (Fin n) κ ↦ N)).matrix_det
  have hdetAt : ContinuousAt (fun b ↦ (M b).det) b₀ :=
    hdet.continuousAt.comp hM
  have hdet₀ : (M b₀).det ≠ 0 := by
    rw [hM₀, Matrix.det_one]
    exact one_ne_zero
  have hnz : ∀ᶠ b in 𝓝 b₀, (M b).det ≠ 0 :=
    hdetAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hdet₀)
  filter_upwards [hnz] with b hb
  have hunit : IsUnit (M b) :=
    (Matrix.isUnit_iff_isUnit_det (M b)).mpr (isUnit_iff_ne_zero.mpr hb)
  intro y
  obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit (A := M b)).mpr hunit (e y)
  have hcoord : Matrix.toLin' (M b) = A b := Matrix.toLin'_toMatrix' (A b)
  have hx' : A b x = e y := by
    rw [← hcoord, Matrix.toLin'_apply]
    exact hx
  exact ⟨j x, e.injective hx'⟩

/-- The surjectivity locus of a pointwise-continuous algebraic linear family is open.
The source module needs no topology. The given module topology on the finite-dimensional
target is essential; an arbitrary normed-space topology need not suffice over incomplete fields. -/
theorem isOpen_setOf_surjective
    {κ : Type uκ} [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ]
    {B : Type uX} [TopologicalSpace B]
    {F : Type uF} [AddCommGroup F] [Module κ F]
    {G : Type uG} [AddCommGroup G] [Module κ G] [TopologicalSpace G]
    [FiniteDimensional κ G] [IsModuleTopology κ G]
    (f : B → F →ₗ[κ] G)
    (hf : ∀ v, Continuous (fun b ↦ f b v)) :
    IsOpen {b | Function.Surjective (f b)} := by
  exact isOpen_iff_mem_nhds.mpr fun b hb ↦
    eventually_surjective_of_continuousAt f (fun v ↦ (hf v).continuousAt) hb

end SurjectivityLocus

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
