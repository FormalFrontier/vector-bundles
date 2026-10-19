/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import VectorBundles.Analysis.Normed.Operator.Factorization
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Instances.Matrix

/-!
# Local projections onto kernels

A continuous family of linear maps from a finite-dimensional normed space, surjective
at one point, admits jointly continuous kernel projections on an open neighborhood of
that point. The projections have a common complementary subspace. In particular they
satisfy `p b (p c x) = p b x`, so their restrictions give mutually inverse maps between
any two kernels in this neighborhood.

## Implementation notes

The target retains its given norm topology and is assumed to have the module topology.
Its finite dimension follows from surjectivity at the chosen point. An algebraic right
inverse at that point is continuous by the module-topology universal property. In a
finite basis of the target, the composite of the varying map with this fixed section
has identity matrix at the chosen point. Its determinant is nonzero on an open
neighborhood; scalar inversion and the adjugate formula give continuous inverse action
there. Finite-basis matrix action and local two-sided inversion are established separately
from the kernel projections. Composing with the fixed section gives right inverses with
a common range. The projections are Mathlib's `ContinuousLinearMap.projKerOfRightInverse`,
followed by kernel inclusion. No completeness, inner product, or change of norm or topology
is used. Only joint continuity of the projection action is asserted, not a bundle atlas.

## References

The proof uses the standard fixed-complement construction, Mathlib's algebraic
projective-module lifting API by Kevin Buzzard and Antoine Labelle, module-topology API
by Kevin Buzzard and Will Sawin, matrix topology and inverse APIs by Oliver Nash and
Eric Wieser, and continuous linear map evaluation by Patrick Massot and Johannes Hölzl.
The fixed-complement perspective also appears in the orthogonal-family construction in
`VectorBundles.Topology.VectorBundle.OrthogonalComplement`; the present argument does not
use orthogonality.
-/

@[expose] public section

open scoped Matrix

universe uκ uB uF uG

namespace ContinuousLinearMap

/-- A continuous family of matrices acts jointly continuously in a finite basis of a
normed space with its module topology. -/
private theorem continuous_matrix_toLin_apply
    {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
    [IsModuleTopology κ G]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Module.Basis ι κ G)
    (M : B → Matrix ι ι κ) (hM : Continuous M) :
    Continuous (fun z : B × G ↦ Matrix.toLin v v (M z.1) z.2) := by
  let e := v.equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have h_apply (b : B) (y : G) :
      Matrix.toLin v v (M b) y = e.symm (M b *ᵥ e y) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change v.equivFun (Matrix.toLin v v (M b) y) = M b *ᵥ v.equivFun y
    rw [v.equivFun_apply, v.equivFun_apply]
    exact Matrix.repr_toLin v v (M b) y
  have hcoord : Continuous (fun z : B × G ↦ M z.1 *ᵥ e z.2) :=
    (hM.comp continuous_fst).matrix_mulVec (he.comp continuous_snd)
  exact (he'.comp hcoord).congr (fun z ↦ (h_apply z.1 z.2).symm)

/-- If a fixed continuous section splits one member of a continuous family, the
composites with that section have jointly continuous two-sided inverses nearby. -/
theorem exists_local_section_inverse
    {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
    [FiniteDimensional κ G] [IsModuleTopology κ G]
    (A : B → F →L[κ] G) (hA : Continuous A)
    (b0 : B) (j0 : G →L[κ] F)
    (hj0 : (A b0).comp j0 = ContinuousLinearMap.id κ G) :
    ∃ U : Set B, IsOpen U ∧ b0 ∈ U ∧
      ∃ K : U → G →L[κ] G,
        Continuous (fun z : U × G ↦ K z.1 z.2) ∧
        (∀ (b : U) (y : G), A b.1 (j0 (K b y)) = y) ∧
        ∀ (b : U) (y : G), K b (A b.1 (j0 y)) = y := by
  classical
  let v := Module.finBasis κ G
  let M : B → Matrix (Fin (Module.finrank κ G)) (Fin (Module.finrank κ G)) κ :=
    fun b ↦ LinearMap.toMatrix v v ((A b).toLinearMap.comp j0.toLinearMap)
  have hM : Continuous M := by
    apply continuous_matrix
    intro i k
    simp only [M, LinearMap.toMatrix_apply, LinearMap.comp_apply]
    exact (IsModuleTopology.continuous_of_linearMap (v.coord i)).comp
      (hA.clm_apply continuous_const)
  have hM0 : M b0 = 1 := by
    change LinearMap.toMatrix v v ((A b0).comp j0).toLinearMap = 1
    rw [hj0]
    exact LinearMap.toMatrix_id v
  let U : Set B := {b | (M b).det ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hM.matrix_det
  have hb0 : b0 ∈ U := by simp [U, hM0]
  have hMr : Continuous (fun b : U ↦ M b.1) := hM.comp continuous_subtype_val
  have hInv : Continuous (fun b : U ↦ (M b.1)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hscalar : ContinuousAt Ring.inverse (M b.1).det := by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ b.property)
    exact (continuousAt_matrix_inv (M b.1) hscalar).comp
      (f := fun c : U ↦ M c.1) (x := b) hMr.continuousAt
  let k : U → G →ₗ[κ] G := fun b ↦ Matrix.toLin v v (M b.1)⁻¹
  have hk : Continuous (fun z : U × G ↦ k z.1 z.2) :=
    continuous_matrix_toLin_apply v (fun b : U ↦ (M b.1)⁻¹) hInv
  have hMlin (b : B) : Matrix.toLin v v (M b) = (A b).toLinearMap.comp j0.toLinearMap :=
    Matrix.toLin_toMatrix v v _
  let K : U → G →L[κ] G :=
    fun b ↦ ⟨k b, IsModuleTopology.continuous_of_linearMap (k b)⟩
  refine ⟨U, hU, hb0, K, hk, ?_, ?_⟩
  · intro b y
    change ((A b.1).toLinearMap.comp j0.toLinearMap) (k b y) = y
    rw [← hMlin b.1]
    change Matrix.toLin v v (M b.1) (Matrix.toLin v v (M b.1)⁻¹ y) = y
    rw [← Matrix.toLin_mul_apply v v v,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr b.property),
      Matrix.toLin_one, LinearMap.id_apply]
  · intro b y
    change Matrix.toLin v v (M b.1)⁻¹ (((A b.1).toLinearMap.comp j0.toLinearMap) y) = y
    rw [← hMlin b.1, ← Matrix.toLin_mul_apply v v v,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr b.property),
      Matrix.toLin_one, LinearMap.id_apply]

/-- Near a surjective member of a continuous family, there are jointly continuous
projections onto its kernels with a common complement. The absorption identity makes
the restrictions of `p b` and `p c` to the two kernels mutually inverse.

The target's given topology must be its module topology. Its finite dimension and the
fixed continuous section used in the construction are derived, not additional inputs. -/
theorem exists_local_kernel_projections
    {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
    [FiniteDimensional κ F] [IsModuleTopology κ G]
    (A : B → F →L[κ] G) (hA : Continuous A)
    (b0 : B) (hsurj : Function.Surjective (A b0)) :
    ∃ U : Set B, IsOpen U ∧ b0 ∈ U ∧
      ∃ p : U → F →L[κ] F,
        Continuous (fun z : U × F ↦ p z.1 z.2) ∧
        (∀ (b : U) (x : F), A b.1 (p b x) = 0) ∧
        (∀ (b : U) (x : F), A b.1 x = 0 → p b x = x) ∧
        ∀ (b c : U) (x : F), p b (p c x) = p b x := by
  classical
  let : FiniteDimensional κ G :=
    FiniteDimensional.of_surjective (A b0).toLinearMap hsurj
  obtain ⟨j, hj⟩ := (A b0).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let j0 : G →L[κ] F := ⟨j, IsModuleTopology.continuous_of_linearMap j⟩
  have hj0 : (A b0).comp j0 = ContinuousLinearMap.id κ G := by
    ext y
    change ((A b0).toLinearMap.comp j) y = y
    rw [hj, LinearMap.id_apply]
  obtain ⟨U, hU, hb0, k, hk, hright, hleft⟩ :=
    exists_local_section_inverse A hA b0 j0 hj0
  let s : U → G →L[κ] F := fun b ↦ j0.comp (k b)
  have hs (b : U) : Function.RightInverse (s b) (A b.1) := hright b
  let p : U → F →L[κ] F := fun b ↦
    (A b.1).ker.subtypeL.comp ((A b.1).projKerOfRightInverse (s b) (hs b))
  have hp_apply (b : U) (x : F) : p b x = x - j0 (k b (A b.1 x)) :=
    coe_projKerOfRightInverse_apply (A b.1) (s b) (hs b) x
  have hAx : Continuous (fun z : U × F ↦ A z.1.1 z.2) :=
    ((hA.comp continuous_subtype_val).comp continuous_fst).clm_apply continuous_snd
  have hKA : Continuous (fun z : U × F ↦ k z.1 (A z.1.1 z.2)) :=
    hk.comp (continuous_fst.prodMk hAx)
  have hjKA : Continuous (fun z : U × F ↦ j0 (k z.1 (A z.1.1 z.2))) :=
    j0.continuous.comp hKA
  have hp : Continuous (fun z : U × F ↦ p z.1 z.2) :=
    (continuous_snd.sub hjKA).congr (fun z ↦ (hp_apply z.1 z.2).symm)
  -- Every projection kills the same fixed section, not merely its own right inverse.
  have hpj (b : U) (y : G) : p b (j0 y) = 0 := by
    rw [hp_apply, hleft b y, sub_self]
  refine ⟨U, hU, hb0, p, hp, ?_, ?_, ?_⟩
  · intro b x
    exact LinearMap.mem_ker.mp
      ((A b.1).projKerOfRightInverse (s b) (hs b) x).property
  · intro b x hx
    rw [hp_apply, hx, map_zero, map_zero, sub_zero]
  · intro b c x
    rw [hp_apply c x, map_sub, hpj, sub_zero]

end ContinuousLinearMap

universe uC

namespace LinearMap

/-- The coefficients in a uniformly injective common range are characterized by their
image under the family of maps. -/
private theorem exists_coefficients_of_uniform_lower_bound
    {κ : Type uκ} [CommSemiring κ]
    {B : Type uB}
    {F : Type uF} [AddCommMonoid F] [Module κ F]
    {G : Type uG} [SeminormedAddCommGroup G] [Module κ G]
    {C : Type uC} [NormedAddCommGroup C] [Module κ C]
    (A : B → F →ₗ[κ] G) (j : C →ₗ[κ] F) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ b u, δ * ‖u‖ ≤ ‖A b (j u)‖)
    (hrange : ∀ b, LinearMap.range ((A b).comp j) = LinearMap.range (A b)) :
    ∃ T : B → F →ₗ[κ] C, ∀ b x u, T b x = u ↔ A b (j u) = A b x := by
  classical
  let L : B → C →ₗ[κ] G := fun b ↦ (A b).comp j
  have hL (b : B) : Function.Injective (L b) := by
    obtain ⟨K, hK⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := L b)).2
      ⟨δ, hδ, hbound b⟩
    exact hK.injective
  have hmem (b : B) (x : F) : A b x ∈ LinearMap.range (L b) := by
    rw [show LinearMap.range (L b) = LinearMap.range (A b) from hrange b]
    exact LinearMap.mem_range_self (A b) x
  let T : B → F →ₗ[κ] C := fun b ↦
    LinearMap.codRestrictOfInjective (A b) (L b) (hL b) (hmem b)
  have hT (b : B) (x : F) : L b (T b x) = A b x :=
    LinearMap.codRestrictOfInjective_comp_apply (A b) (L b) (hL b) (hmem b) x
  refine ⟨T, ?_⟩
  intro b x u
  constructor
  · intro h
    change L b u = A b x
    rw [← h]
    exact hT b x
  · intro h
    apply hL b
    exact (hT b x).trans h.symm

end LinearMap

namespace ContinuousLinearMap

/-- Jointly continuous linear coefficients with the factorization characteristic law
give kernel projections that kill the same fixed coefficient map. -/
private theorem exists_kernel_projections_of_continuous_coefficients
    {κ : Type uκ} [CommRing κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module κ F]
    {G : Type uG} [AddCommGroup G] [TopologicalSpace G] [Module κ G]
    {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [Module κ C]
    (A : B → F →L[κ] G) (j : C →L[κ] F) (T : B → F →ₗ[κ] C)
    (hT : ∀ b x u, T b x = u ↔ A b (j u) = A b x)
    (hTcont : Continuous (fun z : B × F ↦ T z.1 z.2)) :
    ∃ p : B → F →L[κ] F,
      Continuous (fun z : B × F ↦ p z.1 z.2) ∧
      (∀ b x, A b (p b x) = 0) ∧
      (∀ b x, A b x = 0 → p b x = x) ∧
      ∀ b c x, p b (p c x) = p b x := by
  let t : B → F →L[κ] C := fun b ↦
    ⟨T b, hTcont.comp (continuous_const.prodMk continuous_id)⟩
  let p : B → F →L[κ] F := fun b ↦ ContinuousLinearMap.id κ F - j.comp (t b)
  have hp_apply (b : B) (x : F) : p b x = x - j (T b x) := rfl
  have hpcont : Continuous (fun z : B × F ↦ p z.1 z.2) :=
    (continuous_snd.sub (j.continuous.comp hTcont)).congr
      (fun z ↦ (hp_apply z.1 z.2).symm)
  have hfactor (b : B) (x : F) : A b (j (T b x)) = A b x :=
    (hT b x (T b x)).1 rfl
  have hTj (b : B) (u : C) : T b (j u) = u := (hT b (j u) u).2 rfl
  have hTker (b : B) (x : F) (hx : A b x = 0) : T b x = 0 := by
    apply (hT b x 0).2
    rw [map_zero, map_zero, hx]
  have hpj (b : B) (u : C) : p b (j u) = 0 := by
    rw [hp_apply, hTj, sub_self]
  refine ⟨p, hpcont, ?_, ?_, ?_⟩
  · intro b x
    rw [hp_apply, map_sub, hfactor, sub_self]
  · intro b x hx
    rw [hp_apply, hTker b x hx, map_zero, sub_zero]
  · intro b c x
    rw [hp_apply c x, map_sub, hpj, sub_zero]

/-- A continuous family of linear maps admits jointly continuous projections onto its
kernels if the composites with a fixed continuous linear map have the same ranges as the
original maps and satisfy a uniform positive lower norm bound. The projections have a
common complement: `p b (p c x) = p b x`.

The coefficient space must be normed so that the lower bound gives injectivity. The source
only needs to be a topological additive group, the target may be seminormed, and the scalar
ring needs no norm or topology. No completeness or finite-dimensionality is required.
The coefficients are obtained by algebraic restriction to the range, not by a retraction
from the ambient target. -/
theorem exists_kernel_projections_of_uniform_lower_bound
    {κ : Type uκ} [CommRing κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module κ F]
    {G : Type uG} [SeminormedAddCommGroup G] [Module κ G]
    {C : Type uC} [NormedAddCommGroup C] [Module κ C]
    (A : B → F →L[κ] G) (hA : Continuous (fun z : B × F ↦ A z.1 z.2))
    (j : C →L[κ] F) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ b u, δ * ‖u‖ ≤ ‖A b (j u)‖)
    (hrange : ∀ b, LinearMap.range ((A b).comp j).toLinearMap =
      LinearMap.range (A b).toLinearMap) :
    ∃ p : B → F →L[κ] F,
      Continuous (fun z : B × F ↦ p z.1 z.2) ∧
      (∀ b x, A b (p b x) = 0) ∧
      (∀ b x, A b x = 0 → p b x = x) ∧
      ∀ b c x, p b (p c x) = p b x := by
  obtain ⟨T, hT⟩ := LinearMap.exists_coefficients_of_uniform_lower_bound
    (fun b ↦ (A b).toLinearMap) j.toLinearMap hδ hbound
    (fun b ↦ by simpa only [ContinuousLinearMap.toLinearMap_comp] using hrange b)
  have hfactor (b : B) (x : F) : A b (j (T b x)) = A b x :=
    (hT b x (T b x)).1 rfl
  have hTcont : Continuous (fun z : B × F ↦ T z.1 z.2) :=
    LinearMap.continuous_factorization_of_uniform_lower_bound
      (A := fun b ↦ (A b).toLinearMap) (j := j.toLinearMap)
      (T := fun b x ↦ T b x) hA hfactor hδ hbound
  exact exists_kernel_projections_of_continuous_coefficients A j T hT hTcont

end ContinuousLinearMap
