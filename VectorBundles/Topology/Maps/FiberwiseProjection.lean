/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Maps.FiberwiseSplitting
public import VectorBundles.Topology.Module.FiniteCoordinates
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous families of prescribed fibre projections

Let `p : T → B` have given module structures on its equality fibres, and let
`β b` and `ρ b` be linear maps between those fibres and a finite-dimensional
normed space `A`, with `ρ b (β b u) = u`. If `A` has the module topology,
continuity of the two total maps gives
`ContinuousMap.fiberwiseProjectionOfIsModuleTopology`, an operator-norm-continuous
family of idempotents acting by `β b (ρ b a)`.

Over a complete scalar field, `ContinuousMap.fiberwiseProjection` gives the same
prescribed family: the original finite-dimensional normed space has the module
topology. Neither construction requires completeness or nontriviality of `A`.

The prescribed projection has the same kernel as `ρ b`. The complementary
family is the existing continuous-map expression
`1 - (ContinuousMap.subtypeVal _).comp P`. Its residual action and the
decomposition laws use the prescribed maps on the original carriers.
Extensionality is inherited from continuous maps, subtypes and continuous
linear maps.

## Implementation notes

Composing the two total maps gives joint continuity of `β b (ρ b a)`.
Fixed-base slices give individual continuous linear maps, and
`Module.Basis.continuous_clm_apply_iff` detects continuity of their family from
a finite basis. The topology on these operators is the original operator-norm
topology. The fibres retain their given module structures and subspace
topologies; no fibre norm or continuity of fibre operations is required.
The module-topology assumption is sufficient; no necessity or minimality is
asserted. No orthogonality or commutation at different base points is asserted.
The standard finite-Pi norm is the sup norm, not a Euclidean norm.

## References

* `Module.Basis.continuous_clm_apply_iff` supplies the finite-basis continuity
  criterion on the given module topology.
* Mathlib's `isModuleTopologyOfFiniteDimensional` supplies the module topology
  on finite-dimensional Hausdorff topological vector spaces over complete fields.
* Mathlib's operator norm agrees with the bounded-convergence topology on
  continuous linear maps between normed spaces.
* Mathlib's `IsIdempotentElem` and `ContinuousMap` interfaces provide the
  idempotence tag, complementary algebra and pointwise continuous-map operations.
-/

@[expose] public section

universe uK uA uB uT

namespace ContinuousMap

section ModuleTopology

variable {K : Type uK} [NontriviallyNormedField K]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
  [IsModuleTopology K A]
  {B : Type uB} [TopologicalSpace B] {T : Type uT} [TopologicalSpace T]
  (p : T → B) [∀ b, AddCommMonoid {t : T // p t = b}]
  [∀ b, Module K {t : T // p t = b}]
  (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
  (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
  (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
  (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
  (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val))

/-- The prescribed projections `β b ∘ ρ b`, as an operator-norm-continuous
family of idempotent continuous linear endomorphisms when the ambient space has
the module topology.

The ambient finite-dimensional space keeps its original norm and topology.
The equality fibres keep their original module structures and subspace
topologies, without norms or continuity of their module operations. -/
def fiberwiseProjectionOfIsModuleTopology :
    ContinuousMap B {P : A →L[K] A // IsIdempotentElem P} := by
  have hβ (b : B) (u : {t : T // p t = b}) :
      β (p u.val) ⟨u.val, rfl⟩ = β b u := by
    rcases u with ⟨t, h⟩
    cases h
    rfl
  have hP : Continuous (fun y : B × A ↦ β y.1 (ρ y.1 y.2)) :=
    (hβTotal.comp hρTotal).snd.congr (fun y ↦ hβ y.1 (ρ y.1 y.2))
  let P (b : B) : A →L[K] A :=
    { toLinearMap := (β b).comp (ρ b)
      cont := hP.comp ((continuous_const : Continuous (fun _ : A ↦ b)).prodMk
        continuous_id) }
  have hIdem (b : B) : IsIdempotentElem (P b) := by
    change P b * P b = P b
    ext a
    exact congrArg (β b) (hρβ b (ρ b a))
  have hPc : Continuous P := by
    apply (Module.Basis.continuous_clm_apply_iff
      (Module.Basis.ofVectorSpace K A)).mpr
    intro i
    exact hP.comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : B ↦ Module.Basis.ofVectorSpace K A i)))
  exact ⟨fun b ↦ ⟨P b, hIdem b⟩, hPc.subtype_mk (fun b ↦ hIdem b)⟩

/-- The prescribed projection acts by the original linear composition. -/
@[simp]
theorem fiberwiseProjectionOfIsModuleTopology_apply (b : B) (a : A) :
    (fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal b).val a =
      β b (ρ b a) := rfl

/-- The prescribed projection has the same kernel as the prescribed retraction. -/
@[simp]
theorem fiberwiseProjectionOfIsModuleTopology_ker (b : B) :
    LinearMap.ker
      ((fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal b).val.toLinearMap) =
        LinearMap.ker (ρ b) := by
  have hP :
      (fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal b).val.toLinearMap =
        (β b).comp (ρ b) := by
    ext a
    exact fiberwiseProjectionOfIsModuleTopology_apply p β ρ hρβ hβTotal hρTotal b a
  rw [hP]
  exact LinearMap.ker_comp_of_ker_eq_bot (ρ b)
    (LinearMap.ker_eq_bot_of_injective (hρβ b).injective)

local notation "P" => fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal
local notation "Q" =>
  (1 : ContinuousMap B (A →L[K] A)) -
    ContinuousMap.comp (ContinuousMap.subtypeVal (fun R : A →L[K] A ↦ IsIdempotentElem R)) P

/-- The existing complementary continuous-map expression acts by the residual. -/
theorem fiberwiseProjectionOfIsModuleTopology_complement_apply (b : B) (a : A) :
    Q b a = a - β b (ρ b a) := rfl

/-- The complementary component lies in the kernel of the prescribed retraction.
Injectivity of the encoder reduces the calculation to subtraction in the ambient space. -/
theorem fiberwiseProjectionOfIsModuleTopology_rho_complement (b : B) (a : A) :
    ρ b (Q b a) = 0 := by
  apply (hρβ b).injective
  rw [fiberwiseProjectionOfIsModuleTopology_complement_apply]
  simpa only [fiberwiseProjectionOfIsModuleTopology_apply, hρβ b (ρ b a), sub_self,
    map_zero] using (map_sub (P b).val a (β b (ρ b a)))

/-- The complementary family vanishes on the image of the prescribed encoder. -/
theorem fiberwiseProjectionOfIsModuleTopology_complement_beta
    (b : B) (u : {t : T // p t = b}) :
    Q b (β b u) = 0 := by
  rw [fiberwiseProjectionOfIsModuleTopology_complement_apply, hρβ b u, sub_self]

/-- Each ambient vector is the sum of its prescribed image and kernel components. -/
theorem fiberwiseProjectionOfIsModuleTopology_add_complement_apply (b : B) (a : A) :
    (P b).val a + Q b a = a := by
  rw [fiberwiseProjectionOfIsModuleTopology_apply,
    fiberwiseProjectionOfIsModuleTopology_complement_apply, add_comm, sub_add_cancel]

end ModuleTopology

section CompleteField

variable {K : Type uK} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
  {B : Type uB} [TopologicalSpace B] {T : Type uT} [TopologicalSpace T]
  (p : T → B) [∀ b, AddCommMonoid {t : T // p t = b}]
  [∀ b, Module K {t : T // p t = b}]
  (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
  (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
  (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
  (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
  (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val))

/-- The prescribed projections `β b ∘ ρ b`, as an operator-norm-continuous
family of idempotent continuous linear endomorphisms over a complete scalar field.

The ambient finite-dimensional space keeps its original norm and topology.
The equality fibres keep their original module structures and subspace
topologies, without norms or continuity of their module operations. -/
def fiberwiseProjection : ContinuousMap B {P : A →L[K] A // IsIdempotentElem P} := by
  letI : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal

/-- The prescribed projection acts by the original linear composition. -/
@[simp]
theorem fiberwiseProjection_apply (b : B) (a : A) :
    (fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val a = β b (ρ b a) := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_apply p β ρ hρβ hβTotal hρTotal b a

/-- The prescribed projection has the same kernel as the prescribed retraction. -/
@[simp]
theorem fiberwiseProjection_ker (b : B) :
    LinearMap.ker
      ((fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val.toLinearMap) =
        LinearMap.ker (ρ b) := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_ker p β ρ hρβ hβTotal hρTotal b

local notation "P" => fiberwiseProjection p β ρ hρβ hβTotal hρTotal
local notation "Q" =>
  (1 : ContinuousMap B (A →L[K] A)) -
    ContinuousMap.comp (ContinuousMap.subtypeVal (fun R : A →L[K] A ↦ IsIdempotentElem R)) P

/-- The existing complementary continuous-map expression acts by the residual. -/
theorem fiberwiseProjection_complement_apply (b : B) (a : A) :
    Q b a = a - β b (ρ b a) := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_complement_apply p β ρ hρβ hβTotal hρTotal b a

/-- The complementary component lies in the kernel of the prescribed retraction. -/
theorem fiberwiseProjection_rho_complement (b : B) (a : A) :
    ρ b (Q b a) = 0 := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_rho_complement p β ρ hρβ hβTotal hρTotal b a

/-- The complementary family vanishes on the image of the prescribed encoder. -/
theorem fiberwiseProjection_complement_beta (b : B) (u : {t : T // p t = b}) :
    Q b (β b u) = 0 := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_complement_beta p β ρ hρβ hβTotal hρTotal b u

/-- Each ambient vector is the sum of its prescribed image and kernel components. -/
theorem fiberwiseProjection_add_complement_apply (b : B) (a : A) :
    (P b).val a + Q b a = a := by
  have : IsModuleTopology K A := isModuleTopologyOfFiniteDimensional
  exact fiberwiseProjectionOfIsModuleTopology_add_complement_apply p β ρ hρβ hβTotal hρTotal b a

end CompleteField

end ContinuousMap
