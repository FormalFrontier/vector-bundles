/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Maps.FiberwiseSplitting
public import VectorBundles.Topology.Module.FiniteCoordinates
public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional
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
seminormed space `A`, with `ρ b (β b u) = u`. Continuity of the two total maps
gives `ContinuousMap.fiberwiseProjection`, an operator-seminorm-continuous
family of idempotents acting by `β b (ρ b a)`. The scalar field need not be
complete, and the ambient space need not be separated or complete.

The prescribed projection has the same kernel as `ρ b`. The complementary
family is the existing continuous-map expression
`1 - (ContinuousMap.subtypeVal _).comp P`. Its residual action and the
decomposition laws use the prescribed maps on the original carriers.
Extensionality is inherited from continuous maps, subtypes and continuous
linear maps.

## Implementation notes

Composing the two total maps gives joint continuity of `β b (ρ b a)`.
Fixed-base slices give individual continuous linear maps, and
`ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional` detects
continuity of their family from fixed-vector evaluations. The operators retain
the original operator-seminorm topology. The ambient space keeps its original
seminorm and scalar action; the fibres retain their given module structures
and subspace topologies, without fibre norms or continuity of fibre operations.
No orthogonality or commutation at different base points is asserted.

## References

* `ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional` supplies the
  continuity criterion for the original finite-dimensional seminormed domain.
* Mathlib's `IsIdempotentElem` and `ContinuousMap` interfaces provide the
  idempotence tag, complementary algebra and pointwise continuous-map operations.
-/

@[expose] public section

universe uK uA uB uT

namespace ContinuousMap

section Seminormed

variable {K : Type uK} [kK : NontriviallyNormedField K]
  {A : Type uA} [sA : SeminormedAddCommGroup A]
  [nA : @NormedSpace K A kK.toNormedField sA]
  [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
    sA.toAddCommGroup nA.toModule]
  {B : Type uB} [tB : TopologicalSpace B]
  {T : Type uT} [tT : TopologicalSpace T]
  (p : T → B) [aF : ∀ b, AddCommMonoid {t : T // p t = b}]
  [mF : ∀ b, Module K {t : T // p t = b}]
  (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
  (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
  (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
  (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
  (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val))

/-- The prescribed projections `β b ∘ ρ b`, as an operator-seminorm-continuous
family of idempotent continuous linear endomorphisms on a finite-dimensional
seminormed space. The scalar field may be incomplete, and the ambient space need
not be separated or complete.

The ambient space keeps its original seminorm, scalar action and topology.
The equality fibres keep their original module structures and subspace
topologies, without norms or continuity of their module operations. -/
def fiberwiseProjection :
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
    apply (ContinuousLinearMap.continuous_iff_apply_of_finiteDimensional
      (kK := kK) (sA := sA) (nA := nA) (hA := hA)
      (sG := sA) (nG := nA) P).mpr
    intro a
    exact hP.comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : B ↦ a)))
  exact ⟨fun b ↦ ⟨P b, hIdem b⟩, hPc.subtype_mk (fun b ↦ hIdem b)⟩

/-- The prescribed projection acts by the original linear composition. -/
@[simp]
theorem fiberwiseProjection_apply (b : B) (a : A) :
    (fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val a =
      β b (ρ b a) := rfl

/-- The prescribed projection has the same kernel as the prescribed retraction. -/
@[simp]
theorem fiberwiseProjection_ker (b : B) :
    LinearMap.ker
      ((fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val.toLinearMap) =
        LinearMap.ker (ρ b) := by
  have hP :
      (fiberwiseProjection p β ρ hρβ hβTotal hρTotal b).val.toLinearMap =
        (β b).comp (ρ b) := by
    ext a
    exact fiberwiseProjection_apply p β ρ hρβ hβTotal hρTotal b a
  rw [hP]
  exact LinearMap.ker_comp_of_ker_eq_bot (ρ b)
    (LinearMap.ker_eq_bot_of_injective (hρβ b).injective)

local notation "P" => fiberwiseProjection p β ρ hρβ hβTotal hρTotal
local notation "Q" =>
  (1 : ContinuousMap B (A →L[K] A)) -
    ContinuousMap.comp (ContinuousMap.subtypeVal (fun R : A →L[K] A ↦ IsIdempotentElem R)) P

/-- The existing complementary continuous-map expression acts by the residual. -/
theorem fiberwiseProjection_complement_apply (b : B) (a : A) :
    Q b a = a - β b (ρ b a) := rfl

/-- The complementary component lies in the kernel of the prescribed retraction.
Injectivity of the encoder reduces the calculation to subtraction in the ambient space. -/
theorem fiberwiseProjection_rho_complement (b : B) (a : A) :
    ρ b (Q b a) = 0 := by
  apply (hρβ b).injective
  rw [fiberwiseProjection_complement_apply]
  simpa only [fiberwiseProjection_apply, hρβ b (ρ b a), sub_self,
    map_zero] using (map_sub (P b).val a (β b (ρ b a)))

/-- The complementary family vanishes on the image of the prescribed encoder. -/
theorem fiberwiseProjection_complement_beta
    (b : B) (u : {t : T // p t = b}) :
    Q b (β b u) = 0 := by
  rw [fiberwiseProjection_complement_apply, hρβ b u, sub_self]

/-- Each ambient vector is the sum of its prescribed image and kernel components. -/
theorem fiberwiseProjection_add_complement_apply (b : B) (a : A) :
    (P b).val a + Q b a = a := by
  rw [fiberwiseProjection_apply,
    fiberwiseProjection_complement_apply, add_comm, sub_add_cancel]

end Seminormed

section ModuleTopology

/-- Deprecated spelling of `fiberwiseProjection` with the original normed-space
and module-topology hypotheses. -/
def fiberwiseProjectionOfIsModuleTopology
    {K : Type uK} [NontriviallyNormedField K]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
    [IsModuleTopology K A]
    {B : Type uB} [TopologicalSpace B] {T : Type uT} [TopologicalSpace T]
    (p : T → B) [∀ b, AddCommMonoid {t : T // p t = b}]
    [∀ b, Module K {t : T // p t = b}]
    (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
    (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
    (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
    (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
    (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val)) :
    ContinuousMap B {P : A →L[K] A // IsIdempotentElem P} :=
  fiberwiseProjection p β ρ hρβ hβTotal hρTotal

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

/-- The prescribed projection acts by the original linear composition. -/
@[simp]
theorem fiberwiseProjectionOfIsModuleTopology_apply (b : B) (a : A) :
    (fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal b).val a =
      β b (ρ b a) :=
  fiberwiseProjection_apply p β ρ hρβ hβTotal hρTotal b a

/-- The prescribed projection has the same kernel as the prescribed retraction. -/
@[simp]
theorem fiberwiseProjectionOfIsModuleTopology_ker (b : B) :
    LinearMap.ker
      ((fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal b).val.toLinearMap) =
        LinearMap.ker (ρ b) :=
  fiberwiseProjection_ker p β ρ hρβ hβTotal hρTotal b

local notation "P" => fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal
local notation "Q" =>
  (1 : ContinuousMap B (A →L[K] A)) -
    ContinuousMap.comp (ContinuousMap.subtypeVal (fun R : A →L[K] A ↦ IsIdempotentElem R)) P

/-- The existing complementary continuous-map expression acts by the residual. -/
theorem fiberwiseProjectionOfIsModuleTopology_complement_apply (b : B) (a : A) :
    Q b a = a - β b (ρ b a) :=
  fiberwiseProjection_complement_apply p β ρ hρβ hβTotal hρTotal b a

/-- The complementary component lies in the kernel of the prescribed retraction.
Injectivity of the encoder reduces the calculation to subtraction in the ambient space. -/
theorem fiberwiseProjectionOfIsModuleTopology_rho_complement (b : B) (a : A) :
    ρ b (Q b a) = 0 :=
  fiberwiseProjection_rho_complement p β ρ hρβ hβTotal hρTotal b a

/-- The complementary family vanishes on the image of the prescribed encoder. -/
theorem fiberwiseProjectionOfIsModuleTopology_complement_beta
    (b : B) (u : {t : T // p t = b}) :
    Q b (β b u) = 0 :=
  fiberwiseProjection_complement_beta p β ρ hρβ hβTotal hρTotal b u

/-- Each ambient vector is the sum of its prescribed image and kernel components. -/
theorem fiberwiseProjectionOfIsModuleTopology_add_complement_apply (b : B) (a : A) :
    (P b).val a + Q b a = a :=
  fiberwiseProjection_add_complement_apply p β ρ hρβ hβTotal hρTotal b a

end ModuleTopology

/-- The module-topology specialization is the same continuous family of tagged
idempotents on the original ambient space. -/
theorem fiberwiseProjectionOfIsModuleTopology_eq
    {K : Type uK} [NontriviallyNormedField K]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
    [IsModuleTopology K A]
    {B : Type uB} [TopologicalSpace B] {T : Type uT} [TopologicalSpace T]
    (p : T → B) [∀ b, AddCommMonoid {t : T // p t = b}]
    [∀ b, Module K {t : T // p t = b}]
    (β : ∀ b, {t : T // p t = b} →ₗ[K] A)
    (ρ : ∀ b, A →ₗ[K] {t : T // p t = b})
    (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
    (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
    (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val)) :
    fiberwiseProjectionOfIsModuleTopology p β ρ hρβ hβTotal hρTotal =
      fiberwiseProjection p β ρ hρβ hβTotal hρTotal := rfl

attribute [deprecated fiberwiseProjection (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology
attribute [deprecated fiberwiseProjection_apply (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_apply
attribute [deprecated fiberwiseProjection_ker (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_ker
attribute [deprecated fiberwiseProjection_complement_apply (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_complement_apply
attribute [deprecated fiberwiseProjection_rho_complement (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_rho_complement
attribute [deprecated fiberwiseProjection_complement_beta (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_complement_beta
attribute [deprecated fiberwiseProjection_add_complement_apply (since := "2026-11-03")]
  fiberwiseProjectionOfIsModuleTopology_add_complement_apply

end ContinuousMap
