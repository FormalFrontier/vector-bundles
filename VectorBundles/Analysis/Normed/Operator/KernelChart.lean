/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel

/-! # Kernel charts for families of continuous linear idempotents

A continuous family of idempotents on a complete normed space has local
product charts on its kernel total space, with the inherited topology.
-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

universe uK uA uX

variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
variable {X : Type uX}

/-- The composition transport between two idempotents. -/
def kernelTransport (P : X → A →L[K] A) (x₀ x : X) : A →L[K] A :=
  P x * P x₀ + (1 - P x) * (1 - P x₀)

/-- The canonical half-unit neighborhood for the transport. -/
def kernelChartDomain (P : X → A →L[K] A) (x₀ : X) : Set X :=
  {x | ‖kernelTransport P x₀ x - 1‖ < (1 / 2 : ℝ)}

/-- The kernel total space with the inherited product-subtype topology. -/
abbrev KernelTotalSpace (P : X → A →L[K] A) (V : Set X) :=
  {z : V × A // P z.1.1 z.2 = 0}

@[simp]
theorem mem_kernelChartDomain (P : X → A →L[K] A) (x₀ x : X) :
    x ∈ kernelChartDomain P x₀ ↔
      ‖kernelTransport P x₀ x - 1‖ < (1 / 2 : ℝ) := Iff.rfl

@[simp]
theorem kernelTransport_apply (P : X → A →L[K] A) (x₀ x : X) (a : A) :
    kernelTransport P x₀ x a =
      P x (P x₀ a) + (a - P x₀ a - P x (a - P x₀ a)) := rfl

@[simp]
theorem kernelTransport_self (P : X → A →L[K] A) (x₀ : X)
    (h : P x₀ * P x₀ = P x₀) : kernelTransport P x₀ x₀ = 1 := by
  simp only [kernelTransport, sub_mul, mul_sub, one_mul, mul_one, h]
  abel

/-- The center belongs to its transport domain for an idempotent family. -/
theorem self_mem_kernelChartDomain (P : X → A →L[K] A) (x₀ : X)
    (h : P x₀ * P x₀ = P x₀) : x₀ ∈ kernelChartDomain P x₀ := by
  simp [kernelChartDomain, kernelTransport_self P x₀ h]

private theorem transport_semiconj {R : Type*} [Ring R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    SemiconjBy (q * p + (1 - q) * (1 - p)) p q := by
  change (q * p + (1 - q) * (1 - p)) * p =
    q * (q * p + (1 - q) * (1 - p))
  calc
    _ = q * p := by
      rw [add_mul, mul_assoc, hp.eq, mul_assoc,
        hp.one_sub_mul_self, mul_zero, add_zero]
    _ = _ := by
      rw [mul_add, ← mul_assoc, hq.eq, ← mul_assoc,
        hq.mul_one_sub_self, zero_mul, add_zero]

/-- The transport intertwines two idempotents without a commutation assumption. -/
theorem kernelTransport_intertwines (P : X → A →L[K] A) (x₀ x : X)
    (h₀ : P x₀ * P x₀ = P x₀) (hx : P x * P x = P x) :
    P x * kernelTransport P x₀ x = kernelTransport P x₀ x * P x₀ :=
  (transport_semiconj h₀ hx).eq.symm

variable [TopologicalSpace X]

/-- The transport depends continuously on a continuous operator family. -/
theorem continuous_kernelTransport (P : X → A →L[K] A) (hP : Continuous P) (x₀ : X) :
    Continuous (kernelTransport P x₀) :=
  (hP.mul continuous_const).add ((continuous_const.sub hP).mul continuous_const)

/-- The half-unit transport domain is open. -/
theorem isOpen_kernelChartDomain (P : X → A →L[K] A) (hP : Continuous P) (x₀ : X) :
    IsOpen (kernelChartDomain P x₀) :=
  isOpen_lt ((continuous_kernelTransport P hP x₀).sub continuous_const).norm continuous_const

/-- A chart with the prescribed inverse-transport formulas. -/
structure IsKernelChart (P : X → A →L[K] A) (x₀ : X)
    (V : Set X) (e : KernelTotalSpace P V ≃ₜ V × (P x₀).ker) : Prop where
  base_apply (z) : (e z).1 = z.1.1
  vector_apply (z) : ((e z).2 : A) =
    Ring.inverse (kernelTransport P x₀ z.1.1.1) z.1.2
  base_symm_apply (y) : (e.symm y).1.1 = y.1
  vector_symm_apply (y) : (e.symm y).1.2 =
    kernelTransport P x₀ y.1.1 (y.2 : A)

/-- All outputs required of a local kernel chart. No chart is an input. -/
structure KernelChart (P : X → A →L[K] A) (x₀ : X) where
  isOpen_domain : IsOpen (kernelChartDomain P x₀)
  mem_domain : x₀ ∈ kernelChartDomain P x₀
  /-- Ambient equivalences realizing the composition transport. -/
  ambientEquiv : kernelChartDomain P x₀ → A ≃L[K] A
  transport_eq (x) : (ambientEquiv x : A →L[K] A) = kernelTransport P x₀ x.1
  continuous_transport : Continuous (fun x => (ambientEquiv x : A →L[K] A))
  continuous_inverse : Continuous (fun x => ((ambientEquiv x).symm : A →L[K] A))
  /-- The base-preserving homeomorphism onto the central kernel product. -/
  homeomorph : KernelTotalSpace P (kernelChartDomain P x₀) ≃ₜ
    kernelChartDomain P x₀ × (P x₀).ker
  isKernelChart : IsKernelChart P x₀ (kernelChartDomain P x₀) homeomorph
  /-- The continuous-linear equivalence on each kernel fibre. -/
  fibreEquiv (x : kernelChartDomain P x₀) : (P x.1).ker ≃L[K] (P x₀).ker
  fibre_apply (x : kernelChartDomain P x₀) (a : (P x.1).ker) :
    (fibreEquiv x a : A) = (ambientEquiv x).symm (a : A)
  fibre_symm_apply (x : kernelChartDomain P x₀) (v : (P x₀).ker) :
    ((fibreEquiv x).symm v : A) = ambientEquiv x (v : A)
  homeomorph_fibre (z) :
    (homeomorph z).2 = fibreEquiv z.1.1 ⟨z.1.2, z.2⟩
  homeomorph_center (v : (P x₀).ker) :
    homeomorph ⟨(⟨x₀, mem_domain⟩, (v : A)), v.2⟩ = (⟨x₀, mem_domain⟩, v)


/-- The canonical local product chart for a continuous family of idempotents
on a complete normed space, with its inherited kernel-total-space topology. -/
def kernelChart [CompleteSpace A] (P : X → A →L[K] A) (hP : Continuous P)
    (hIdem : ∀ x, P x * P x = P x) (x₀ : X) : KernelChart P x₀ := by
  let U := kernelTransport P x₀
  let V := kernelChartDomain P x₀
  have hU : Continuous U := continuous_kernelTransport P hP x₀
  let u (x : V) : (A →L[K] A)ˣ := Units.oneSub (1 - U x.1) (by
    rw [norm_sub_rev]
    exact x.property.trans (div_lt_self zero_lt_one one_lt_two))
  have hu (x : V) : (u x : A →L[K] A) = U x.1 := by
    change 1 - (1 - U x.1) = U x.1
    abel
  let e (x : V) : A ≃L[K] A := ContinuousLinearEquiv.ofUnit (u x)
  have heU (x : V) : (e x : A →L[K] A) = kernelTransport P x₀ x.1 := hu x
  have hInv (x : V) : ((e x).symm : A →L[K] A) = Ring.inverse (U x.1) := by
    change (↑((u x)⁻¹) : A →L[K] A) = Ring.inverse (U x.1)
    rw [← hu x, Ring.inverse_unit]
  have hCInv : Continuous (fun x : V => Ring.inverse (U x.1)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hi : ContinuousAt Ring.inverse (U x.1) := by
      rw [← hu x]
      exact NormedRing.inverse_continuousAt (u x)
    exact (hi.comp hU.continuousAt).comp continuous_subtype_val.continuousAt
  have heInv : Continuous (fun x : V => ((e x).symm : A →L[K] A)) := by
    simpa only [hInv] using hCInv
  have hI (x : V) (a : A) : P x.1 (e x a) = e x (P x₀ a) := by
    change P x.1 ((e x : A →L[K] A) a) = (e x : A →L[K] A) (P x₀ a)
    rw [heU x]
    exact congrArg (fun f : A →L[K] A => f a)
      (kernelTransport_intertwines P x₀ x.1 (hIdem x₀) (hIdem x.1))
  have hopen := isOpen_kernelChartDomain P hP x₀
  have hmem := self_mem_kernelChartDomain P x₀ (hIdem x₀)
  have he : Continuous (fun x => (e x : A →L[K] A)) := by
    simpa only [Function.comp_def, heU] using
      (continuous_kernelTransport P hP x₀).comp continuous_subtype_val
  have forward (x : V) {v : A} (hv : P x₀ v = 0) :
      P x.1 (e x v) = 0 := by
    rw [hI x v, hv, map_zero]
  have backward (x : V) {a : A} (ha : P x.1 a = 0) :
      P x₀ ((e x).symm a) = 0 := by
    apply (e x).injective
    rw [← hI x ((e x).symm a), (e x).apply_symm_apply, ha, map_zero]
  have hmap (x : V) :
      ((P x.1).ker).map ((e x).symm : A →ₗ[K] A) = (P x₀).ker := by
    ext a
    constructor
    · intro ha
      rcases Submodule.mem_map.mp ha with ⟨b, hb, rfl⟩
      exact backward x hb
    · intro ha
      exact Submodule.mem_map.mpr
        ⟨e x a, forward x ha, (e x).symm_apply_apply a⟩
  let fibre (x : V) : (P x.1).ker ≃L[K] (P x₀).ker :=
    (e x).symm.ofSubmodules _ _ (hmap x)
  let H : KernelTotalSpace P V ≃ₜ V × (P x₀).ker :=
    { toFun := fun z =>
        (z.1.1, ⟨(e z.1.1).symm z.1.2, backward z.1.1 z.2⟩)
      invFun := fun y =>
        ⟨(y.1, e y.1 (y.2 : A)), forward y.1 y.2.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (e z.1.1).apply_symm_apply z.1.2
      right_inv := by
        intro y
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact (e y.1).symm_apply_apply (y.2 : A)
      continuous_toFun := by
        exact (continuous_fst.comp continuous_subtype_val).prodMk
          (((heInv.comp (continuous_fst.comp continuous_subtype_val)).clm_apply
            (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
      continuous_invFun := by
        exact (continuous_fst.prodMk
          ((he.comp continuous_fst).clm_apply
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _ }
  refine
    { isOpen_domain := hopen
      mem_domain := hmem
      ambientEquiv := e
      transport_eq := heU
      continuous_transport := he
      continuous_inverse := heInv
      homeomorph := H
      isKernelChart := ?_
      fibreEquiv := fibre
      fibre_apply := ?_
      fibre_symm_apply := ?_
      homeomorph_fibre := ?_
      homeomorph_center := ?_ }
  · refine
      { base_apply := fun _ => rfl
        vector_apply := ?_
        base_symm_apply := fun _ => rfl
        vector_symm_apply := ?_ }
    · intro z
      change ((e z.1.1).symm : A →L[K] A) z.1.2 = _
      rw [hInv z.1.1]
    · intro y
      change (e y.1 : A →L[K] A) (y.2 : A) = _
      rw [heU y.1]
  · intro x a
    rfl
  · intro x v
    rfl
  · intro z
    rfl
  · intro v
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (e ⟨x₀, hmem⟩).symm (v : A) = (v : A)
      apply (e ⟨x₀, hmem⟩).injective
      rw [(e ⟨x₀, hmem⟩).apply_symm_apply]
      change (v : A) = (e ⟨x₀, hmem⟩ : A →L[K] A) (v : A)
      rw [heU ⟨x₀, hmem⟩, kernelTransport_self P x₀ (hIdem x₀)]
      rfl


namespace KernelChart

@[simp]
theorem apply_eq (P : X → A →L[K] A) (x₀ : X) (c : KernelChart P x₀)
    (z : KernelTotalSpace P (kernelChartDomain P x₀)) :
    c.homeomorph z = (z.1.1, c.fibreEquiv z.1.1 ⟨z.1.2, z.2⟩) :=
  Prod.ext (c.isKernelChart.base_apply z) (c.homeomorph_fibre z)

@[simp]
theorem symm_apply_val (P : X → A →L[K] A) (x₀ : X) (c : KernelChart P x₀)
    (y : kernelChartDomain P x₀ × (P x₀).ker) :
    (c.homeomorph.symm y).1 = (y.1, kernelTransport P x₀ y.1.1 (y.2 : A)) :=
  Prod.ext (c.isKernelChart.base_symm_apply y) (c.isKernelChart.vector_symm_apply y)

end KernelChart

/-- Local kernel charts for every continuous family of idempotents on a given
complete normed space. -/
def KernelChartExistence : Prop :=
  ∀ (K : Type uK) [NontriviallyNormedField K]
    (A : Type uA) [NormedAddCommGroup A] [NormedSpace K A] [CompleteSpace A]
    (X : Type uX) [TopologicalSpace X] (P : X → A →L[K] A),
    Continuous P → (∀ x, P x * P x = P x) → ∀ x₀, Nonempty (KernelChart P x₀)

/-- Specialization of the universal kernel-chart assertion to a given family. -/
theorem KernelChartExistence.specialize (h : KernelChartExistence.{uK, uA, uX})
    [CompleteSpace A] (P : X → A →L[K] A) (hP : Continuous P)
    (hIdem : ∀ x, P x * P x = P x) (x₀ : X) : Nonempty (KernelChart P x₀) :=
  h K A X P hP hIdem x₀

/-- Every continuous family of idempotents on a complete normed space has
the prescribed local kernel charts. -/
theorem kernelChartExistence : KernelChartExistence.{uK, uA, uX} := by
  intro K _ A _ _ _ X _ P hP hIdem x₀
  exact ⟨kernelChart P hP hIdem x₀⟩

end ContinuousLinearMap

