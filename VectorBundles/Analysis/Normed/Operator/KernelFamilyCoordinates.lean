/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Operator.UnitGramContinuity
public import ProjectiveModules.Topology.KernelComparison

/-!
# Fixed-kernel coordinates for supplied split families

Let `Γ d : H →L[K] A` have supplied linear retractions `r d : A →ₗ[K] H`.
A fixed continuous linear map `q0 : A →L[K] H` need not itself retract every
`Γ d`: it suffices that `q0.comp (Γ d)` is a unit in the continuous-linear
endomorphism ring. The existing `inverseGramComp` normalizes this comparison.

`kerFamilyHomeomorphOfIsUnit` identifies the original product-subtype total
kernel of `r` with the product of the parameter space and the fixed kernel of
`q0`. Its only continuity input is the joint difference of the original and
normalized ambient projections. In particular, `r d` need only be linear.
`kerFamilyHomeomorphOfContinuous` supplies convenient sufficient hypotheses:
operator-seminorm continuity of `Γ` and joint continuity of the original `Γr`.

All product and subtype topologies are the original ones. The parameter space
can be empty, and no openness or completeness is assumed. In particular it may
be exactly the subtype where the continuous-linear Gram operator is a unit;
then all retraction data are needed only on that subtype. An anchor
`q0.comp (Γ d) = id` alone does not make the coordinates the identity: identity
on a fibre follows, for example, when the supplied `r d` equals `q0`.
-/

universe uX uY uZ uK uH uA uD uB

section Repack

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private def kernelProductRepack (P : X → Y → Prop) (Q : Y → Prop)
    (h : ∀ x y, P x y ↔ Q y) :
    {p : X × Y // P p.1 p.2} ≃ₜ X × {y : Y // Q y} where
  toFun p := (p.val.1, ⟨p.val.2, (h p.val.1 p.val.2).mp p.property⟩)
  invFun z := ⟨(z.1, z.2.val), (h z.1 z.2.val).mpr z.2.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  continuous_toFun := by
    exact (continuous_fst.comp continuous_subtype_val).prodMk (by
      apply Continuous.subtype_mk
      exact continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

variable (P : X → Y → Prop) (Q : Y → Prop) (h : ∀ x y, P x y ↔ Q y)

private theorem kernelProductRepack_apply_fst (p : {p : X × Y // P p.1 p.2}) :
    (kernelProductRepack P Q h p).1 = p.val.1 := rfl

private theorem kernelProductRepack_apply_snd (p : {p : X × Y // P p.1 p.2}) :
    ((kernelProductRepack P Q h p).2 : Y) = p.val.2 := rfl

private theorem kernelProductRepack_symm_apply_fst (z : X × {y : Y // Q y}) :
    ((kernelProductRepack P Q h).symm z).val.1 = z.1 := rfl

private theorem kernelProductRepack_symm_apply_snd (z : X × {y : Y // Q y}) :
    ((kernelProductRepack P Q h).symm z).val.2 = (z.2 : Y) := rfl

private theorem kernelProductRepack_trans_symm_apply
    (e : Z ≃ₜ {p : X × Y // P p.1 p.2}) (z : X × {y : Y // Q y}) :
    (e.trans (kernelProductRepack P Q h)).symm z =
      e.symm ((kernelProductRepack P Q h).symm z) := rfl

end Repack

public section

namespace ContinuousLinearMap

variable {K : Type uK} [NontriviallyNormedField K]
variable {H : Type uH} [SeminormedAddCommGroup H] [NormedSpace K H]
variable {A : Type uA} [SeminormedAddCommGroup A] [NormedSpace K A]
variable {D : Type uD} [TopologicalSpace D]

/-- Fixed-kernel coordinates for supplied split families on an all-unit domain.
Only the difference of the two ambient projections must be jointly continuous.
The source has its original product-subtype topology. -/
noncomputable def kerFamilyHomeomorphOfIsUnit
    (Γ : D → H →L[K] A) (q0 : A →L[K] H)
    (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
    (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
    (hΔ : Continuous (fun p : D × A =>
      Γ p.1 (r p.1 p.2) - Γ p.1 (inverseGramComp (Γ p.1) q0 p.2))) :
    {p : D × A // r p.1 p.2 = 0} ≃ₜ D × LinearMap.ker q0.toLinearMap :=
  (LinearMap.kerFamilyHomeomorphOfCommonRightInverse
    (fun d => (Γ d).toLinearMap) r
    (fun d => (inverseGramComp (Γ d) q0).toLinearMap)
    hr (fun d h => congrArg (fun f : H →L[K] H => f h)
      (inverseGramComp_comp_of_isUnit (hunit d))) hΔ).trans
    (kernelProductRepack
      (fun d a => inverseGramComp (Γ d) q0 a = 0) (fun a => q0 a = 0)
      (fun d a => inverseGramComp_eq_zero_iff_of_isUnit (hunit d) a))

section CharacteristicAPI

variable (Γ : D → H →L[K] A) (q0 : A →L[K] H)
variable (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
variable (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
variable (hΔ : Continuous (fun p : D × A =>
  Γ p.1 (r p.1 p.2) - Γ p.1 (inverseGramComp (Γ p.1) q0 p.2)))

/-- Fixed-kernel coordinates preserve the base point. -/
@[simp]
theorem kerFamilyHomeomorphOfIsUnit_apply_fst
    (x : {p : D × A // r p.1 p.2 = 0}) :
    (kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ x).1 = x.val.1 := by
  unfold kerFamilyHomeomorphOfIsUnit
  erw [Homeomorph.trans_apply, kernelProductRepack_apply_fst,
    LinearMap.kerFamilyHomeomorphOfCommonRightInverse_apply_fst]

/-- The forward ambient coordinate is the normalized residual. -/
@[simp]
theorem kerFamilyHomeomorphOfIsUnit_apply_snd
    (x : {p : D × A // r p.1 p.2 = 0}) :
    ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ x).2 : A) =
      x.val.2 - Γ x.val.1 (inverseGramComp (Γ x.val.1) q0 x.val.2) := by
  unfold kerFamilyHomeomorphOfIsUnit
  erw [Homeomorph.trans_apply, kernelProductRepack_apply_snd,
    LinearMap.kerFamilyHomeomorphOfCommonRightInverse_apply_snd]
  rfl

/-- Inverse coordinates also preserve the base point. -/
@[simp]
theorem kerFamilyHomeomorphOfIsUnit_symm_apply_fst
    (y : D × LinearMap.ker q0.toLinearMap) :
    ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ).symm y).val.1 = y.1 := by
  unfold kerFamilyHomeomorphOfIsUnit
  erw [kernelProductRepack_trans_symm_apply,
    LinearMap.kerFamilyHomeomorphOfCommonRightInverse_symm_apply_fst,
    kernelProductRepack_symm_apply_fst]

/-- The inverse ambient coordinate uses the original supplied retraction. -/
@[simp]
theorem kerFamilyHomeomorphOfIsUnit_symm_apply_snd
    (y : D × LinearMap.ker q0.toLinearMap) :
    ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ).symm y).val.2 =
      (y.2 : A) - Γ y.1 (r y.1 (y.2 : A)) := by
  unfold kerFamilyHomeomorphOfIsUnit
  erw [kernelProductRepack_trans_symm_apply,
    LinearMap.kerFamilyHomeomorphOfCommonRightInverse_symm_apply_snd,
    kernelProductRepack_symm_apply_fst, kernelProductRepack_symm_apply_snd]
  rfl

/-- Base and ambient-coordinate formulas uniquely characterize the coordinates. -/
theorem kerFamilyHomeomorphOfIsUnit_unique
    (e : {p : D × A // r p.1 p.2 = 0} ≃ₜ D × LinearMap.ker q0.toLinearMap)
    (hbase : ∀ x, (e x).1 = x.val.1)
    (hvalue : ∀ x, ((e x).2 : A) = x.val.2 - Γ x.val.1
      (inverseGramComp (Γ x.val.1) q0 x.val.2)) :
    e = kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ := by
  apply Homeomorph.ext
  intro x
  apply Prod.ext
  · exact (hbase x).trans (kerFamilyHomeomorphOfIsUnit_apply_fst
      Γ q0 hunit r hr hΔ x).symm
  · apply Subtype.ext
    exact (hvalue x).trans (kerFamilyHomeomorphOfIsUnit_apply_snd
      Γ q0 hunit r hr hΔ x).symm

/-- Compatibility with the original retraction gives identity on a source fibre. -/
theorem kerFamilyHomeomorphOfIsUnit_apply_snd_of_retraction_eq
    (x : {p : D × A // r p.1 p.2 = 0}) (hx : r x.val.1 = q0.toLinearMap) :
    ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ x).2 : A) = x.val.2 := by
  rw [kerFamilyHomeomorphOfIsUnit_apply_snd]
  have ha : q0 x.val.2 = 0 := by
    have ha' : q0.toLinearMap x.val.2 = 0 := by
      rw [← hx]
      exact x.property
    exact ha'
  rw [(inverseGramComp_eq_zero_iff_of_isUnit (hunit x.val.1) x.val.2).mpr ha,
    map_zero, sub_zero]

/-- Compatibility with the original retraction gives identity on a target fibre. -/
theorem kerFamilyHomeomorphOfIsUnit_symm_apply_snd_of_retraction_eq
    (y : D × LinearMap.ker q0.toLinearMap) (hy : r y.1 = q0.toLinearMap) :
    ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ).symm y).val.2 = (y.2 : A) := by
  rw [kerFamilyHomeomorphOfIsUnit_symm_apply_snd, hy]
  have hb : q0 (y.2 : A) = 0 := y.2.property
  change (y.2 : A) - Γ y.1 (q0 (y.2 : A)) = (y.2 : A)
  rw [hb, map_zero, sub_zero]

end CharacteristicAPI

/-- Operator-seminorm continuity of the section and joint continuity of the
original ambient projection suffice for continuity of the comparison difference.
No continuity of the supplied linear retractions is required. -/
theorem continuous_kerFamilyComparisonDifference_of_isUnit
    (Γ : D → H →L[K] A) (q0 : A →L[K] H)
    (hunit : ∀ d, IsUnit (q0.comp (Γ d))) (r : D → A →ₗ[K] H)
    (hΓ : Continuous Γ)
    (hP : Continuous (fun p : D × A => Γ p.1 (r p.1 p.2))) :
    Continuous (fun p : D × A => Γ p.1 (r p.1 p.2) -
      Γ p.1 (inverseGramComp (Γ p.1) q0 p.2)) := by
  have hq : Continuous (fun d => inverseGramComp (Γ d) q0) := by
    apply continuous_inverseGramComp_of_isUnit <;>
      first | assumption | exact continuous_const
  have hQ : Continuous (fun p : D × A =>
      Γ p.1 (inverseGramComp (Γ p.1) q0 p.2)) :=
    (hΓ.comp continuous_fst).clm_apply
      ((hq.comp continuous_fst).clm_apply continuous_snd)
  exact hP.sub hQ

/-- The same fixed-kernel coordinates from convenient ambient continuity data. -/
@[expose]
noncomputable def kerFamilyHomeomorphOfContinuous
    (Γ : D → H →L[K] A) (q0 : A →L[K] H)
    (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
    (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
    (hΓ : Continuous Γ)
    (hP : Continuous (fun p : D × A => Γ p.1 (r p.1 p.2))) :
    {p : D × A // r p.1 p.2 = 0} ≃ₜ D × LinearMap.ker q0.toLinearMap :=
  kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr
    (continuous_kerFamilyComparisonDifference_of_isUnit Γ q0 hunit r hΓ hP)

/-- The convenient constructor has exactly the core constructor's coordinates. -/
@[simp]
theorem kerFamilyHomeomorphOfContinuous_eq
    (Γ : D → H →L[K] A) (q0 : A →L[K] H)
    (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
    (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
    (hΓ : Continuous Γ)
    (hP : Continuous (fun p : D × A => Γ p.1 (r p.1 p.2))) :
    kerFamilyHomeomorphOfContinuous Γ q0 hunit r hr hΓ hP =
      kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr
        (continuous_kerFamilyComparisonDifference_of_isUnit Γ q0 hunit r hΓ hP) := rfl

-- On the original unit subtype, no retraction data outside the subtype are used.
noncomputable example {B : Type uB} [TopologicalSpace B]
    (Γ : B → H →L[K] A) (q0 : A →L[K] H)
    (r : {b : B // IsUnit (q0.comp (Γ b))} → A →ₗ[K] H)
    (hr : ∀ u h, r u (Γ u.val h) = h)
    (hΔ : Continuous
      (fun p : {b : B // IsUnit (q0.comp (Γ b))} × A =>
        Γ p.1.val (r p.1 p.2) -
          Γ p.1.val (inverseGramComp (Γ p.1.val) q0 p.2))) :
    {p : {b : B // IsUnit (q0.comp (Γ b))} × A // r p.1 p.2 = 0} ≃ₜ
      {b : B // IsUnit (q0.comp (Γ b))} × LinearMap.ker q0.toLinearMap :=
  kerFamilyHomeomorphOfIsUnit (fun u => Γ u.val) q0 (fun u => u.property) r hr hΔ

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {K : Type uK} [NontriviallyNormedField K]
variable {H : Type uH} [SeminormedAddCommGroup H] [NormedSpace K H]
variable {A : Type uA} [SeminormedAddCommGroup A] [NormedSpace K A]
variable {D : Type uD} [TopologicalSpace D]

private noncomputable def submoduleIdentityOfEq
    (S T : Submodule K A) (h : S = T) : S ≃L[K] T := by
  cases h
  exact ContinuousLinearEquiv.refl K S

private theorem coe_submoduleIdentityOfEq_apply
    (S T : Submodule K A) (h : S = T) (a : S) :
    (submoduleIdentityOfEq S T h a : A) = (a : A) := by
  cases h
  simp [submoduleIdentityOfEq]

private theorem coe_submoduleIdentityOfEq_symm_apply
    (S T : Submodule K A) (h : S = T) (b : T) :
    ((submoduleIdentityOfEq S T h).symm b : A) = (b : A) := by
  exact (coe_submoduleIdentityOfEq_apply S T h
    ((submoduleIdentityOfEq S T h).symm b)).symm.trans
      (congrArg (fun a : T => (a : A))
        ((submoduleIdentityOfEq S T h).apply_symm_apply b))

/-- The fibrewise continuous linear equivalence underlying fixed-kernel coordinates
on an all-unit domain. Both kernels carry their original submodule structures;
only the difference of the ambient projections must be jointly continuous. -/
noncomputable def kerFamilyContinuousLinearEquivOfIsUnit
    (Γ : D → H →L[K] A) (q0 : A →L[K] H)
    (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
    (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
    (hΔ : Continuous (fun p : D × A =>
      Γ p.1 (r p.1 p.2) - Γ p.1 (inverseGramComp (Γ p.1) q0 p.2)))
    (d : D) :
    LinearMap.ker (r d) ≃L[K] LinearMap.ker q0.toLinearMap := by
  have hq : ∀ h : H, inverseGramComp (Γ d) q0 (Γ d h) = h :=
    fun h => congrArg (fun f : H →L[K] H => f h)
      (inverseGramComp_comp_of_isUnit (hunit d))
  have hΔd : Continuous (fun a : A =>
      Γ d (r d a) - Γ d (inverseGramComp (Γ d) q0 a)) :=
    hΔ.comp ((continuous_const : Continuous (fun _ : A => d)).prodMk continuous_id)
  have hker : LinearMap.ker (inverseGramComp (Γ d) q0).toLinearMap =
      LinearMap.ker q0.toLinearMap := by
    ext a
    exact inverseGramComp_eq_zero_iff_of_isUnit (hunit d) a
  exact (LinearMap.kerContinuousLinearEquivOfCommonRightInverseOfContinuous
    (Γ d).toLinearMap (r d) (inverseGramComp (Γ d) q0).toLinearMap
    (hr d) hq hΔd).trans (submoduleIdentityOfEq _ _ hker)

section FibreCharacteristicAPI

variable (Γ : D → H →L[K] A) (q0 : A →L[K] H)
variable (hunit : ∀ d, IsUnit (q0.comp (Γ d)))
variable (r : D → A →ₗ[K] H) (hr : ∀ d h, r d (Γ d h) = h)
variable (hΔ : Continuous (fun p : D × A =>
  Γ p.1 (r p.1 p.2) - Γ p.1 (inverseGramComp (Γ p.1) q0 p.2)))

/-- The forward fibre coordinate has the normalized residual as ambient value. -/
@[simp]
theorem coe_kerFamilyContinuousLinearEquivOfIsUnit_apply
    (d : D) (a : LinearMap.ker (r d)) :
    (kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d a : A) =
      (a : A) - Γ d (inverseGramComp (Γ d) q0 (a : A)) := by
  unfold kerFamilyContinuousLinearEquivOfIsUnit
  erw [ContinuousLinearEquiv.trans_apply, coe_submoduleIdentityOfEq_apply,
    LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_apply]; rfl

/-- The inverse fibre coordinate uses the original supplied linear retraction. -/
@[simp]
theorem coe_kerFamilyContinuousLinearEquivOfIsUnit_symm_apply
    (d : D) (b : LinearMap.ker q0.toLinearMap) :
    ((kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d).symm b : A) =
      (b : A) - Γ d (r d (b : A)) := by
  have hq : ∀ h : H, inverseGramComp (Γ d) q0 (Γ d h) = h :=
    fun h => congrArg (fun f : H →L[K] H => f h)
      (inverseGramComp_comp_of_isUnit (hunit d))
  have hΔd : Continuous (fun a : A =>
      Γ d (r d a) - Γ d (inverseGramComp (Γ d) q0 a)) :=
    hΔ.comp ((continuous_const : Continuous (fun _ : A => d)).prodMk continuous_id)
  have hker : LinearMap.ker (inverseGramComp (Γ d) q0).toLinearMap =
      LinearMap.ker q0.toLinearMap := by
    ext a
    exact inverseGramComp_eq_zero_iff_of_isUnit (hunit d) a
  let e := LinearMap.kerContinuousLinearEquivOfCommonRightInverseOfContinuous
    (Γ d).toLinearMap (r d) (inverseGramComp (Γ d) q0).toLinearMap
    (hr d) hq hΔd
  let i := submoduleIdentityOfEq _ _ hker
  have hsymm : (e.trans i).symm b = e.symm (i.symm b) := by
    apply (e.trans i).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  simpa only [kerFamilyContinuousLinearEquivOfIsUnit] using
    (calc
      ((e.trans i).symm b : A) = (e.symm (i.symm b) : A) :=
        congrArg (fun a : LinearMap.ker (r d) => (a : A)) hsymm
      _ = (b : A) - Γ d (r d (b : A)) := by
        dsimp only [e, i]
        erw [LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_symm_apply,
          coe_submoduleIdentityOfEq_symm_apply]; rfl)

/-- After inclusion in the ambient space, forgetting continuity recovers the
algebraic common-section kernel comparison with the normalized retraction. -/
theorem kerFamilyContinuousLinearEquivOfIsUnit_toLinearMap
    (d : D) :
    (LinearMap.ker q0.toLinearMap).subtype.comp
        (kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d).toLinearEquiv.toLinearMap =
      (LinearMap.ker (inverseGramComp (Γ d) q0).toLinearMap).subtype.comp
        (LinearMap.kerEquivOfCommonRightInverse (Γ d).toLinearMap (r d)
          (inverseGramComp (Γ d) q0).toLinearMap (hr d)
          (fun h => congrArg (fun f : H →L[K] H => f h)
            (inverseGramComp_comp_of_isUnit (hunit d)))).toLinearMap := by
  apply DFunLike.ext
  intro a
  change (kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d a : A) =
    (LinearMap.kerEquivOfCommonRightInverse (Γ d).toLinearMap (r d)
      (inverseGramComp (Γ d) q0).toLinearMap (hr d)
      (fun h => congrArg (fun f : H →L[K] H => f h)
        (inverseGramComp_comp_of_isUnit (hunit d))) a : A)
  exact (coe_kerFamilyContinuousLinearEquivOfIsUnit_apply Γ q0 hunit r hr hΔ d a).trans
    (LinearMap.coe_kerEquivOfCommonRightInverse_apply (Γ d).toLinearMap (r d)
      (inverseGramComp (Γ d) q0).toLinearMap (hr d)
      (fun h => congrArg (fun f : H →L[K] H => f h)
        (inverseGramComp_comp_of_isUnit (hunit d))) a).symm

/-- The fibre equivalence agrees with the second coordinate of the total-space
fixed-kernel homeomorphism. -/
theorem kerFamilyContinuousLinearEquivOfIsUnit_apply_eq_snd
    (d : D) (a : LinearMap.ker (r d)) :
    kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d a =
      (kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ
        ⟨(d, (a : A)), a.property⟩).2 := by
  apply Subtype.ext
  exact (coe_kerFamilyContinuousLinearEquivOfIsUnit_apply
    Γ q0 hunit r hr hΔ d a).trans
      (kerFamilyHomeomorphOfIsUnit_apply_snd
        Γ q0 hunit r hr hΔ ⟨(d, (a : A)), a.property⟩).symm

/-- The inverse fibre equivalence agrees in the ambient space with the inverse
total-space fixed-kernel homeomorphism. -/
theorem kerFamilyContinuousLinearEquivOfIsUnit_symm_apply_eq_snd
    (d : D) (b : LinearMap.ker q0.toLinearMap) :
    ((kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d).symm b : A) =
      ((kerFamilyHomeomorphOfIsUnit Γ q0 hunit r hr hΔ).symm (d, b)).val.2 := by
  exact (coe_kerFamilyContinuousLinearEquivOfIsUnit_symm_apply
    Γ q0 hunit r hr hΔ d b).trans
      (kerFamilyHomeomorphOfIsUnit_symm_apply_snd
        Γ q0 hunit r hr hΔ (d, b)).symm

/-- The forward ambient residual uniquely determines the fibre equivalence. -/
theorem kerFamilyContinuousLinearEquivOfIsUnit_unique
    (d : D) (e : LinearMap.ker (r d) ≃L[K] LinearMap.ker q0.toLinearMap)
    (hvalue : ∀ a, (e a : A) =
      (a : A) - Γ d (inverseGramComp (Γ d) q0 (a : A))) :
    e = kerFamilyContinuousLinearEquivOfIsUnit Γ q0 hunit r hr hΔ d := by
  apply DFunLike.ext
  intro a
  apply Subtype.ext
  exact (hvalue a).trans (coe_kerFamilyContinuousLinearEquivOfIsUnit_apply
    Γ q0 hunit r hr hΔ d a).symm

end FibreCharacteristicAPI

-- Inverse fibre coordinates vary continuously on the original relative unit subtype.
example {B : Type uB} [TopologicalSpace B]
    (Γ : B → H →L[K] A) (q0 : A →L[K] H)
    (r : {b : B // IsUnit (q0.comp (Γ b))} → A →ₗ[K] H)
    (hr : ∀ u h, r u (Γ u.val h) = h)
    (hΔ : Continuous
      (fun p : {b : B // IsUnit (q0.comp (Γ b))} × A =>
        Γ p.1.val (r p.1 p.2) -
          Γ p.1.val (inverseGramComp (Γ p.1.val) q0 p.2))) :
    Continuous
      (fun p : {b : B // IsUnit (q0.comp (Γ b))} × LinearMap.ker q0.toLinearMap =>
        ((kerFamilyContinuousLinearEquivOfIsUnit (fun u => Γ u.val) q0
          (fun u => u.property) r hr hΔ p.1).symm p.2 : A)) := by
  let e :
      {p : {b : B // IsUnit (q0.comp (Γ b))} × A // r p.1 p.2 = 0} ≃ₜ
        {b : B // IsUnit (q0.comp (Γ b))} × LinearMap.ker q0.toLinearMap :=
    kerFamilyHomeomorphOfIsUnit (fun u => Γ u.val) q0
      (fun u => u.property) r hr hΔ
  have hinv : Continuous
      (fun p : {b : B // IsUnit (q0.comp (Γ b))} × LinearMap.ker q0.toLinearMap =>
        (e.symm p).val) :=
    continuous_subtype_val.comp e.symm.continuous_toFun
  have hambient : Continuous
      (fun p : {b : B // IsUnit (q0.comp (Γ b))} × LinearMap.ker q0.toLinearMap =>
        (e.symm p).val.2) :=
    continuous_snd.comp hinv
  have hpoint (u : {b : B // IsUnit (q0.comp (Γ b))})
      (b : LinearMap.ker q0.toLinearMap) :
      (e.symm (u, b)).val.2 =
        ((kerFamilyContinuousLinearEquivOfIsUnit (fun u => Γ u.val) q0
          (fun u => u.property) r hr hΔ u).symm b : A) := by
    exact (kerFamilyContinuousLinearEquivOfIsUnit_symm_apply_eq_snd
      (D := {b : B // IsUnit (q0.comp (Γ b))})
      (fun u => Γ u.val) q0 (fun u => u.property) r hr hΔ u b).symm
  exact hambient.congr (fun p => hpoint p.1 p.2)

end ContinuousLinearMap
