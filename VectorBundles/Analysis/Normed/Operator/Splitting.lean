/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import ProjectiveModules.Topology.Splitting

/-!
# Isometric kernel-product decompositions

Seminormed additive group data on kernels are used to form products in isometric
decompositions over semirings. The kernel retains its original submodule structure
and the norm and subtype geometry inherited from the source.

`LinearIsometry.equivProdKerOfRightInverse` decomposes a linear isometry with a given
linear right inverse as the product of its target and kernel. It derives the section's
continuity and reuses the continuous kernel-product equivalence from
`ProjectiveModules.Topology.Splitting`, bundled isometrically by Mathlib's
`LinearIsometryEquiv.mk`. The kernel need not vanish: its inherited seminorm vanishes
for an isometry, without any separation assumption. The output uses the usual
maximum product norm. The whole-bundle comparisons determine the isometric lift
uniquely through Mathlib's injective forgetful map to continuous linear equivalences.

The kernel data are installed only locally for this construction. They retain the
original submodule scalar action and module, and over rings agree with the full
submodule seminormed structure. No norm or topology on the scalar semiring is required.
-/

@[expose] public section

noncomputable section

universe uR uE uF

namespace LinearMap

section Semiring

variable {R : Type uR} {E : Type uE} {F : Type uF}
  [Semiring R] [SeminormedAddCommGroup E] [AddCommMonoid F]
  [Module R E] [Module R F]

/-- The seminormed additive group structure on a linear kernel, with norm restricted
from the source. This uses the additive-homomorphism kernel and retains the original
submodule additive-monoid structure and scalar action. It is not a global instance. -/
abbrev kerSeminormedAddCommGroup (f : E →ₗ[R] F) : SeminormedAddCommGroup f.ker :=
  fast_instance% AddSubgroup.seminormedAddCommGroup (s := f.toAddMonoidHom.ker)

variable (f : E →ₗ[R] F)

/-- The kernel seminormed structure is the structure on the additive-homomorphism kernel. -/
theorem kerSeminormedAddCommGroup_eq_addSubgroup :
    f.kerSeminormedAddCommGroup =
      AddSubgroup.seminormedAddCommGroup (s := f.toAddMonoidHom.ker) :=
  rfl

/-- The kernel group is the group of the additive-homomorphism kernel. -/
theorem kerSeminormedAddCommGroup_toAddCommGroup :
    f.kerSeminormedAddCommGroup.toAddCommGroup =
      AddSubgroup.toAddCommGroup f.toAddMonoidHom.ker :=
  rfl

/-- The additive-monoid parent is the original submodule structure, including `nsmul`. -/
theorem kerSeminormedAddCommGroup_toAddCommMonoid :
    f.kerSeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid =
      Submodule.addCommMonoid f.ker :=
  rfl

/-- The kernel norm is the restriction of the source norm. -/
theorem kerSeminormedAddCommGroup_toNorm :
    f.kerSeminormedAddCommGroup.toNorm = ⟨fun k => ‖(k : E)‖⟩ :=
  rfl

/-- The kernel pseudometric is the original induced subtype pseudometric. -/
theorem kerSeminormedAddCommGroup_toPseudoMetricSpace :
    f.kerSeminormedAddCommGroup.toPseudoMetricSpace =
      PseudoMetricSpace.induced (Subtype.val : f.ker → E)
        ‹SeminormedAddCommGroup E›.toPseudoMetricSpace :=
  rfl

/-- The kernel uniform structure is the original subtype uniform structure. -/
theorem kerSeminormedAddCommGroup_toUniformSpace :
    f.kerSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace =
      UniformSpace.comap (Subtype.val : f.ker → E)
        ‹SeminormedAddCommGroup E›.toPseudoMetricSpace.toUniformSpace :=
  rfl

/-- The kernel topology is the original subtype topology. -/
theorem kerSeminormedAddCommGroup_toTopologicalSpace :
    f.kerSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced (Subtype.val : f.ker → E)
        ‹SeminormedAddCommGroup E›.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  rfl

/-- The kernel bornology is the original induced subtype bornology. -/
theorem kerSeminormedAddCommGroup_toBornology :
    f.kerSeminormedAddCommGroup.toPseudoMetricSpace.toBornology =
      Bornology.induced (Subtype.val : f.ker → E) :=
  rfl

end Semiring

section RingKernel

variable {R : Type uR} {E : Type uE} {F : Type uF}
  [Ring R] [AddCommGroup E] [AddCommMonoid F] [Module R E] [Module R F]

/-- Over a ring, the submodule kernel and the additive-homomorphism kernel give
identical additive subgroups, even when the target is only an additive monoid. -/
theorem ker_toAddSubgroup_eq_addMonoidHom_ker (f : E →ₗ[R] F) :
    f.ker.toAddSubgroup = f.toAddMonoidHom.ker := by
  ext x
  rfl

end RingKernel

section Ring

variable {R : Type uR} {E : Type uE} {F : Type uF}
  [Ring R] [SeminormedAddCommGroup E] [AddCommMonoid F]
  [Module R E] [Module R F]

variable (f : E →ₗ[R] F)

/-- Over a ring, the kernel group agrees with the original submodule group. -/
theorem kerSeminormedAddCommGroup_toAddCommGroup_eq :
    f.kerSeminormedAddCommGroup.toAddCommGroup = Submodule.addCommGroup f.ker :=
  rfl

/-- Over a ring, the full seminormed structure agrees with the submodule structure. -/
theorem kerSeminormedAddCommGroup_eq :
    f.kerSeminormedAddCommGroup = Submodule.seminormedAddCommGroup f.ker :=
  rfl

end Ring

end LinearMap

namespace LinearIsometry

section Semiring

attribute [local instance] LinearMap.kerSeminormedAddCommGroup

variable {R : Type uR} {E : Type uE} {F : Type uF}
  [Semiring R] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

private def rightInverseIsometry (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) : F →ₗᵢ[R] E :=
  LinearIsometry.mk s fun y =>
    (f.norm_map (s y)).symm.trans (congrArg norm (DFunLike.congr_fun hsComp y))

private theorem rightInverseIsometry_toContinuousLinearMap_apply
    (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) (y : F) :
    (rightInverseIsometry f s hsComp).toContinuousLinearMap y = s y := by
  calc
    (rightInverseIsometry f s hsComp).toContinuousLinearMap y =
        rightInverseIsometry f s hsComp y :=
      congrFun (LinearIsometry.coe_toContinuousLinearMap _) y
    _ = s y := rfl

/-- An isometry with a linear right inverse identifies its source isometrically with
its target times its original kernel. The section's continuity is derived from its
norm preservation; the product has the usual maximum norm. The construction uses
`ContinuousLinearMap.equivProdKerOfRightInverse` from ProjectiveModules and Mathlib's
`LinearIsometryEquiv.mk`, retaining the supplied continuous equivalence and inverse. -/
def equivProdKerOfRightInverse (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) :
    E ≃ₗᵢ[R] (F × f.toLinearMap.ker) := by
  let sLI : F →ₗᵢ[R] E :=
    LinearIsometry.mk s fun y =>
      (f.norm_map (s y)).symm.trans (congrArg norm (DFunLike.congr_fun hsComp y))
  have hfs : Function.RightInverse sLI.toContinuousLinearMap f.toContinuousLinearMap :=
    fun y => DFunLike.congr_fun hsComp y
  let c :=
    f.toContinuousLinearMap.equivProdKerOfRightInverse sLI.toContinuousLinearMap hfs
  refine LinearIsometryEquiv.mk c.toLinearEquiv ?_
  have hker (k : f.toLinearMap.ker) : ‖k‖ = 0 := by
    calc
      ‖k‖ = ‖(k : E)‖ :=
        AddSubgroup.coe_norm (s := f.toLinearMap.toAddMonoidHom.ker) k
      _ = ‖f (k : E)‖ := (f.norm_map (k : E)).symm
      _ = 0 := by rw [show f (k : E) = 0 from k.property, norm_zero]
  intro x
  calc
    ‖c x‖ = max ‖(c x).1‖ ‖(c x).2‖ := Prod.norm_def _
    _ = max ‖f x‖ 0 := by
      have hfst : (c x).1 = f x :=
        (ContinuousLinearMap.fst_equivProdKerOfRightInverse
          f.toContinuousLinearMap sLI.toContinuousLinearMap hfs x).trans
          (congrFun (LinearIsometry.coe_toContinuousLinearMap f) x)
      exact congrArg₂ max (congrArg norm hfst) (hker (c x).2)
    _ = ‖f x‖ := max_eq_left (norm_nonneg _)
    _ = ‖x‖ := f.norm_map x

/-- The first coordinate of the isometric kernel-product equivalence is the given map. -/
@[simp]
theorem fst_equivProdKerOfRightInverse (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) (x : E) :
    (f.equivProdKerOfRightInverse s hsComp x).1 = f x := by
  change (f.toContinuousLinearMap.equivProdKerOfRightInverse
    (rightInverseIsometry f s hsComp).toContinuousLinearMap
    (fun y => DFunLike.congr_fun hsComp y) x).1 = f x
  exact ContinuousLinearMap.fst_equivProdKerOfRightInverse f.toContinuousLinearMap
    (rightInverseIsometry f s hsComp).toContinuousLinearMap
    (fun y => DFunLike.congr_fun hsComp y) x

/-- The kernel coordinate is the residual after applying the given section. -/
@[simp]
theorem coe_snd_equivProdKerOfRightInverse (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) (x : E) :
    ((f.equivProdKerOfRightInverse s hsComp x).2 : E) = x - s (f x) := by
  change ((f.toContinuousLinearMap.equivProdKerOfRightInverse
    (rightInverseIsometry f s hsComp).toContinuousLinearMap
    (fun y => DFunLike.congr_fun hsComp y) x).2 : E) = x - s (f x)
  exact ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse f.toContinuousLinearMap
    (rightInverseIsometry f s hsComp).toContinuousLinearMap
    (fun y => DFunLike.congr_fun hsComp y) x

/-- The inverse adds the section value and the original kernel vector. -/
@[simp]
theorem equivProdKerOfRightInverse_symm_apply (f : E →ₗᵢ[R] F) (s : F →ₗ[R] E)
    (hsComp : f.toLinearMap.comp s = LinearMap.id) (y : F) (k : f.toLinearMap.ker) :
    (f.equivProdKerOfRightInverse s hsComp).symm (y, k) = s y + (k : E) := by
  change (f.toContinuousLinearMap.equivProdKerOfRightInverse
    (rightInverseIsometry f s hsComp).toContinuousLinearMap
    (fun z => DFunLike.congr_fun hsComp z)).symm (y, k) = s y + (k : E)
  calc
    (f.toContinuousLinearMap.equivProdKerOfRightInverse
        (rightInverseIsometry f s hsComp).toContinuousLinearMap
        (fun z => DFunLike.congr_fun hsComp z)).symm (y, k) =
        (k : E) + (rightInverseIsometry f s hsComp).toContinuousLinearMap y :=
      ContinuousLinearMap.equivProdKerOfRightInverse_symm_apply f.toContinuousLinearMap
        (rightInverseIsometry f s hsComp).toContinuousLinearMap
        (fun z => DFunLike.congr_fun hsComp z) (y, k)
    _ = (k : E) + s y :=
      congrArg (fun z : E => (k : E) + z)
        (rightInverseIsometry_toContinuousLinearMap_apply f s hsComp y)
    _ = s y + (k : E) := add_comm _ _

/-- For a continuous section, the complete underlying linear equivalence is the
canonical continuous kernel-product equivalence's underlying linear equivalence. -/
theorem equivProdKerOfRightInverse_toLinearEquiv (f : E →ₗᵢ[R] F) (s : F →L[R] E)
    (hs : Function.RightInverse s f.toContinuousLinearMap) :
    (f.equivProdKerOfRightInverse s.toLinearMap (LinearMap.ext hs)).toLinearEquiv =
      (f.toContinuousLinearMap.equivProdKerOfRightInverse s hs).toLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · exact (fst_equivProdKerOfRightInverse f s.toLinearMap (LinearMap.ext hs) x).trans
      (ContinuousLinearMap.fst_equivProdKerOfRightInverse f.toContinuousLinearMap s hs x).symm
  · apply Subtype.ext
    exact (coe_snd_equivProdKerOfRightInverse f s.toLinearMap (LinearMap.ext hs) x).trans
      (ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse
        f.toContinuousLinearMap s hs x).symm

/-- Forgetting the isometry gives the whole canonical continuous equivalence, including
its inverse. No continuity hypothesis is needed by the algebraic-section constructor. -/
theorem equivProdKerOfRightInverse_toContinuousLinearEquiv
    (f : E →ₗᵢ[R] F) (s : F →L[R] E)
    (hs : Function.RightInverse s f.toContinuousLinearMap) :
    (f.equivProdKerOfRightInverse s.toLinearMap (LinearMap.ext hs)).toContinuousLinearEquiv =
      f.toContinuousLinearMap.equivProdKerOfRightInverse s hs := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.ext
  intro x
  exact (congrFun (LinearIsometryEquiv.coe_toContinuousLinearEquiv
    (f.equivProdKerOfRightInverse s.toLinearMap (LinearMap.ext hs))) x).trans
      (DFunLike.congr_fun (equivProdKerOfRightInverse_toLinearEquiv f s hs) x)

end Semiring

section Ring

variable {R : Type uR} {E : Type uE} {F : Type uF}
  [Ring R] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- Over a ring, forgetting the isometry agrees with the whole Mathlib continuous
splitting on the stock submodule kernel. The full kernel structure agrees by
`LinearMap.kerSeminormedAddCommGroup_eq`; no kernel structure is transported. -/
theorem equivProdKerOfRightInverse_toContinuousLinearEquiv_eq_equivOfRightInverse
    (f : E →ₗᵢ[R] F) (s : F →L[R] E)
    (hs : Function.RightInverse s f.toContinuousLinearMap) :
    (f.equivProdKerOfRightInverse s.toLinearMap (LinearMap.ext hs)).toContinuousLinearEquiv =
      ContinuousLinearEquiv.equivOfRightInverse f.toContinuousLinearMap s hs :=
  (equivProdKerOfRightInverse_toContinuousLinearEquiv f s hs).trans
    (ContinuousLinearMap.equivProdKerOfRightInverse_eq_equivOfRightInverse
      f.toContinuousLinearMap s hs)

/-- Over a ring, the complete underlying linear equivalence agrees with the stock
continuous splitting's underlying linear equivalence on the original kernel. -/
theorem equivProdKerOfRightInverse_toLinearEquiv_eq_equivOfRightInverse
    (f : E →ₗᵢ[R] F) (s : F →L[R] E)
    (hs : Function.RightInverse s f.toContinuousLinearMap) :
    (f.equivProdKerOfRightInverse s.toLinearMap (LinearMap.ext hs)).toLinearEquiv =
      (ContinuousLinearEquiv.equivOfRightInverse f.toContinuousLinearMap s hs).toLinearEquiv :=
  (equivProdKerOfRightInverse_toLinearEquiv f s hs).trans
    (congrArg ContinuousLinearEquiv.toLinearEquiv
      (ContinuousLinearMap.equivProdKerOfRightInverse_eq_equivOfRightInverse
        f.toContinuousLinearMap s hs))

end Ring

end LinearIsometry
