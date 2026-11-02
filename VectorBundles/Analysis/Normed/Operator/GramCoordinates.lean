/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.GramRetraction

/-!
# Coordinate changes for Gram normalization

For `Γ : E →L[K] A` and a supplied partner `q0 : A →L[K] E`, the existing
`inverseGramComp Γ q0` is a retraction of `Γ` when `q0.comp Γ` is a unit.
We compare this construction with its independently evaluated counterpart for
`Γ.comp e.toContinuousLinearMap` and `h.toContinuousLinearMap.comp q0`, where
`e : G ≃L[K] E` and `h : E ≃L[K] G` are independent equivalences.

The normalized map changes by postcomposition with `e.symm`, whereas the
ambient projection is unchanged. Neither equivalence need be an isometry, and
`h` need not be `e.symm` or an adjoint of `e`. For a unit endomorphism `T`,
the transformed `Ring.inverse` is obtained by precomposition with `h.symm`
and postcomposition with `e.symm`. The unit and inverse comparisons hold for
modules with arbitrary given topologies; they do not require norms.

## Implementation notes

Only the retraction and kernel characterizations of `inverseGramComp` are used
to compare the two constructed normalizers. The spaces have their given
seminorms and topologies; no completeness or inner product is assumed. The
ambient projection need not be orthogonal for an arbitrary supplied `q0`.
-/

@[expose] public section

universe uK uE uG uA

namespace ContinuousLinearMap

section Units

variable {K : Type uK} [Semiring K]
variable {E : Type uE} [AddCommMonoid E] [Module K E] [TopologicalSpace E]
variable {G : Type uG} [AddCommMonoid G] [Module K G] [TopologicalSpace G]

private theorem isUnit_equiv_comp_comp (T : E →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (hT : IsUnit T) :
    IsUnit (h.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap)) := by
  rcases hT with ⟨u, rfl⟩
  refine ⟨{
    val := h.toContinuousLinearMap.comp
      ((u : E →L[K] E).comp e.toContinuousLinearMap)
    inv := e.symm.toContinuousLinearMap.comp
      ((↑(u⁻¹) : E →L[K] E).comp h.symm.toContinuousLinearMap)
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · ext x
    change h ((u : E →L[K] E)
      (e (e.symm ((↑(u⁻¹) : E →L[K] E) (h.symm x))))) = x
    rw [e.apply_symm_apply]
    have hu : (u : E →L[K] E)
        ((↑(u⁻¹) : E →L[K] E) (h.symm x)) = h.symm x :=
      congrArg (fun f : E →L[K] E => f (h.symm x)) u.val_inv
    rw [hu, h.apply_symm_apply]
  · ext x
    change e.symm ((↑(u⁻¹) : E →L[K] E)
      (h.symm (h ((u : E →L[K] E) (e x))))) = x
    rw [h.symm_apply_apply]
    have hu : (↑(u⁻¹) : E →L[K] E)
        ((u : E →L[K] E) (e x)) = e x :=
      congrArg (fun f : E →L[K] E => f (e x)) u.inv_val
    rw [hu, e.symm_apply_apply]

/-- Pre- and postcomposing an endomorphism with independent coordinate
equivalences preserves invertibility. No relation between `e` and `h` is required. -/
theorem isUnit_comp_comp_equiv_iff (T : E →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) :
    IsUnit (h.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap)) ↔
      IsUnit T := by
  constructor
  · intro hunit
    have hunit' := isUnit_equiv_comp_comp
      (h.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap))
      e.symm h.symm hunit
    have heq : h.symm.toContinuousLinearMap.comp
        ((h.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap)).comp
          e.symm.toContinuousLinearMap) = T := by
      ext x
      change h.symm (h (T (e (e.symm x)))) = T x
      rw [e.apply_symm_apply, h.symm_apply_apply]
    exact heq ▸ hunit'
  · exact isUnit_equiv_comp_comp T e h

/-- The inverse of a unit endomorphism under independent coordinate changes.
The inverse equivalences occur in reverse composition order. -/
theorem inverse_comp_comp_equiv_of_isUnit (T : E →L[K] E)
    (e : G ≃L[K] E) (h : E ≃L[K] G) (hunit : IsUnit T) :
    Ring.inverse (h.toContinuousLinearMap.comp (T.comp e.toContinuousLinearMap)) =
      e.symm.toContinuousLinearMap.comp
        ((Ring.inverse T).comp h.symm.toContinuousLinearMap) := by
  rcases hunit with ⟨u, rfl⟩
  have hunit' := (isUnit_comp_comp_equiv_iff (u : E →L[K] E) e h).mpr ⟨u, rfl⟩
  rcases hunit' with ⟨v, hv⟩
  rw [← hv]
  simp only [Ring.inverse_unit]
  have hu (y : E) : (↑(u⁻¹) : E →L[K] E) ((u : E →L[K] E) y) = y :=
    congrArg (fun f : E →L[K] E => f y) u.inv_val
  ext x
  have hvx : h ((u : E →L[K] E) (e ((↑(v⁻¹) : G →L[K] G) x))) = x := by
    calc
      h ((u : E →L[K] E) (e ((↑(v⁻¹) : G →L[K] G) x))) =
          (v : G →L[K] G) ((↑(v⁻¹) : G →L[K] G) x) :=
        (congrArg (fun f : G →L[K] G => f ((↑(v⁻¹) : G →L[K] G) x)) hv).symm
      _ = x := congrArg (fun f : G →L[K] G => f x) v.val_inv
  have hex : e ((↑(v⁻¹) : G →L[K] G) x) =
      (↑(u⁻¹) : E →L[K] E) (h.symm x) := by
    simpa only [h.symm_apply_apply, hu] using
      congrArg (fun z : G => (↑(u⁻¹) : E →L[K] E) (h.symm z)) hvx
  calc
    (↑(v⁻¹) : G →L[K] G) x =
        e.symm (e ((↑(v⁻¹) : G →L[K] G) x)) := (e.symm_apply_apply _).symm
    _ = e.symm ((↑(u⁻¹) : E →L[K] E) (h.symm x)) := congrArg e.symm hex

end Units

section Normalization

variable {K : Type uK} [NontriviallyNormedField K]
variable {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace K E]
variable {G : Type uG} [SeminormedAddCommGroup G] [NormedSpace K G]
variable {A : Type uA} [SeminormedAddCommGroup A] [NormedSpace K A]

/-- A one-way inclusion of the supplied partners' kernels, together with both
Gram units, makes the constructed normalizers agree contravariantly. -/
theorem inverseGramComp_comp_equiv_of_ker_le_of_isUnit
    (β : E →L[K] A) (g0 : A →L[K] E) (e : G ≃L[K] E) (g1 : A →L[K] G)
    (hker : LinearMap.ker g1.toLinearMap ≤ LinearMap.ker g0.toLinearMap)
    (hunit : IsUnit (g0.comp β))
    (hunit' : IsUnit (g1.comp (β.comp e.toContinuousLinearMap))) :
    inverseGramComp (β.comp e.toContinuousLinearMap) g1 =
      e.symm.toContinuousLinearMap.comp (inverseGramComp β g0) := by
  let n : A →L[K] E := inverseGramComp β g0
  let n' : A →L[K] G := inverseGramComp (β.comp e.toContinuousLinearMap) g1
  have hn (x : E) : n (β x) = x :=
    congrArg (fun f : E →L[K] E => f x)
      (inverseGramComp_comp_of_isUnit hunit)
  have hn' (z : G) : n' (β (e z)) = z :=
    congrArg (fun f : G →L[K] G => f z)
      (inverseGramComp_comp_of_isUnit hunit')
  ext a
  -- The residual for the new normalizer lies in both normalizers' kernels.
  let b : A := a - β (e (n' a))
  have hb' : n' b = 0 := by
    dsimp only [b]
    rw [map_sub, hn', sub_self]
  have hg1b : g1 b = 0 :=
    (inverseGramComp_eq_zero_iff_of_isUnit hunit' b).mp hb'
  have hg0b : g0 b = 0 := hker hg1b
  have hb : n b = 0 :=
    (inverseGramComp_eq_zero_iff_of_isUnit hunit b).mpr hg0b
  have hna : n a = e (n' a) := by
    apply sub_eq_zero.mp
    simpa only [b, map_sub, hn] using hb
  calc
    n' a = e.symm (e (n' a)) := (e.symm_apply_apply (n' a)).symm
    _ = e.symm (n a) := congrArg e.symm hna.symm

/-- The constructed normalizer changes contravariantly with the auxiliary
coordinates. An independent equivalence applied to the supplied partner cancels
from the normalization. -/
theorem inverseGramComp_comp_equiv_of_isUnit
    (Γ : E →L[K] A) (q0 : A →L[K] E) (e : G ≃L[K] E) (h : E ≃L[K] G)
    (hunit : IsUnit (q0.comp Γ)) :
    inverseGramComp (Γ.comp e.toContinuousLinearMap)
        (h.toContinuousLinearMap.comp q0) =
      e.symm.toContinuousLinearMap.comp (inverseGramComp Γ q0) := by
  have hunit' : IsUnit ((h.toContinuousLinearMap.comp q0).comp
      (Γ.comp e.toContinuousLinearMap)) := by
    simpa only [ContinuousLinearMap.comp_assoc] using
      (isUnit_comp_comp_equiv_iff (q0.comp Γ) e h).mpr hunit
  apply inverseGramComp_comp_equiv_of_ker_le_of_isUnit
    Γ q0 e (h.toContinuousLinearMap.comp q0) ?_ hunit hunit'
  intro a ha
  change q0 a = 0
  apply h.injective
  change h (q0 a) = 0 at ha
  simpa only [map_zero] using ha

/-- The ambient projection constructed by normalization is unchanged by
independent changes of auxiliary coordinates and partner. This projection is
not asserted to be orthogonal when `q0` is arbitrary. -/
theorem comp_inverseGramComp_comp_equiv_of_isUnit
    (Γ : E →L[K] A) (q0 : A →L[K] E) (e : G ≃L[K] E) (h : E ≃L[K] G)
    (hunit : IsUnit (q0.comp Γ)) :
    (Γ.comp e.toContinuousLinearMap).comp
        (inverseGramComp (Γ.comp e.toContinuousLinearMap)
          (h.toContinuousLinearMap.comp q0)) =
      Γ.comp (inverseGramComp Γ q0) := by
  rw [inverseGramComp_comp_equiv_of_isUnit Γ q0 e h hunit]
  ext a
  change Γ (e (e.symm (inverseGramComp Γ q0 a))) =
    Γ (inverseGramComp Γ q0 a)
  rw [e.apply_symm_apply]

end Normalization

end ContinuousLinearMap
