/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Prod
public import VectorBundles.Topology.Maps.FiberwiseSplitting
import Mathlib.Algebra.Group.TransferInstance
import VectorBundles.Data.Bundle

/-!
# Sum–kernel coordinates on a bundle sum

A family of linear retractions gives coordinates on the fiberwise product of a bundle with
its kernel family. The kernel total space retains its given topology, assumed to be induced
by its base and ambient vector coordinates. The domain carries the standard fiberwise-product
topology. No local triviality, topology on the scalar semiring, or continuous scalar action is
required.

`Bundle.TotalSpace.sumKerHomeomorph` preserves the base and sends `(e, h)` to `β e + h`.
Its inverse-value formula uses the original retraction and the residual `a - β (ρ a)`.
The forward fiber coordinate agrees with `LinearMap.coprod`, for the given scalar action.

## Implementation notes

The construction uses `Homeomorph.fiberwiseSumKer` from VectorBundles, after identifying each
original fiber with the equality fiber of the total-space projection. The public pure
`Bundle.TotalSpace.fiberLinearEquiv` uses the opt-in canonical additive and module families
on those equality fibers. The original module structures and both given total-space
topologies are unchanged.
-/

public section

open Bundle Topology

universe uR uB uA uE uF uG

namespace Bundle.TotalSpace

noncomputable section

section EqualityFiber

variable {B : Type uB} (F : Type uF) (E : B → Type uE)

variable [∀ b, AddCommMonoid (E b)]

private abbrev equalityFiberAddMonoid (b : B) :
    AddMonoid {t : TotalSpace F E // t.proj = b} :=
  (fiberAddCommMonoid (E := E) F b).toAddMonoid

attribute [local instance] fiberAddCommMonoid fiberModule equalityFiberAddMonoid

variable {R : Type uR} [Semiring R] {A : Type uA} [AddCommGroup A]
  [Module R A] [∀ b, Module R (E b)]

private def equalityFiberBeta (β : ∀ b, E b →ₗ[R] A) (b : B) :
    {t : TotalSpace F E // t.proj = b} →+ A :=
  ((β b).comp (fiberLinearEquiv (E := E) R F b).symm.toLinearMap).toAddMonoidHom

private def equalityFiberRho (ρ : ∀ b, A →ₗ[R] E b) (b : B) :
    A →+ {t : TotalSpace F E // t.proj = b} :=
  ((fiberLinearEquiv (E := E) R F b).toLinearMap.comp (ρ b)).toAddMonoidHom

private theorem equalityFiberBeta_apply (β : ∀ b, E b →ₗ[R] A)
    (t : TotalSpace F E) :
    equalityFiberBeta F E β t.proj ⟨t, rfl⟩ = β t.proj t.snd :=
  comp_fiberLinearEquiv_symm_apply_self (E := E) R F β t

private theorem equalityFiberRho_apply_val (ρ : ∀ b, A →ₗ[R] E b) (b : B) (a : A) :
    (equalityFiberRho F E ρ b a).val = (⟨b, ρ b a⟩ : TotalSpace F E) :=
  fiberLinearEquiv_comp_apply_val (E := E) R F b (ρ b) a

private theorem equalityFiberBeta_rho (β : ∀ b, E b →ₗ[R] A)
    (ρ : ∀ b, A →ₗ[R] E b) (b : B) (a : A) :
    equalityFiberBeta F E β b (equalityFiberRho F E ρ b a) = β b (ρ b a) :=
  congrArg (β b) ((fiberLinearEquiv (E := E) R F b).symm_apply_apply (ρ b a))

private theorem equalityFiberRho_eq_zero_iff (ρ : ∀ b, A →ₗ[R] E b) (b : B) (a : A) :
    equalityFiberRho F E ρ b a = 0 ↔ ρ b a = 0 := by
  change fiberLinearEquiv (E := E) R F b (ρ b a) = 0 ↔ ρ b a = 0
  constructor
  · intro h
    exact (fiberLinearEquiv (E := E) R F b).injective
      (h.trans (fiberLinearEquiv (E := E) R F b).map_zero.symm)
  · intro h
    exact (congrArg (fiberLinearEquiv (E := E) R F b) h).trans
      (fiberLinearEquiv (E := E) R F b).map_zero

private theorem equalityFiber_rightInverse (β : ∀ b, E b →ₗ[R] A)
    (ρ : ∀ b, A →ₗ[R] E b) (hρβ : ∀ b e, ρ b (β b e) = e) :
    ∀ b, Function.RightInverse (equalityFiberBeta F E β b) (equalityFiberRho F E ρ b) := by
  intro b t
  apply (fiberLinearEquiv (E := E) R F b).symm.injective
  exact ((fiberLinearEquiv (E := E) R F b).symm_apply_apply _).trans (hρβ b _)

section Topology

variable [TopologicalSpace B] [TopologicalSpace A]
  [TopologicalSpace (TotalSpace F E)]
  (G : Type uG) (ρ : ∀ b, A →ₗ[R] E b)
  [TopologicalSpace (TotalSpace G (fun b => (ρ b).ker))]

private theorem equalityFiberBeta_continuous (β : ∀ b, E b →ₗ[R] A)
    (hβTotal : Continuous (fun t : TotalSpace F E => (t.proj, β t.proj t.snd))) :
    Continuous (fun t : TotalSpace F E =>
      (t.proj, equalityFiberBeta F E β t.proj ⟨t, rfl⟩)) :=
  hβTotal.congr (fun t => by rw [equalityFiberBeta_apply])

private theorem equalityFiberRho_continuous
    (hρTotal : Continuous (fun y : B × A => (⟨y.1, ρ y.1 y.2⟩ : TotalSpace F E))) :
    Continuous (fun y : B × A => (equalityFiberRho F E ρ y.1 y.2).val) :=
  hρTotal.congr (fun y => by rw [equalityFiberRho_apply_val])

private def equalBaseHomeomorphRaw
    (hκ : IsInducing (fun k : TotalSpace G (fun b => (ρ b).ker) =>
      (k.proj, (k.snd : A))))
    (hp : Continuous (TotalSpace.proj : TotalSpace F E → B)) :
    {w : TotalSpace F E × TotalSpace G (fun b => (ρ b).ker) // w.1.proj = w.2.proj} ≃ₜ
      {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0} where
  toFun w := ⟨(w.val.1, (w.val.2.snd : A)),
    (equalityFiberRho_eq_zero_iff F E ρ _ _).2 (by
      rcases w with ⟨⟨⟨b, e⟩, ⟨c, h⟩⟩, q⟩
      cases q
      exact h.property)⟩
  invFun z := ⟨(z.val.1, ⟨z.val.1.proj,
    ⟨z.val.2, (equalityFiberRho_eq_zero_iff F E ρ _ _).1 z.property⟩⟩), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨b, e⟩, ⟨c, h⟩⟩, q⟩
    cases q
    rfl
  right_inv _ := rfl
  continuous_toFun := by
    have ht : Continuous (fun w :
        {w : TotalSpace F E × TotalSpace G (fun b => (ρ b).ker) //
          w.1.proj = w.2.proj} => w.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have hk : Continuous (fun w :
        {w : TotalSpace F E × TotalSpace G (fun b => (ρ b).ker) //
          w.1.proj = w.2.proj} => w.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (ht.prodMk (hκ.continuous.comp hk).snd).subtype_mk _
  continuous_invFun := by
    have ht : Continuous (fun z :
        {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0} => z.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have ha : Continuous (fun z :
        {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0} => z.val.2) :=
      continuous_snd.comp continuous_subtype_val
    have hk : Continuous (fun z :
        {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0} =>
        (⟨z.val.1.proj,
          ⟨z.val.2, (equalityFiberRho_eq_zero_iff F E ρ _ _).1 z.property⟩⟩ :
            TotalSpace G (fun b => (ρ b).ker))) :=
      hκ.continuous_iff.2 ((hp.comp ht).prodMk ha)
    exact (ht.prodMk hk).subtype_mk _

private def sumHomeomorphRaw
    (hκ : IsInducing (fun k : TotalSpace G (fun b => (ρ b).ker) =>
      (k.proj, (k.snd : A))))
    (hp : Continuous (TotalSpace.proj : TotalSpace F E → B)) :
    TotalSpace (F × G) (fun b => E b × (ρ b).ker) ≃ₜ
      {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0} :=
  (FiberBundle.Prod.homeomorphEqualBase F E G (fun b => (ρ b).ker)).trans
    (equalBaseHomeomorphRaw F E G ρ hκ hp)

private theorem sumHomeomorphRaw_apply_val
    (hκ : IsInducing (fun k : TotalSpace G (fun b => (ρ b).ker) =>
      (k.proj, (k.snd : A))))
    (hp : Continuous (TotalSpace.proj : TotalSpace F E → B))
    (c : TotalSpace (F × G) (fun b => E b × (ρ b).ker)) :
    (sumHomeomorphRaw F E G ρ hκ hp c).val =
      ((⟨c.proj, c.snd.1⟩ : TotalSpace F E), (c.snd.2 : A)) := rfl

private theorem sumHomeomorphRaw_symm_apply_val
    (hκ : IsInducing (fun k : TotalSpace G (fun b => (ρ b).ker) =>
      (k.proj, (k.snd : A))))
    (hp : Continuous (TotalSpace.proj : TotalSpace F E → B))
    (z : {z : TotalSpace F E × A // equalityFiberRho F E ρ z.1.proj z.2 = 0}) :
    let c := (sumHomeomorphRaw F E G ρ hκ hp).symm z
    ((⟨c.proj, c.snd.1⟩ : TotalSpace F E), (c.snd.2 : A)) = z.val := by
  apply Prod.ext
  · exact FiberBundle.Prod.homeomorphEqualBase_mk_fst_symm_apply F E G
      (fun b => (ρ b).ker) ((equalBaseHomeomorphRaw F E G ρ hκ hp).symm z)
  · exact congrArg (fun k : TotalSpace G (fun b => (ρ b).ker) => (k.snd : A))
      (FiberBundle.Prod.homeomorphEqualBase_mk_snd_symm_apply F E G
        (fun b => (ρ b).ker) ((equalBaseHomeomorphRaw F E G ρ hκ hp).symm z))

end Topology
end EqualityFiber

attribute [local instance] fiberAddCommMonoid fiberModule equalityFiberAddMonoid

variable {R : Type uR} [Semiring R] {B : Type uB} [TopologicalSpace B]
  {A : Type uA} [AddCommGroup A] [Module R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] {E : B → Type uE}
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  {F : Type uF} {G : Type uG} [TopologicalSpace (TotalSpace F E)]
  (β : ∀ b, E b →ₗ[R] A) (ρ : ∀ b, A →ₗ[R] E b)
  [TopologicalSpace (TotalSpace G (fun b => (ρ b).ker))]
  (hρβ : ∀ b e, ρ b (β b e) = e)
  (hκ : IsInducing (fun k : TotalSpace G (fun b => (ρ b).ker) => (k.proj, (k.snd : A))))
  (hβTotal : Continuous (fun t : TotalSpace F E => (t.proj, β t.proj t.snd)))
  (hρTotal : Continuous (fun y : B × A => (⟨y.1, ρ y.1 y.2⟩ : TotalSpace F E)))

/-- Sum–kernel coordinates on the fiberwise product with the kernel of a family of linear
retractions. The kernel total-space topology is induced by its base and ambient coordinates;
the source has the standard fiberwise-product topology. The forward map preserves the base
and adds the image of the first fiber coordinate to the kernel value. -/
def sumKerHomeomorph :
    TotalSpace (F × G) (fun b => E b × (ρ b).ker) ≃ₜ B × A :=
  (sumHomeomorphRaw F E G ρ hκ hβTotal.fst).trans
    (Homeomorph.fiberwiseSumKer (TotalSpace.proj : TotalSpace F E → B)
      (equalityFiberBeta F E β) (equalityFiberRho F E ρ)
      (equalityFiber_rightInverse F E β ρ hρβ)
      (equalityFiberBeta_continuous F E β hβTotal)
      (equalityFiberRho_continuous F E ρ hρTotal))

/-- Evaluation of the base and sum coordinates on an arbitrary bundle-sum point. -/
@[simp]
theorem sumKerHomeomorph_apply (c : TotalSpace (F × G) (fun b => E b × (ρ b).ker)) :
    sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal c =
      (c.proj, β c.proj c.snd.1 + (c.snd.2 : A)) := by
  unfold sumKerHomeomorph
  erw [Homeomorph.trans_apply, Homeomorph.fiberwiseSumKer_apply]
  have hβ :
      equalityFiberBeta F E β c.proj
        ⟨(⟨c.proj, c.snd.1⟩ : TotalSpace F E), rfl⟩ =
        β c.proj c.snd.1 :=
    equalityFiberBeta_apply F E β ⟨c.proj, c.snd.1⟩
  erw [sumHomeomorphRaw_apply_val F E G ρ hκ hβTotal.fst c, hβ]

/-- On a constructed bundle-sum point, the coordinates use the given fiber values. -/
theorem sumKerHomeomorph_apply_mk (b : B) (e : E b) (h : (ρ b).ker) :
    sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal
      (TotalSpace.mk' (F × G) b (e, h)) = (b, β b e + (h : A)) :=
  sumKerHomeomorph_apply β ρ hρβ hκ hβTotal hρTotal _

/-- The inverse recovers the original retraction total-space point and the ambient residual.
The first coordinate is an equality in the original total space, so no comparison of values
in different dependent fibers is needed. -/
@[simp]
theorem sumKerHomeomorph_symm_apply_val (y : B × A) :
    let c := (sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal).symm y
    ((⟨c.proj, c.snd.1⟩ : TotalSpace F E), (c.snd.2 : A)) =
      ((⟨y.1, ρ y.1 y.2⟩ : TotalSpace F E), y.2 - β y.1 (ρ y.1 y.2)) := by
  unfold sumKerHomeomorph
  simpa only [Homeomorph.symm_trans_apply, equalityFiberRho_apply_val,
    equalityFiberBeta_rho] using
    (sumHomeomorphRaw_symm_apply_val F E G ρ hκ hβTotal.fst _).trans
      (Homeomorph.fiberwiseSumKer_symm_apply_val (TotalSpace.proj : TotalSpace F E → B)
        (equalityFiberBeta F E β) (equalityFiberRho F E ρ)
        (equalityFiber_rightInverse F E β ρ hρβ)
        (equalityFiberBeta_continuous F E β hβTotal)
        (equalityFiberRho_continuous F E ρ hρTotal) y)

/-- The inverse preserves the original base point. -/
@[simp]
theorem sumKerHomeomorph_symm_apply_proj (y : B × A) :
    ((sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal).symm y).proj = y.1 :=
  congrArg (fun z : TotalSpace F E × A => z.1.proj)
    (sumKerHomeomorph_symm_apply_val β ρ hρβ hκ hβTotal hρTotal y)

/-- The forward fiber coordinate is the existing bundled coproduct of the given linear map
and the kernel inclusion. In particular it is linear for the original `R`-actions. -/
theorem sumKerHomeomorph_fiber_eq_coprod (b : B) :
    (fun w : E b × (ρ b).ker =>
      (sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal (TotalSpace.mk' (F × G) b w)).2) =
      (LinearMap.coprod (β b) (ρ b).ker.subtype : E b × (ρ b).ker → A) := by
  funext w
  simp only [sumKerHomeomorph_apply, LinearMap.coprod_apply]
  rfl

end

end Bundle.TotalSpace
