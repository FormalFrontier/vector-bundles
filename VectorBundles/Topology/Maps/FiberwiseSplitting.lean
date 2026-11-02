/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import ProjectiveModules.Topology.Splitting
import Mathlib.Algebra.Group.InjSurj

/-!
# Sum–kernel coordinates for additive fibre retractions

Let `p : T → B` have given additive monoid structures on its equality fibres,
with their inherited topologies. Additive maps `β b` into a topological abelian
group `A` and retractions `ρ b` give sum coordinates on the original subspace
`{z : T × A // ρ (p z.1) z.2 = 0}`. Joint continuity of the two total maps gives
`Homeomorph.fiberwiseSumKer`, with inverse given by the prescribed retraction and
residual `a - β b (ρ b a)`.

The characteristic continuity criterion tests a map into this subspace by its
base and sum coordinates. Neither continuous fibre operations nor bundle charts
are required.

## Implementation notes

Injectivity of `β b` derives commutativity without changing the given addition,
zero or natural-number repetition. The canonical `ℕ`-module structures allow
reuse of ProjectiveModules' continuous-linear right-inverse splitting.
Only dependent-index transport and joint continuity on the original carriers
are assembled here. In an application with given `R`-linear maps over any
semiring, use their `LinearMap.toAddMonoidHom`; the auxiliary `ℕ` presentation
does not change the given `R`-actions, functions or topologies. The prescribed
range projector is `β b ∘ ρ b`, not its residual.

## References

* Mathlib's `Function.Injective.addCommMonoid`, `AddCommMonoid.toNatModule` and
  `AddMonoidHom.toNatLinearMap` supply the additive-to-`ℕ` presentation.
* ProjectiveModules' `ContinuousLinearMap.equivProdKerOfRightInverse` supplies
  the pointwise splitting and its inverse laws. Its inverse is the sum of the
  kernel coordinate and the image of the section.
-/

@[expose] public section

universe uB uT uA uX

namespace Homeomorph

variable {B : Type uB} {T : Type uT} {A : Type uA}
  [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace A]
  (p : T → B) [∀ b, AddMonoid {t : T // p t = b}]
  [AddCommGroup A] [IsTopologicalAddGroup A]

variable (β : ∀ b, {t : T // p t = b} →+ A)
  (ρ : ∀ b, A →+ {t : T // p t = b})
  (hρβ : ∀ b, Function.RightInverse (β b) (ρ b))
  (hβTotal : Continuous (fun t : T ↦ (p t, β (p t) ⟨t, rfl⟩)))
  (hρTotal : Continuous (fun y : B × A ↦ (ρ y.1 y.2).val))

/-- Sum–kernel coordinates for additive retractions on the original equality
fibres of a projection. The domain has its product-subspace topology, and the
coordinates are `(p t, β (p t) ⟨t, rfl⟩ + v)`. The inverse is the given
retraction together with `a - β b (ρ b a)`.

Only continuity of the two displayed total maps is assumed. The fibre monoids
retain their given operations and inherited topology; no continuity of those
operations is required. For given linear maps over a semiring, forgetting
linearity with `LinearMap.toAddMonoidHom` leaves the functions and scalar actions
unchanged. The pointwise equivalence and its laws are supplied by
`ContinuousLinearMap.equivProdKerOfRightInverse` over `ℕ`. -/
def fiberwiseSumKer :
    {z : T × A // ρ (p z.1) z.2 = 0} ≃ₜ B × A := by
  have hβval {b : B} (u : {t : T // p t = b}) :
      β (p u.val) ⟨u.val, rfl⟩ = β b u := by
    rcases u with ⟨t, ht⟩
    cases ht
    rfl
  have hρzero {b : B} (u : {t : T // p t = b}) {a : A}
      (ha : ρ b a = 0) : ρ (p u.val) a = 0 := by
    rcases u with ⟨t, ht⟩
    cases ht
    exact ha
  have hp : Continuous p := hβTotal.fst
  have hβb (b : B) : Continuous (β b) := by
    have h : Continuous (fun u : {t : T // p t = b} ↦
        β (p u.val) ⟨u.val, rfl⟩) :=
      (hβTotal.comp continuous_subtype_val).snd
    exact h.congr (fun u ↦ hβval u)
  have hρb (b : B) : Continuous (ρ b) :=
    (hρTotal.comp (continuous_const.prodMk continuous_id)).subtype_mk
      (fun a ↦ (ρ b a).property)
  -- This transport retains the original nsmul as well as addition and zero.
  letI (b : B) : AddCommMonoid {t : T // p t = b} :=
    (hρβ b).injective.addCommMonoid (β b) (β b).map_zero
      (β b).map_add (fun u n ↦ (β b).map_nsmul n u)
  letI : Module ℕ A := AddCommMonoid.toNatModule
  letI (b : B) : Module ℕ {t : T // p t = b} := AddCommMonoid.toNatModule
  let βL (b : B) : {t : T // p t = b} →L[ℕ] A :=
    { toLinearMap := (β b).toNatLinearMap
      cont := by
        change Continuous (β b)
        exact hβb b }
  let ρL (b : B) : A →L[ℕ] {t : T // p t = b} :=
    { toLinearMap := (ρ b).toNatLinearMap
      cont := by
        change Continuous (ρ b)
        exact hρb b }
  let e (b : B) := (ρL b).equivProdKerOfRightInverse (βL b) (hρβ b)
  have he_fst (b : B) (a : A) : (e b a).1 = ρ b a :=
    ContinuousLinearMap.fst_equivProdKerOfRightInverse (ρL b) (βL b) (hρβ b) a
  have he_snd (b : B) (a : A) :
      ((e b a).2 : A) = a - β b (ρ b a) :=
    ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse (ρL b) (βL b) (hρβ b) a
  have he_symm (b : B) (w : {t : T // p t = b} × (ρL b).ker) :
      (e b).symm w = β b w.1 + (w.2 : A) :=
    (ContinuousLinearMap.equivProdKerOfRightInverse_symm_apply
      (ρL b) (βL b) (hρβ b) w).trans (add_comm _ _)
  have hker (b : B) (a : A) : ρ b (a - β b (ρ b a)) = 0 := by
    have h : ρ b ((e b a).2 : A) = 0 := (e b a).2.property
    simpa only [he_snd] using h
  let inv : B × A → {z : T × A // ρ (p z.1) z.2 = 0} := fun y ↦
    ⟨((ρ y.1 y.2).val, y.2 - β y.1 (ρ y.1 y.2)),
      hρzero (ρ y.1 y.2) (hker y.1 y.2)⟩
  refine
    { toFun := fun z ↦ (p z.val.1, β (p z.val.1) ⟨z.val.1, rfl⟩ + z.val.2)
      invFun := inv
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    let b := p z.val.1
    let u : {t : T // p t = b} := ⟨z.val.1, rfl⟩
    let w : {t : T // p t = b} × (ρL b).ker := (u, ⟨z.val.2, z.property⟩)
    have hw : e b (β b u + z.val.2) = w := calc
      e b (β b u + z.val.2) = e b ((e b).symm w) :=
        congrArg (e b) (he_symm b w).symm
      _ = w := (e b).apply_symm_apply w
    apply Subtype.ext
    apply Prod.ext
    · change (ρ b (β b u + z.val.2)).val = z.val.1
      have h := congrArg Prod.fst hw
      rw [he_fst] at h
      exact congrArg Subtype.val h
    · change (β b u + z.val.2) - β b (ρ b (β b u + z.val.2)) = z.val.2
      have h := congrArg
        (fun q : {t : T // p t = b} × (ρL b).ker ↦ (q.2 : A)) hw
      simpa only [he_snd] using h
  · intro y
    apply Prod.ext
    · exact (ρ y.1 y.2).property
    · change β (p ((ρ y.1 y.2).val)) ⟨(ρ y.1 y.2).val, rfl⟩ +
          (y.2 - β y.1 (ρ y.1 y.2)) = y.2
      rw [hβval (ρ y.1 y.2)]
      have h := (e y.1).symm_apply_apply y.2
      rw [he_symm, he_fst, he_snd] at h
      exact h
  · have ht : Continuous
        (fun z : {z : T × A // ρ (p z.1) z.2 = 0} ↦ z.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have hv : Continuous
        (fun z : {z : T × A // ρ (p z.1) z.2 = 0} ↦ z.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (hp.comp ht).prodMk ((hβTotal.comp ht).snd.add hv)
  · have hinv : Continuous (fun y : B × A ↦
        ((ρ y.1 y.2).val, y.2 - β y.1 (ρ y.1 y.2))) := by
      refine (hρTotal.prodMk (continuous_snd.sub (hβTotal.comp hρTotal).snd)).congr ?_
      intro y
      apply Prod.ext
      · rfl
      · exact congrArg (fun a : A ↦ y.2 - a) (hβval (ρ y.1 y.2))
    exact hinv.subtype_mk (fun y ↦ (inv y).property)

/-- Evaluation of the base and sum coordinates of `fiberwiseSumKer`. -/
@[simp]
theorem fiberwiseSumKer_apply (z : {z : T × A // ρ (p z.1) z.2 = 0}) :
    fiberwiseSumKer p β ρ hρβ hβTotal hρTotal z =
      (p z.val.1, β (p z.val.1) ⟨z.val.1, rfl⟩ + z.val.2) := rfl

/-- The inverse has the original total-space value of `ρ` and its ambient residual. -/
@[simp]
theorem fiberwiseSumKer_symm_apply_val (y : B × A) :
    ((fiberwiseSumKer p β ρ hρβ hβTotal hρTotal).symm y).val =
      ((ρ y.1 y.2).val, y.2 - β y.1 (ρ y.1 y.2)) := rfl

include hρβ hβTotal hρTotal in
/-- A map into the original sum–kernel subspace is continuous exactly when its
base coordinate and sum coordinate are continuous. -/
theorem continuous_iff_fiberwiseSumKer {X : Type uX} [TopologicalSpace X]
    (f : X → {z : T × A // ρ (p z.1) z.2 = 0}) :
    Continuous f ↔
      Continuous (fun x ↦ p (f x).val.1) ∧
        Continuous (fun x ↦
          β (p (f x).val.1) ⟨(f x).val.1, rfl⟩ + (f x).val.2) := by
  let e := fiberwiseSumKer p β ρ hρβ hβTotal hρTotal
  constructor
  · intro hf
    have h : Continuous (fun x ↦ e (f x)) := e.continuous_toFun.comp hf
    constructor
    · simpa only [e, fiberwiseSumKer_apply] using h.fst
    · simpa only [e, fiberwiseSumKer_apply] using h.snd
  · rintro ⟨hb, hs⟩
    apply e.comp_continuous_iff.mp
    simpa only [Function.comp_def, e, fiberwiseSumKer_apply] using hb.prodMk hs

end Homeomorph
