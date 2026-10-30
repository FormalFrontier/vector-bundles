/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import VectorBundles.Topology.VectorBundle.FiniteEmbedding.Chart

/-!
# Linear equivalences on fibres of a trivialization

For `b ∈ e.baseSet`, a trivialization `e : Bundle.Trivialization F p` of `p : T → B`
restricts to a homeomorphism from `p ⁻¹' {b}` to its model fibre. If the coordinate function
on this fibre is linear for the given module structure, this homeomorphism is a linear equivalence
and a continuous linear equivalence.

The fibre has the subspace topology inherited from `T`. No continuity of addition or
scalar multiplication, topology on the scalar semiring, or bundle typeclass is needed.
The constructed equivalences support the usual `map_zero`, `map_add` and `map_smul` API.
The comparison with `Trivialization.linearEquivAt` uses an explicitly given linear
identification with the fibre of a total space, compatible with its inclusion.

For a trivialization constructed by `ofPreimageHomeomorph`, linearity of the given
homeomorphism's fibre coordinates supplies the linearity hypothesis for these
refinements. The continuous linear equivalence retains those same coordinates.
-/

@[expose] public section

universe uR uB uT uF uE

namespace Bundle.Trivialization

section Projection

variable {R : Type uR} {B : Type uB} {T : Type uT} {F : Type uF}
  [Semiring R] [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace F]
  [AddCommMonoid F] [Module R F] {p : T → B}
  (e : Trivialization F p) {b : B}
  [AddCommMonoid (p ⁻¹' {b})] [Module R (p ⁻¹' {b})]

/-- A trivialization whose coordinate function on a fibre is linear gives a linear
 equivalence from that fibre to the model fibre. Its underlying equivalence is the one
 supplied by `preimageSingletonHomeomorph`. -/
def preimageSingletonLinearEquiv (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) :
    (p ⁻¹' {b}) ≃ₗ[R] F :=
  (e.preimageSingletonHomeomorph hb).toEquiv.toLinearEquiv hlinear

@[simp]
theorem preimageSingletonLinearEquiv_apply (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2))
    (v : p ⁻¹' {b}) :
    e.preimageSingletonLinearEquiv hb hlinear v = (e v.val).2 :=
  rfl

@[simp]
theorem preimageSingletonLinearEquiv_toEquiv (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) :
    (e.preimageSingletonLinearEquiv hb hlinear).toEquiv =
      (e.preimageSingletonHomeomorph hb).toEquiv :=
  rfl

@[simp]
theorem preimageSingletonLinearEquiv_symm_apply_val (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) (w : F) :
    ((e.preimageSingletonLinearEquiv hb hlinear).symm w).val =
      e.toOpenPartialHomeomorph.symm (b, w) :=
  rfl

theorem preimageSingletonLinearEquiv_symm_apply_proj (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) (w : F) :
    p ((e.preimageSingletonLinearEquiv hb hlinear).symm w).val = b := by
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
    ((e.preimageSingletonLinearEquiv hb hlinear).symm w).property

/-- The coordinate equation characterizes the linear equivalence on a fibre. -/
theorem preimageSingletonLinearEquiv_eq_iff (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2))
    (L : (p ⁻¹' {b}) ≃ₗ[R] F) :
    e.preimageSingletonLinearEquiv hb hlinear = L ↔
      ∀ v, L v = (e v.val).2 := by
  constructor
  · intro h v
    rw [← h]
    rfl
  · intro h
    exact LinearEquiv.ext fun v => (h v).symm

/-- A supplied linear equivalence with the coordinate equation proves linearity of the
 coordinate function for the given fibre module. -/
theorem isLinearMap_snd_of_linearEquiv (L : (p ⁻¹' {b}) ≃ₗ[R] F)
    (hL : ∀ v, L v = (e v.val).2) :
    IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2) where
  map_add v w := by
    rw [← hL (v + w), ← hL v, ← hL w, map_add]
  map_smul c v := by
    rw [← hL (c • v), ← hL v, map_smul]

/-- Starting with a linear equivalence satisfying the coordinate equation recovers
 that same equivalence from the trivialization. -/
theorem preimageSingletonLinearEquiv_of_linearEquiv (hb : b ∈ e.baseSet)
    (L : (p ⁻¹' {b}) ≃ₗ[R] F) (hL : ∀ v, L v = (e v.val).2) :
    e.preimageSingletonLinearEquiv hb (e.isLinearMap_snd_of_linearEquiv L hL) = L :=
  (e.preimageSingletonLinearEquiv_eq_iff hb _ L).2 hL

/-- The fibre homeomorphism of a trivialization, with its given linear coordinate
 function, is a continuous linear equivalence for the inherited fibre topology. -/
def preimageSingletonContinuousLinearEquiv (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) :
    (p ⁻¹' {b}) ≃L[R] F where
  toLinearEquiv := e.preimageSingletonLinearEquiv hb hlinear
  continuous_toFun := (e.preimageSingletonHomeomorph hb).continuous
  continuous_invFun := (e.preimageSingletonHomeomorph hb).symm.continuous

@[simp]
theorem preimageSingletonContinuousLinearEquiv_apply (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2))
    (v : p ⁻¹' {b}) :
    e.preimageSingletonContinuousLinearEquiv hb hlinear v = (e v.val).2 :=
  rfl

@[simp]
theorem preimageSingletonContinuousLinearEquiv_toLinearEquiv (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) :
    (e.preimageSingletonContinuousLinearEquiv hb hlinear).toLinearEquiv =
      e.preimageSingletonLinearEquiv hb hlinear :=
  rfl

@[simp]
theorem preimageSingletonContinuousLinearEquiv_toHomeomorph (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) :
    (e.preimageSingletonContinuousLinearEquiv hb hlinear).toHomeomorph =
      e.preimageSingletonHomeomorph hb :=
  rfl

@[simp]
theorem preimageSingletonContinuousLinearEquiv_symm_apply_val (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2)) (w : F) :
    ((e.preimageSingletonContinuousLinearEquiv hb hlinear).symm w).val =
      e.toOpenPartialHomeomorph.symm (b, w) :=
  rfl

/-- The coordinate equation also characterizes the continuous linear equivalence. -/
theorem preimageSingletonContinuousLinearEquiv_eq_iff (hb : b ∈ e.baseSet)
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} => (e v.val).2))
    (L : (p ⁻¹' {b}) ≃L[R] F) :
    e.preimageSingletonContinuousLinearEquiv hb hlinear = L ↔
      ∀ v, L v = (e v.val).2 := by
  constructor
  · intro h v
    rw [← h]
    rfl
  · intro h
    exact ContinuousLinearEquiv.ext (funext fun v => (h v).symm)

/-- A linear equivalence agreeing with the coordinates of a trivialization is
 continuous in both directions for the inherited fibre topology. -/
theorem continuous_linearEquiv_of_apply_eq (hb : b ∈ e.baseSet)
    (L : (p ⁻¹' {b}) ≃ₗ[R] F) (hL : ∀ v, L v = (e v.val).2) :
    Continuous L ∧ Continuous L.symm := by
  have h := e.preimageSingletonLinearEquiv_of_linearEquiv hb L hL
  constructor
  · have hc : Continuous (e.preimageSingletonLinearEquiv hb
        (e.isLinearMap_snd_of_linearEquiv L hL)) :=
      (e.preimageSingletonContinuousLinearEquiv hb
        (e.isLinearMap_snd_of_linearEquiv L hL)).continuous
    simpa only [h] using hc
  · have hc : Continuous (e.preimageSingletonLinearEquiv hb
        (e.isLinearMap_snd_of_linearEquiv L hL)).symm :=
      (e.preimageSingletonContinuousLinearEquiv hb
        (e.isLinearMap_snd_of_linearEquiv L hL)).symm.continuous
    simpa only [h] using hc

end Projection

section PreimageHomeomorph

variable {R : Type uR} {B : Type uB} {T : Type uT} {F : Type uF}
  [Semiring R] [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace F]
  [AddCommMonoid F] [Module R F] {p : T → B} {U : Set B} {b : B}
  [AddCommMonoid (p ⁻¹' {b})] [Module R (p ⁻¹' {b})]
  (hU : IsOpen U) (hp : Continuous p) (h : p ⁻¹' U ≃ₜ U × F)
  (hproj : ∀ t, ((h t).1 : B) = p t) (s : B → T) (hb : b ∈ U)

/-- Linearity of the coordinates of a homeomorphism of a preimage gives linearity
 of the fibre coordinates of its associated trivialization. -/
theorem ofPreimageHomeomorph_isLinearMap_snd
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} =>
      (h ⟨v.val, by
        change p v.val ∈ U
        rw [show p v.val = b from v.property]
        exact hb⟩).2)) :
    IsLinearMap R (fun v : p ⁻¹' {b} =>
      (ofPreimageHomeomorph hU hp h hproj s v.val).2) := by
  have hcoord : (fun v : p ⁻¹' {b} =>
      (ofPreimageHomeomorph hU hp h hproj s v.val).2) =
      (fun v : p ⁻¹' {b} =>
        (h ⟨v.val, by
          change p v.val ∈ U
          rw [show p v.val = b from v.property]
          exact hb⟩).2) := by
    funext v
    rw [ofPreimageHomeomorph_apply hU hp h hproj s
      (by
        rw [show p v.val = b from v.property]
        exact hb)]
  rw [hcoord]
  exact hlinear

/-- The continuous linear equivalence on a fibre of a trivialization constructed from
 a homeomorphism of a preimage has exactly the given homeomorphism's coordinates. -/
theorem ofPreimageHomeomorph_preimageSingletonContinuousLinearEquiv_apply
    (hlinear : IsLinearMap R (fun v : p ⁻¹' {b} =>
      (h ⟨v.val, by
        change p v.val ∈ U
        rw [show p v.val = b from v.property]
        exact hb⟩).2))
    (v : p ⁻¹' {b}) :
    (ofPreimageHomeomorph hU hp h hproj s).preimageSingletonContinuousLinearEquiv
        (by simpa only [ofPreimageHomeomorph_baseSet] using hb)
        (ofPreimageHomeomorph_isLinearMap_snd hU hp h hproj s hb hlinear) v =
      (h ⟨v.val, by
        change p v.val ∈ U
        rw [show p v.val = b from v.property]
        exact hb⟩).2 := by
  rw [preimageSingletonContinuousLinearEquiv_apply,
    ofPreimageHomeomorph_apply hU hp h hproj s
      (by
        rw [show p v.val = b from v.property]
        exact hb)]

end PreimageHomeomorph

section TotalSpace

variable {R : Type uR} {B : Type uB} {F : Type uF} {E : B → Type uE}
  [Semiring R] [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (Bundle.TotalSpace F E)]
  [AddCommMonoid F] [Module R F]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
  [e.IsLinear R] {b : B}
  [AddCommMonoid ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' {b})]
  [Module R ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' {b})]

/-- A linear identification of a total-space fibre with the corresponding preimage,
 compatible with inclusion into the total space, transfers the usual coordinate
 linearity to the given module on the preimage. -/
theorem isLinearMap_snd_of_linearEquivAt (hb : b ∈ e.baseSet)
    (I : E b ≃ₗ[R]
      ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' {b}))
    (hI : ∀ v, (I v).val = Bundle.TotalSpace.mk b v) :
    IsLinearMap R (fun v :
      ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' {b}) => (e v.val).2) := by
  apply e.isLinearMap_snd_of_linearEquiv (I.symm.trans (e.linearEquivAt R b hb))
  intro w
  obtain ⟨v, rfl⟩ := I.surjective w
  rw [LinearEquiv.trans_apply, I.symm_apply_apply, linearEquivAt_apply, hI v]

/-- Under a linear fibre identification compatible with the total-space inclusion,
 the equivalence on the preimage agrees with `linearEquivAt`. The compatibility
 hypothesis relates the two given module structures; neither is replaced. -/
theorem linearEquivAt_eq_trans_preimageSingletonLinearEquiv (hb : b ∈ e.baseSet)
    (I : E b ≃ₗ[R]
      ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' {b}))
    (hI : ∀ v, (I v).val = Bundle.TotalSpace.mk b v) :
    e.linearEquivAt R b hb =
      I.trans (e.preimageSingletonLinearEquiv hb
        (e.isLinearMap_snd_of_linearEquivAt hb I hI)) := by
  apply LinearEquiv.ext
  intro v
  rw [linearEquivAt_apply, LinearEquiv.trans_apply,
    preimageSingletonLinearEquiv_apply, hI v]

end TotalSpace

end Bundle.Trivialization
