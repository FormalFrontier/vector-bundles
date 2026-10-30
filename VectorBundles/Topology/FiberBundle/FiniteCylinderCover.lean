/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Choose

/-!
# Finite product-chart covers from local product charts

For a compact base and an arbitrary topological parameter space with a chosen
point, whole-product charts supplied near every base point admit an ordered
finite subcover. The topological theorem retains the selected original chart
model, the homeomorphism on the original projection preimage, both base laws,
and agreement with the original chart in both directions on the chosen slice.
The linear theorem also retains coordinate linear equivalences on the given
original projection fibers, their forward and inverse formulas at every
parameter, and their identification with the original linear chart coordinates
on the chosen slice. The cylinder-cover theorems are the specializations to the
unit interval with chosen point `0`.

## Implementation notes

Compactness is required only of the base and is used through
`IsCompact.elim_finite_subcover`. The finite family is obtained by enumerating a
finite set of centers and pulling back the selected data along that enumeration.
All subtype topologies and module structures are the given ones.

## Limitations

The local whole-product charts are input; these results do not construct such
charts from an ordinary local atlas. No compactness of the parameter space,
continuity of the projection, openness of the original chart domains, atlas
coverage, normality, separation, nonemptiness, common model, rank, weights,
scalar topology or continuity of module operations is required.

## References

- The Mathlib contributors, `IsCompact.elim_finite_subcover` for compactness and
  `Finset.equivFin` for enumeration of finite sets.
-/

@[expose] public section

open Set
open scoped unitInterval

namespace Bundle.Trivialization

universe uX uT uJ uF uR

private theorem exists_finite_centers
    {X : Type uX} [TopologicalSpace X] [CompactSpace X]
    (U : X → Set X) (hU : ∀ x, IsOpen (U x)) (hx : ∀ x, x ∈ U x) :
    ∃ (n : ℕ) (c : Fin n → X), (⋃ k, U (c k)) = univ := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hx x⟩)
  let c : Fin s.card → X := fun k ↦ (s.equivFin.symm k).val
  refine ⟨s.card, c, ?_⟩
  apply subset_antisymm (subset_univ _)
  intro x _
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine mem_iUnion.mpr ⟨s.equivFin ⟨y, hy⟩, ?_⟩
  simpa only [c, Equiv.symm_apply_apply] using hxy

section Product

universe uY

variable {X : Type uX} {T : Type uT} {J : Type uJ}
variable [TopologicalSpace X] [TopologicalSpace T] [CompactSpace X]
variable {Y : Type uY} [TopologicalSpace Y] (y₀ : Y)
variable (p : T → X × Y)
variable (F : J → Type uF) [∀ j, TopologicalSpace (F j)]
variable (W : J → Set (X × Y))
variable (e : ∀ j, (p ⁻¹' W j) ≃ₜ (W j) × F j)

/-- Local whole-product charts over a compact base and an arbitrary topological
parameter space with chosen point `y₀` admit a finite ordered open cover, with a
center in each member. Each selected chart keeps its original model, both
whole-base laws and both original-chart laws on the chosen slice.

Only the base is required to be compact. The empty base is allowed, with no
nonemptiness assumption on the models or the original chart index type. -/
theorem exists_finiteProductCover_of_local
    (hlocal : ∀ x : X,
      ∃ (U : Set X) (j₀ : J)
        (hU₀ : ∀ u : U, (u.val, y₀) ∈ W j₀)
        (H : {z : T // (p z).1 ∈ U} ≃ₜ (U × Y) × F j₀),
        IsOpen U ∧ x ∈ U ∧
        (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
        (∀ q : (U × Y) × F j₀,
          p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
        (∀ (u : U) (v : {z : T // p z = (u.val, y₀)}),
          (H ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
          (e j₀ ⟨v.val,
            Eq.mpr (congrArg (fun b ↦ b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
        (∀ (u : U) (v : F j₀),
          (H.symm ((u, y₀), v)).val =
          ((e j₀).symm (⟨(u.val, y₀), hU₀ u⟩, v)).val)) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, y₀) ∈ W (j₀ k))
      (H : ∀ k, {z : T // (p z).1 ∈ U k} ≃ₜ
        ((U k) × Y) × F (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × Y) × F (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : T // p z = (u.val, y₀)}),
        (H k ⟨v.val,
          (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b ↦ b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : F (j₀ k)),
        ((H k).symm ((u, y₀), v)).val =
        ((e (j₀ k)).symm
          (⟨(u.val, y₀), hU₀ k u⟩, v)).val) := by
  classical
  choose U j hU₀ H hU hx hbase hbase_symm hbottom hbottom_symm using hlocal
  obtain ⟨n, c, hcover⟩ := exists_finite_centers U hU hx
  exact ⟨n, c, (fun k ↦ U (c k)), (fun k ↦ j (c k)),
    (fun k ↦ hU₀ (c k)), (fun k ↦ H (c k)),
    (fun k ↦ hU (c k)), (fun k ↦ hx (c k)), hcover,
    (fun k ↦ hbase (c k)), (fun k ↦ hbase_symm (c k)),
    (fun k ↦ hbottom (c k)), (fun k ↦ hbottom_symm (c k))⟩

variable {R : Type uR} [Semiring R]
variable [∀ j, AddCommMonoid (F j)] [∀ j, Module R (F j)]
variable [∀ b : X × Y, AddCommMonoid {z : T // p z = b}]
variable [∀ b : X × Y, Module R {z : T // p z = b}]
variable (L : ∀ (j : J) (b : X × Y), b ∈ W j →
  {z : T // p z = b} ≃ₗ[R] F j)

/-- Local whole-product charts with linear coordinates on the given original
projection fibers over an arbitrary semiring admit a finite ordered open cover.
All homeomorphism laws, both original-chart chosen-slice laws, the forward and
inverse linear-coordinate formulas at every parameter, and the original linear
equivalences on the chosen slice are retained for each chosen center.

Only the base is required to be compact. The scalar semiring need not be
commutative and has no topology assumptions; the base, parameter space, total
space, chart indices, varying models and scalar type have independent universes. -/
theorem exists_finiteLinearProductCover_of_local
    (hlocal : ∀ x : X,
      ∃ (U : Set X) (j₀ : J)
        (hU₀ : ∀ u : U, (u.val, y₀) ∈ W j₀)
        (H : {z : T // (p z).1 ∈ U} ≃ₜ (U × Y) × F j₀)
        (K : ∀ (u : U) (t : Y),
          {z : T // p z = (u.val, t)} ≃ₗ[R] F j₀),
        IsOpen U ∧ x ∈ U ∧
        (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
        (∀ q : (U × Y) × F j₀,
          p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
        (∀ (u : U) (v : {z : T // p z = (u.val, y₀)}),
          (H ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
          (e j₀ ⟨v.val,
            Eq.mpr (congrArg (fun b ↦ b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
        (∀ (u : U) (v : F j₀),
          (H.symm ((u, y₀), v)).val =
          ((e j₀).symm (⟨(u.val, y₀), hU₀ u⟩, v)).val) ∧
        (∀ (u : U) (t : Y) (v : {z : T // p z = (u.val, t)}),
          K u t v =
            (H ⟨v.val,
              (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
        (∀ (u : U) (t : Y) (v : F j₀),
          (H.symm ((u, t), v)).val = ((K u t).symm v).val) ∧
        (∀ u : U, K u y₀ =
          L j₀ (u.val, y₀) (hU₀ u))) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, y₀) ∈ W (j₀ k))
      (H : ∀ k, {z : T // (p z).1 ∈ U k} ≃ₜ
        ((U k) × Y) × F (j₀ k))
      (K : ∀ k (u : U k) (t : Y),
        {z : T // p z = (u.val, t)} ≃ₗ[R] F (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × Y) × F (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : T // p z = (u.val, y₀)}),
        (H k ⟨v.val,
          (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b ↦ b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : F (j₀ k)),
        ((H k).symm ((u, y₀), v)).val =
        ((e (j₀ k)).symm
          (⟨(u.val, y₀), hU₀ k u⟩, v)).val) ∧
      (∀ k (u : U k) (t : Y)
          (v : {z : T // p z = (u.val, t)}),
        K k u t v =
          (H k ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
      (∀ k (u : U k) (t : Y) (v : F (j₀ k)),
        ((H k).symm ((u, t), v)).val = ((K k u t).symm v).val) ∧
      (∀ k (u : U k), K k u y₀ =
        L (j₀ k) (u.val, y₀) (hU₀ k u)) := by
  classical
  choose U j hU₀ H K hU hx hbase hbase_symm hbottom hbottom_symm
    hlinear hlinear_symm hlinear_bottom using hlocal
  obtain ⟨n, c, hcover⟩ := exists_finite_centers U hU hx
  exact ⟨n, c, (fun k ↦ U (c k)), (fun k ↦ j (c k)),
    (fun k ↦ hU₀ (c k)), (fun k ↦ H (c k)), (fun k ↦ K (c k)),
    (fun k ↦ hU (c k)), (fun k ↦ hx (c k)), hcover,
    (fun k ↦ hbase (c k)), (fun k ↦ hbase_symm (c k)),
    (fun k ↦ hbottom (c k)), (fun k ↦ hbottom_symm (c k)),
    (fun k ↦ hlinear (c k)), (fun k ↦ hlinear_symm (c k)),
    (fun k ↦ hlinear_bottom (c k))⟩

end Product

variable {X : Type uX} {T : Type uT} {J : Type uJ}
variable [TopologicalSpace X] [TopologicalSpace T] [CompactSpace X]
variable (p : T → X × I)
variable (F : J → Type uF) [∀ j, TopologicalSpace (F j)]
variable (W : J → Set (X × I))
variable (e : ∀ j, (p ⁻¹' W j) ≃ₜ (W j) × F j)

/-- Local whole-cylinder charts over a compact base admit a finite ordered open
cover, with a center in each member. Each selected chart keeps its original
model, both whole-base laws and both original-chart bottom laws.

This is `exists_finiteProductCover_of_local` for the unit interval with chosen
point `0`. The empty base is allowed, with no nonemptiness assumption on the
models or the original chart index type. -/
theorem exists_finiteCylinderCover_of_local
    (hlocal : ∀ x : X,
      ∃ (U : Set X) (j₀ : J)
        (hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀)
        (H : {z : T // (p z).1 ∈ U} ≃ₜ (U × I) × F j₀),
        IsOpen U ∧ x ∈ U ∧
        (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
        (∀ q : (U × I) × F j₀,
          p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
        (∀ (u : U) (v : {z : T // p z = (u.val, (0 : I))}),
          (H ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
          (e j₀ ⟨v.val,
            Eq.mpr (congrArg (fun b ↦ b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
        (∀ (u : U) (v : F j₀),
          (H.symm ((u, (0 : I)), v)).val =
          ((e j₀).symm (⟨(u.val, (0 : I)), hU₀ u⟩, v)).val)) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, (0 : I)) ∈ W (j₀ k))
      (H : ∀ k, {z : T // (p z).1 ∈ U k} ≃ₜ
        ((U k) × I) × F (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × I) × F (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : T // p z = (u.val, (0 : I))}),
        (H k ⟨v.val,
          (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b ↦ b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : F (j₀ k)),
        ((H k).symm ((u, (0 : I)), v)).val =
        ((e (j₀ k)).symm
          (⟨(u.val, (0 : I)), hU₀ k u⟩, v)).val) := by
  exact exists_finiteProductCover_of_local (0 : I) p F W e hlocal

variable {R : Type uR} [Semiring R]
variable [∀ j, AddCommMonoid (F j)] [∀ j, Module R (F j)]
variable [∀ b : X × I, AddCommMonoid {z : T // p z = b}]
variable [∀ b : X × I, Module R {z : T // p z = b}]
variable (L : ∀ (j : J) (b : X × I), b ∈ W j →
  {z : T // p z = b} ≃ₗ[R] F j)

/-- Local whole-cylinder charts with linear coordinates on the given original
projection fibers over an arbitrary semiring admit a finite ordered open cover.
All homeomorphism laws, both original-chart bottom laws, the forward and inverse
linear-coordinate formulas, and the original bottom linear equivalences are
retained for each chosen center.

This is `exists_finiteLinearProductCover_of_local` for the unit interval with
chosen point `0`. The scalar semiring need not be commutative and has no topology
assumptions; the base, total space, chart indices, varying models and scalar type
have independent universes. -/
theorem exists_finiteLinearCylinderCover_of_local
    (hlocal : ∀ x : X,
      ∃ (U : Set X) (j₀ : J)
        (hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀)
        (H : {z : T // (p z).1 ∈ U} ≃ₜ (U × I) × F j₀)
        (K : ∀ (u : U) (t : I),
          {z : T // p z = (u.val, t)} ≃ₗ[R] F j₀),
        IsOpen U ∧ x ∈ U ∧
        (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
        (∀ q : (U × I) × F j₀,
          p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
        (∀ (u : U) (v : {z : T // p z = (u.val, (0 : I))}),
          (H ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
          (e j₀ ⟨v.val,
            Eq.mpr (congrArg (fun b ↦ b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
        (∀ (u : U) (v : F j₀),
          (H.symm ((u, (0 : I)), v)).val =
          ((e j₀).symm (⟨(u.val, (0 : I)), hU₀ u⟩, v)).val) ∧
        (∀ (u : U) (t : I) (v : {z : T // p z = (u.val, t)}),
          K u t v =
            (H ⟨v.val,
              (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
        (∀ (u : U) (t : I) (v : F j₀),
          (H.symm ((u, t), v)).val = ((K u t).symm v).val) ∧
        (∀ u : U, K u (0 : I) =
          L j₀ (u.val, (0 : I)) (hU₀ u))) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, (0 : I)) ∈ W (j₀ k))
      (H : ∀ k, {z : T // (p z).1 ∈ U k} ≃ₜ
        ((U k) × I) × F (j₀ k))
      (K : ∀ k (u : U k) (t : I),
        {z : T // p z = (u.val, t)} ≃ₗ[R] F (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × I) × F (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : T // p z = (u.val, (0 : I))}),
        (H k ⟨v.val,
          (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b ↦ b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : F (j₀ k)),
        ((H k).symm ((u, (0 : I)), v)).val =
        ((e (j₀ k)).symm
          (⟨(u.val, (0 : I)), hU₀ k u⟩, v)).val) ∧
      (∀ k (u : U k) (t : I)
          (v : {z : T // p z = (u.val, t)}),
        K k u t v =
          (H k ⟨v.val,
            (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
      (∀ k (u : U k) (t : I) (v : F (j₀ k)),
        ((H k).symm ((u, t), v)).val = ((K k u t).symm v).val) ∧
      (∀ k (u : U k), K k u (0 : I) =
        L (j₀ k) (u.val, (0 : I)) (hU₀ k u)) := by
  exact exists_finiteLinearProductCover_of_local (0 : I) p F W e L hlocal

end Bundle.Trivialization
