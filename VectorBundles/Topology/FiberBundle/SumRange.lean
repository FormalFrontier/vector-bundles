/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SumKer
public import VectorBundles.Topology.VectorBundle.Range
import Mathlib.LinearAlgebra.Projection

/-!
# Sum coordinates with a complementary range

A family of linear retractions from a topological additive group gives sum coordinates on
its encoded family and the range of the complementary endomorphisms `id - β.comp ρ`.
The range total space has `VectorBundle.rangeTotalSpaceTopology`, induced by the base and
ambient vector coordinates. The sum total space has `FiberBundle.Prod.topologicalSpace`,
formed from the given topology on the encoded total space and this range topology.

`Bundle.TotalSpace.sumRangeHomeomorph` preserves the base and sends `(e, s)` to `β e + s`.
Its inverse recovers `ρ a` and the complementary component `(id - β.comp ρ) a`.
The forward fiber coordinate is `LinearMap.coprod` for the given scalar actions.
No topology on the scalar semiring or the phantom model parameters, continuity of fiber
operations, local triviality, norm or dimension hypothesis is needed.

## Implementation notes

The complementary range equals the kernel of the given retraction. Equality elimination
on this submodule family transports its total-space topology and inducing graph together.
The construction then uses `Bundle.TotalSpace.sumKerHomeomorph`; no new splitting or
product-topology construction is introduced.

## References

* Mathlib's `LinearMap.IsIdempotentElem.ker_eq_range` identifies the complementary range.
* VectorBundles' `Bundle.TotalSpace.sumKerHomeomorph` supplies the sum–kernel coordinates.
-/

public section

open Bundle Topology

universe uR uB uA uE uF uG

namespace LinearMap

/-- The complementary range of a split linear injection is the kernel of its retraction.
The source of the injection only needs an additive commutative monoid: all subtraction
occurs among endomorphisms of the ambient additive group. -/
theorem range_id_sub_comp_eq_ker {R : Type uR} [Semiring R]
    {E : Type uE} [AddCommMonoid E] [Module R E]
    {A : Type uA} [AddCommGroup A] [Module R A]
    (β : E →ₗ[R] A) (ρ : A →ₗ[R] E) (hρβ : Function.LeftInverse ρ β) :
    (LinearMap.id - β.comp ρ).range = ρ.ker := by
  have hIdempotent : IsIdempotentElem (β.comp ρ) := by
    change (β.comp ρ) * (β.comp ρ) = β.comp ρ
    ext a
    exact congrArg β (hρβ (ρ a))
  exact (LinearMap.IsIdempotentElem.ker_eq_range hIdempotent).symm.trans
    (LinearMap.ker_comp_of_ker_eq_bot ρ
      (LinearMap.ker_eq_bot_of_injective hρβ.injective))

end LinearMap

namespace Bundle.TotalSpace

noncomputable section

variable {R : Type uR} [Semiring R] {B : Type uB} [TopologicalSpace B]
  {A : Type uA} [AddCommGroup A] [Module R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] {E : B → Type uE}
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  {F : Type uF} {G : Type uG} [tE : TopologicalSpace (TotalSpace F E)]
  (β : ∀ b, E b →ₗ[R] A) (ρ : ∀ b, A →ₗ[R] E b)
  (hρβ : ∀ b e, ρ b (β b e) = e)
  (hβTotal : Continuous (fun t : TotalSpace F E => (t.proj, β t.proj t.snd)))
  (hρTotal : Continuous (fun y : B × A => TotalSpace.mk' F y.1 (ρ y.1 y.2)))

-- This is exactly the literal graph-induced range topology; the product topology below
-- is formed from it and the given original total-space topology.
private abbrev complementaryRangeTopology :
    TopologicalSpace
      (TotalSpace G (fun b => (LinearMap.id - (β b).comp (ρ b)).range)) :=
  VectorBundle.rangeTotalSpaceTopology (F := G)
    (fun b => LinearMap.id - (β b).comp (ρ b))

-- Register the same canonical product topology directly for inverse Homeomorph projections.
-- Both aliases are reducible and private; neither introduces a topology parameter.
private abbrev complementarySumTopology :
    TopologicalSpace (TotalSpace (F × G)
      (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) :=
  @FiberBundle.Prod.topologicalSpace B F E G
    (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
    (VectorBundle.rangeTotalSpaceTopology (F := G)
      (fun b => LinearMap.id - (β b).comp (ρ b)))

attribute [local instance] complementaryRangeTopology complementarySumTopology

private def sumRangeHomeomorphData :
    {H : @Homeomorph
      (TotalSpace (F × G) (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range))
      (B × A)
      (@FiberBundle.Prod.topologicalSpace B F E G
        (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
        (VectorBundle.rangeTotalSpaceTopology (F := G)
          (fun b => LinearMap.id - (β b).comp (ρ b)))) inferInstance //
      (∀ c, H c = (c.proj, β c.proj c.snd.1 + (c.snd.2 : A))) ∧
      (∀ y : B × A, let c := H.symm y
        ((TotalSpace.mk' F c.proj c.snd.1 : TotalSpace F E), (c.snd.2 : A)) =
          ((TotalSpace.mk' F y.1 (ρ y.1 y.2) : TotalSpace F E),
            y.2 - β y.1 (ρ y.1 y.2)))} := by
  -- Transport the topology and its graph assertion with the submodule family, rather than
  -- putting a separately chosen topology on the kernel total space.
  let assemble (S : B → Submodule R A)
      [tS : TopologicalSpace (TotalSpace G (fun b => S b))]
      (hS : S = fun b => (ρ b).ker)
      (hκ : IsInducing (fun k : TotalSpace G (fun b => S b) => (k.proj, (k.snd : A)))) :
      {H : TotalSpace (F × G) (fun b => E b × S b) ≃ₜ B × A //
        (∀ c, H c = (c.proj, β c.proj c.snd.1 + (c.snd.2 : A))) ∧
        (∀ y : B × A, let c := H.symm y
          ((TotalSpace.mk' F c.proj c.snd.1 : TotalSpace F E), (c.snd.2 : A)) =
            ((TotalSpace.mk' F y.1 (ρ y.1 y.2) : TotalSpace F E),
              y.2 - β y.1 (ρ y.1 y.2)))} := by
    subst S
    exact ⟨sumKerHomeomorph β ρ hρβ hκ hβTotal hρTotal,
      sumKerHomeomorph_apply β ρ hρβ hκ hβTotal hρTotal,
      sumKerHomeomorph_symm_apply_val β ρ hρβ hκ hβTotal hρTotal⟩
  letI := VectorBundle.rangeTotalSpaceTopology (F := G)
    (fun b => LinearMap.id - (β b).comp (ρ b))
  exact assemble (fun b => (LinearMap.id - (β b).comp (ρ b)).range)
    (funext fun b => LinearMap.range_id_sub_comp_eq_ker (β b) (ρ b) (hρβ b)) ⟨rfl⟩

/-- Sum coordinates on a family and the range of its complementary endomorphisms.
The source carries the canonical fiberwise-product topology formed from the given first
total-space topology and `VectorBundle.rangeTotalSpaceTopology` on the complementary range.
The phantom parameters are independent and need no structure. -/
def sumRangeHomeomorph :
    @Homeomorph
      (TotalSpace (F × G) (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range))
      (B × A)
      (@FiberBundle.Prod.topologicalSpace B F E G
        (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
        (VectorBundle.rangeTotalSpaceTopology (F := G)
          (fun b => LinearMap.id - (β b).comp (ρ b)))) inferInstance :=
  (sumRangeHomeomorphData (G := G) β ρ hρβ hβTotal hρTotal).val

/-- Evaluation of the base and sum coordinates on an arbitrary bundle-sum point. -/
@[simp]
theorem sumRangeHomeomorph_apply
    (c : TotalSpace (F × G)
      (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) :
    sumRangeHomeomorph β ρ hρβ hβTotal hρTotal c =
      (c.proj, β c.proj c.snd.1 + (c.snd.2 : A)) :=
  (sumRangeHomeomorphData (G := G) β ρ hρβ hβTotal hρTotal).property.1 c

/-- On a constructed sum point the coordinates use the given fiber values. -/
theorem sumRangeHomeomorph_apply_mk (b : B) (e : E b)
    (s : (LinearMap.id - (β b).comp (ρ b)).range) :
    sumRangeHomeomorph β ρ hρβ hβTotal hρTotal
      (TotalSpace.mk' (F × G) b (e, s)) = (b, β b e + (s : A)) :=
  sumRangeHomeomorph_apply β ρ hρβ hβTotal hρTotal _

/-- The sum coordinates preserve the base point. -/
@[simp]
theorem sumRangeHomeomorph_apply_fst
    (c : TotalSpace (F × G)
      (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) :
    (sumRangeHomeomorph β ρ hρβ hβTotal hρTotal c).1 = c.proj := by
  rw [sumRangeHomeomorph_apply]

/-- The inverse recovers the retraction total-space point and complementary ambient value.
The first equality is in the given total space, avoiding comparisons of different fibers. -/
@[simp]
theorem sumRangeHomeomorph_symm_apply_val (y : B × A) :
    let c := @Homeomorph.symm
      (TotalSpace (F × G)
        (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) (B × A)
      (@FiberBundle.Prod.topologicalSpace B F E G
        (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
        (VectorBundle.rangeTotalSpaceTopology (F := G)
          (fun b => LinearMap.id - (β b).comp (ρ b)))) inferInstance
      (sumRangeHomeomorph (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal) y
    ((TotalSpace.mk' F c.proj c.snd.1 : TotalSpace F E), (c.snd.2 : A)) =
      ((TotalSpace.mk' F y.1 (ρ y.1 y.2) : TotalSpace F E),
        ((LinearMap.id : A →ₗ[R] A) - (β y.1).comp (ρ y.1)) y.2) :=
  (sumRangeHomeomorphData (F := F) (G := G) (tE := tE)
    β ρ hρβ hβTotal hρTotal).property.2 y

/-- The inverse preserves the base point. -/
@[simp]
theorem sumRangeHomeomorph_symm_apply_proj (y : B × A) :
    (@Homeomorph.symm
      (TotalSpace (F × G)
        (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) (B × A)
      (@FiberBundle.Prod.topologicalSpace B F E G
        (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
        (VectorBundle.rangeTotalSpaceTopology (F := G)
          (fun b => LinearMap.id - (β b).comp (ρ b)))) inferInstance
      (sumRangeHomeomorph (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal) y).proj = y.1 :=
  congrArg (fun z : TotalSpace F E × A => z.1.proj)
    (sumRangeHomeomorph_symm_apply_val (F := F) (G := G) (tE := tE)
      β ρ hρβ hβTotal hρTotal y)

/-- On a base and ambient vector, the inverse is the constructed retraction and range point. -/
theorem sumRangeHomeomorph_symm_apply_mk (b : B) (a : A) :
    (@Homeomorph.symm
      (TotalSpace (F × G)
        (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) (B × A)
      (@FiberBundle.Prod.topologicalSpace B F E G
        (fun b => (LinearMap.id - (β b).comp (ρ b)).range) tE
        (VectorBundle.rangeTotalSpaceTopology (F := G)
          (fun b => LinearMap.id - (β b).comp (ρ b)))) inferInstance
      (sumRangeHomeomorph (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal)) (b, a) =
      TotalSpace.mk' (F × G) b
        (ρ b a, ⟨((LinearMap.id : A →ₗ[R] A) - (β b).comp (ρ b)) a, ⟨a, rfl⟩⟩) := by
  let H := sumRangeHomeomorph (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal
  apply H.injective
  trans (b, a)
  · exact H.apply_symm_apply _
  · rw [sumRangeHomeomorph_apply]
    apply Prod.ext
    · rfl
    · change a = β b (ρ b a) + (a - β b (ρ b a))
      exact ((add_comm _ _).trans (sub_add_cancel _ _)).symm

/-- The forward fiber coordinate is the bundled coproduct of the given encoder and range
inclusion, hence is linear for the given scalar actions. -/
theorem sumRangeHomeomorph_fiber_eq_coprod (b : B) :
    (fun w : E b × (LinearMap.id - (β b).comp (ρ b)).range =>
      (sumRangeHomeomorph β ρ hρβ hβTotal hρTotal
        (TotalSpace.mk' (F × G) b w)).2) =
      (LinearMap.coprod (β b) (LinearMap.id - (β b).comp (ρ b)).range.subtype :
        E b × (LinearMap.id - (β b).comp (ρ b)).range → A) := by
  funext w
  simp only [sumRangeHomeomorph_apply, LinearMap.coprod_apply]
  rfl

end

end Bundle.TotalSpace
