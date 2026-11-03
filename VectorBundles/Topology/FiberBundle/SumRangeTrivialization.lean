/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.SumRange
public import VectorBundles.Topology.VectorBundle.FiniteRank
public import VectorBundles.Topology.FiberBundle.Trivialization.CompHomeomorph

/-!
# Full-base sum–range trivializations

A family of split linear injections into a topological additive group gives a canonical
trivialization on the fiberwise product of the original family with its complementary
ranges. The chart model is the ambient group, independently of the total-space parameter.
Its underlying open partial homeomorphism is `Bundle.TotalSpace.sumRangeHomeomorph`, so both
the sum coordinates and their inverse are fixed.

The complementary range carries `VectorBundle.rangeTotalSpaceTopology`. The domain carries
`FiberBundle.Prod.topologicalSpace`, formed from that topology and the given topology on the
original total space. No original bundle structure or topology on the scalar semiring is
required. Fiberwise linearity uses the given module actions and the public coproduct
identity for the sum–range homeomorphism.

## Implementation notes

The construction precomposes Mathlib's trivial-bundle chart with the sum–range homeomorphism
and the inverse of `Bundle.Trivial.homeomorphProd`. Only equality of the projection functions
is transported; the domain and its topology remain unchanged.

## References

* Mathlib's `Bundle.Trivial.trivialization` and `Bundle.Trivialization.compHomeomorph`.
* `Bundle.TotalSpace.sumRangeHomeomorph` and its coproduct identity.
-/

@[expose] public section

universe uR uB uA uE uF uG

open Bundle Topology

namespace Bundle.TotalSpace

variable {R : Type uR} [Semiring R]
variable {B : Type uB} [TopologicalSpace B]
variable {A : Type uA} [AddCommGroup A] [Module R A]
variable [TopologicalSpace A] [IsTopologicalAddGroup A]
variable {E : B → Type uE}
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
variable {F : Type uF} {G : Type uG}
variable [tE : TopologicalSpace (TotalSpace F E)]

variable (β : ∀ b, E b →ₗ[R] A) (ρ : ∀ b, A →ₗ[R] E b)

-- This notation expands to the fixed topology, without introducing a declaration.
local notation "τ" =>
  @FiberBundle.Prod.topologicalSpace B F E G
    (fun b => LinearMap.range (LinearMap.id - LinearMap.comp (β b) (ρ b))) tE
    (VectorBundle.rangeTotalSpaceTopology (F := G)
      (fun b => LinearMap.id - LinearMap.comp (β b) (ρ b)))

-- Public signatures synthesize the same canonical range topology and its product with tE.
attribute [local instance] VectorBundle.rangeTotalSpaceTopology

/-- The full-base sum–range chart on the original fiberwise-product total space.
The model is the ambient module, and both total-space parameters are independent of it. -/
noncomputable def sumRangeTrivialization
    (hρβ : ∀ b e, ρ b (β b e) = e)
    (hβTotal : Continuous
      (fun t : TotalSpace F E => (t.proj, β t.proj t.snd)))
    (hρTotal : Continuous
      (fun y : B × A => TotalSpace.mk' F y.1 (ρ y.1 y.2))) :
    @Trivialization B A
      (TotalSpace (F × G)
        (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range))
      inferInstance inferInstance
      τ
      TotalSpace.proj := by
  letI := τ
  let H := sumRangeHomeomorph (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal
  let h := H.trans (Bundle.Trivial.homeomorphProd B A).symm
  have hproj :
      (TotalSpace.proj : TotalSpace A (Bundle.Trivial B A) → B) ∘ h =
        (TotalSpace.proj : TotalSpace (F × G)
          (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range) → B) := by
    funext c
    exact sumRangeHomeomorph_apply_fst (F := F) (G := G) (tE := tE)
      β ρ hρβ hβTotal hρTotal c
  exact hproj ▸ (Bundle.Trivial.trivialization B A).compHomeomorph h

variable (hρβ : ∀ b e, ρ b (β b e) = e)
variable (hβTotal : Continuous
  (fun t : TotalSpace F E => (t.proj, β t.proj t.snd)))
variable (hρTotal : Continuous
  (fun y : B × A => TotalSpace.mk' F y.1 (ρ y.1 y.2)))

local notation "T" => sumRangeTrivialization
  (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal
local notation "H" => sumRangeHomeomorph
  (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal

/-- The chart agrees with the canonical sum–range homeomorphism as an open partial
homeomorphism, including its inverse, source and target. -/
theorem sumRangeTrivialization_toOpenPartialHomeomorph :
    (T).toOpenPartialHomeomorph = (H).toOpenPartialHomeomorph := by
  let := τ
  let h := (H).trans (Bundle.Trivial.homeomorphProd B A).symm
  have hproj :
      (TotalSpace.proj : TotalSpace A (Bundle.Trivial B A) → B) ∘ h =
        (TotalSpace.proj : TotalSpace (F × G)
          (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range) → B) := by
    funext c
    exact sumRangeHomeomorph_apply_fst (F := F) (G := G) (tE := tE)
      β ρ hρβ hβTotal hρTotal c
  -- The projection is a parameter of a trivialization, not of its underlying map.
  have htransport
      (p q : TotalSpace (F × G)
        (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range) → B)
      (hp : p = q) (e : Trivialization A p) :
      (hp ▸ e).toOpenPartialHomeomorph = e.toOpenPartialHomeomorph := by
    cases hp
    rfl
  change
    (hproj ▸ (Bundle.Trivial.trivialization B A).compHomeomorph h).toOpenPartialHomeomorph =
      (H).toOpenPartialHomeomorph
  rw [htransport]
  apply OpenPartialHomeomorph.ext
  · intro c
    change ((Bundle.Trivial.trivialization B A).compHomeomorph h) c = H c
    rw [Bundle.Trivialization.compHomeomorph_apply]
    change (Bundle.Trivial.homeomorphProd B A)
      ((Bundle.Trivial.homeomorphProd B A).symm (H c)) = H c
    exact (Bundle.Trivial.homeomorphProd B A).apply_symm_apply (H c)
  · intro y
    rw [Bundle.Trivialization.toOpenPartialHomeomorph_compHomeomorph_symm_apply,
      Bundle.Trivial.toOpenPartialHomeomorph_trivialization_symm_apply]
    rfl
  · change ((Bundle.Trivial.trivialization B A).compHomeomorph h).source = Set.univ
    rw [Bundle.Trivialization.source_eq, Bundle.Trivialization.compHomeomorph_baseSet]
    rfl

/-- Every base point belongs to the sum–range chart. -/
@[simp] theorem sumRangeTrivialization_baseSet :
    (T).baseSet = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  apply ((T).mem_target (x := (b, (0 : A)))).mp
  change (b, (0 : A)) ∈ (T).toOpenPartialHomeomorph.target
  rw [sumRangeTrivialization_toOpenPartialHomeomorph]
  exact Set.mem_univ _

/-- The chart retains the base point and adds the encoded and complementary vectors. -/
@[simp] theorem sumRangeTrivialization_apply
    (c : TotalSpace (F × G)
      (fun b => E b × (LinearMap.id - (β b).comp (ρ b)).range)) :
    T c = (c.proj, β c.proj c.snd.1 + (c.snd.2 : A)) := by
  change (T).toOpenPartialHomeomorph c = _
  rw [sumRangeTrivialization_toOpenPartialHomeomorph]
  exact sumRangeHomeomorph_apply β ρ hρβ hβTotal hρTotal c

/-- The underlying chart inverse recovers the original retraction total-space point and
the complementary ambient vector; this is not the zero-extended fiber inverse. -/
@[simp] theorem toOpenPartialHomeomorph_sumRangeTrivialization_symm_apply_val (y : B × A) :
    let c := (T).toOpenPartialHomeomorph.symm y
    ((TotalSpace.mk' F c.proj c.snd.1 : TotalSpace F E), (c.snd.2 : A)) =
      ((TotalSpace.mk' F y.1 (ρ y.1 y.2) : TotalSpace F E),
        ((LinearMap.id : A →ₗ[R] A) - (β y.1).comp (ρ y.1)) y.2) := by
  rw [sumRangeTrivialization_toOpenPartialHomeomorph]
  exact sumRangeHomeomorph_symm_apply_val (F := F) (G := G) (tE := tE)
    β ρ hρβ hβTotal hρTotal y

/-- The sum–range chart is fiberwise linear for the original module actions. -/
theorem sumRangeTrivialization_isFiberwiseLinear :
    (T).IsFiberwiseLinear (K := R) := by
  have hfiber (b : B) :
      (fun w : E b × (LinearMap.id - (β b).comp (ρ b)).range =>
        (T (TotalSpace.mk' (F × G) b w)).2) =
      (LinearMap.coprod (β b) (LinearMap.id - (β b).comp (ρ b)).range.subtype :
        E b × (LinearMap.id - (β b).comp (ρ b)).range → A) := by
    change (fun w : E b × (LinearMap.id - (β b).comp (ρ b)).range =>
      ((T).toOpenPartialHomeomorph (TotalSpace.mk' (F × G) b w)).2) = _
    rw [sumRangeTrivialization_toOpenPartialHomeomorph]
    exact sumRangeHomeomorph_fiber_eq_coprod β ρ hρβ hβTotal hρTotal b
  have hcoord (b : B) (w : E b × (LinearMap.id - (β b).comp (ρ b)).range) :
      (T (TotalSpace.mk' (F × G) b w)).2 =
        LinearMap.coprod (β b) (LinearMap.id - (β b).comp (ρ b)).range.subtype w :=
    congrFun (hfiber b) w
  constructor
  · intro b _ v w
    rw [hcoord b (v + w), hcoord b v, hcoord b w]
    exact (LinearMap.coprod (β b)
      (LinearMap.id - (β b).comp (ρ b)).range.subtype).map_add v w
  · intro b _ r v
    rw [hcoord b (r • v), hcoord b v]
    exact (LinearMap.coprod (β b)
      (LinearMap.id - (β b).comp (ρ b)).range.subtype).map_smul r v

/-- The chart's bundled fiber map is the coproduct of the encoder and range inclusion. -/
theorem sumRangeTrivialization_linearMap (b : B) (hb : b ∈ (T).baseSet) :
    (sumRangeTrivialization_isFiberwiseLinear
      (F := F) (G := G) (tE := tE) β ρ hρβ hβTotal hρTotal).linearMap hb =
      LinearMap.coprod (β b)
        (LinearMap.id - (β b).comp (ρ b)).range.subtype := by
  apply LinearMap.ext
  intro w
  rw [Bundle.Trivialization.IsFiberwiseLinear.linearMap_apply]
  change ((T).toOpenPartialHomeomorph (TotalSpace.mk' (F × G) b w)).2 = _
  rw [sumRangeTrivialization_toOpenPartialHomeomorph]
  exact congrFun (sumRangeHomeomorph_fiber_eq_coprod β ρ hρβ hβTotal hρTotal b) w

end Bundle.TotalSpace
