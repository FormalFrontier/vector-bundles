/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.LinearAlgebra.Prod

/-!
# Homeomorphisms of fiberwise-product total spaces

The canonical swap and reassociation of fiberwise products are homeomorphisms of total spaces.
Both sides carry their existing product topologies, induced by the diagonal maps into products of
original total spaces. No topology on the base or model parameters, local triviality, or algebraic
structure on the fibers is needed for these homeomorphisms.

Their restrictions to a fiber agree with Mathlib's product linear equivalences whenever the fibers
are modules over a semiring. In particular, for vector bundles these are the symmetry and
associativity isomorphisms of Whitney sums, without any finite-dimensionality, completeness, or
separation hypothesis.

Pullback along any map distributes over the fiberwise product: the comparison preserves the
source base and both fiber coordinates. Its two total spaces carry, respectively, the canonical
pullback-of-product and product-of-pullbacks topologies. Only a topology on the source base and
the two original total-space topologies are needed. This is a total-space comparison, not a claim
of local triviality for arbitrary base maps or a bundled vector-bundle isomorphism.

A base-preserving homeomorphism of the right original total space induces a homeomorphism of
fiberwise-product total spaces. It fixes the complete first original total-space point in both
directions. The two sides use the stock product topologies formed from the same first topology
and the respective original right topologies; no topology or continuity of projections on the
base is needed. The construction restricts an ordinary product homeomorphism to equal-base pairs.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, November 2017, pp. 9–10,
  and the Whitney-sum pullback identity, printed p. 20 / PDF p. 24,
  https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf.
* Mathlib's `Mathlib.Topology.FiberBundle.Constructions` supplies the fiberwise product topology;
  `Mathlib.Topology.Constructions.SumProd` and `Mathlib.LinearAlgebra.Prod` supply ordinary product
  homeomorphisms and linear equivalences.
-/

@[expose] public section

open Bundle

universe uB uF₁ uF₂ uF₃ uE₁ uE₂ uE₃ uR

namespace FiberBundle.Prod

variable {B : Type uB}

/-- The canonical swap of a same-base fiberwise product, with the canonical product topology on
both total spaces. It sends `⟨b, (v₁, v₂)⟩` to `⟨b, (v₂, v₁)⟩`. -/
def homeomorphComm
    (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
    [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)] :
    @Homeomorph (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (TotalSpace (F₂ × F₁) (E₂ ×ᵇ E₁))
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
      (@FiberBundle.Prod.topologicalSpace B F₂ E₂ F₁ E₁ t₂ t₁) :=
  @Equiv.toHomeomorphOfIsInducing _ _
    (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
    (@FiberBundle.Prod.topologicalSpace B F₂ E₂ F₁ E₁ t₂ t₁)
    { toFun := fun p ↦ ⟨p.proj, (p.snd.2, p.snd.1)⟩
      invFun := fun p ↦ ⟨p.proj, (p.snd.2, p.snd.1)⟩
      left_inv := by rintro ⟨b, v₁, v₂⟩; rfl
      right_inv := by rintro ⟨b, v₂, v₁⟩; rfl }
    (by
      -- Compare through the inducing diagonal maps into the ordinary product.
      exact (isInducing_diag F₂ E₂ F₁ E₁).of_comp_iff.mp
        ((Homeomorph.prodComm (TotalSpace F₁ E₁) (TotalSpace F₂ E₂)).isInducing.comp
          (isInducing_diag F₁ E₁ F₂ E₂)))

section Comm

variable (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]

/-- The swap acts by exchanging the two fiber coordinates. -/
@[simp]
theorem homeomorphComm_apply (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    @homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂ p = ⟨p.proj, (p.snd.2, p.snd.1)⟩ := rfl

/-- The inverse swap exchanges the two fiber coordinates in the reverse direction. -/
@[simp]
theorem homeomorphComm_symm_apply (p : TotalSpace (F₂ × F₁) (E₂ ×ᵇ E₁)) :
    (@homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂).symm p =
      ⟨p.proj, (p.snd.2, p.snd.1)⟩ := rfl

/-- The swap preserves the base point. -/
@[simp]
theorem homeomorphComm_apply_proj (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    (@homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂ p).proj = p.proj := rfl

/-- The inverse swap preserves the base point. -/
@[simp]
theorem homeomorphComm_symm_apply_proj (p : TotalSpace (F₂ × F₁) (E₂ ×ᵇ E₁)) :
    ((@homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂).symm p).proj = p.proj := rfl

variable (R : Type uR) [Semiring R]
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module R (E₁ b)]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module R (E₂ b)]

/-- On each fiber, the swap is the standard product linear equivalence. -/
theorem homeomorphComm_apply_mk (b : B) (v : E₁ b × E₂ b) :
    @homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂ (TotalSpace.mk' (F₁ × F₂) b v) =
      TotalSpace.mk' (F₂ × F₁) b (LinearEquiv.prodComm R (E₁ b) (E₂ b) v) := rfl

/-- On each fiber, the inverse swap is the inverse product linear equivalence. -/
theorem homeomorphComm_symm_apply_mk (b : B) (v : E₂ b × E₁ b) :
    (@homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂).symm (TotalSpace.mk' (F₂ × F₁) b v) =
      TotalSpace.mk' (F₁ × F₂) b ((LinearEquiv.prodComm R (E₁ b) (E₂ b)).symm v) := rfl

end Comm

/-- The canonical reassociation of three same-base fiberwise products, with their canonical
iterated product topologies. It sends `⟨b, ((v₁, v₂), v₃)⟩` to `⟨b, (v₁, (v₂, v₃))⟩`. -/
def homeomorphAssoc
    (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
    (F₃ : Type uF₃) (E₃ : B → Type uE₃)
    [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]
    [t₃ : TopologicalSpace (TotalSpace F₃ E₃)] :
    @Homeomorph (TotalSpace ((F₁ × F₂) × F₃) ((E₁ ×ᵇ E₂) ×ᵇ E₃))
      (TotalSpace (F₁ × (F₂ × F₃)) (E₁ ×ᵇ (E₂ ×ᵇ E₃)))
      (@FiberBundle.Prod.topologicalSpace B (F₁ × F₂) (E₁ ×ᵇ E₂) F₃ E₃
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂) t₃)
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ (F₂ × F₃) (E₂ ×ᵇ E₃)
        t₁ (@FiberBundle.Prod.topologicalSpace B F₂ E₂ F₃ E₃ t₂ t₃)) :=
  @Equiv.toHomeomorphOfIsInducing _ _
    (@FiberBundle.Prod.topologicalSpace B (F₁ × F₂) (E₁ ×ᵇ E₂) F₃ E₃
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂) t₃)
    (@FiberBundle.Prod.topologicalSpace B F₁ E₁ (F₂ × F₃) (E₂ ×ᵇ E₃)
      t₁ (@FiberBundle.Prod.topologicalSpace B F₂ E₂ F₃ E₃ t₂ t₃))
    { toFun := fun p ↦ ⟨p.proj, (p.snd.1.1, (p.snd.1.2, p.snd.2))⟩
      invFun := fun p ↦ ⟨p.proj, ((p.snd.1, p.snd.2.1), p.snd.2.2)⟩
      left_inv := by rintro ⟨b, ⟨v₁, v₂⟩, v₃⟩; rfl
      right_inv := by rintro ⟨b, v₁, v₂, v₃⟩; rfl }
    (by
      -- Flatten both iterated diagonal maps into ordinary triple products.
      have hleft := ((isInducing_diag F₁ E₁ F₂ E₂).prodMap
        (Topology.IsInducing.id (X := TotalSpace F₃ E₃))).comp
          (isInducing_diag (F₁ × F₂) (E₁ ×ᵇ E₂) F₃ E₃)
      have hright := ((Topology.IsInducing.id (X := TotalSpace F₁ E₁)).prodMap
        (isInducing_diag F₂ E₂ F₃ E₃)).comp
          (isInducing_diag F₁ E₁ (F₂ × F₃) (E₂ ×ᵇ E₃))
      exact hright.of_comp_iff.mp
        ((Homeomorph.prodAssoc (TotalSpace F₁ E₁) (TotalSpace F₂ E₂)
          (TotalSpace F₃ E₃)).isInducing.comp hleft))

section Assoc

variable (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  (F₃ : Type uF₃) (E₃ : B → Type uE₃)
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]
  [t₃ : TopologicalSpace (TotalSpace F₃ E₃)]

/-- Reassociation groups the last two fiber coordinates together. -/
@[simp]
theorem homeomorphAssoc_apply (p : TotalSpace ((F₁ × F₂) × F₃) ((E₁ ×ᵇ E₂) ×ᵇ E₃)) :
    @homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ p =
      ⟨p.proj, (p.snd.1.1, (p.snd.1.2, p.snd.2))⟩ := rfl

/-- Inverse reassociation groups the first two fiber coordinates together. -/
@[simp]
theorem homeomorphAssoc_symm_apply (p : TotalSpace (F₁ × (F₂ × F₃)) (E₁ ×ᵇ (E₂ ×ᵇ E₃))) :
    (@homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃).symm p =
      ⟨p.proj, ((p.snd.1, p.snd.2.1), p.snd.2.2)⟩ := rfl

/-- Reassociation preserves the base point. -/
@[simp]
theorem homeomorphAssoc_apply_proj
    (p : TotalSpace ((F₁ × F₂) × F₃) ((E₁ ×ᵇ E₂) ×ᵇ E₃)) :
    (@homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ p).proj = p.proj := rfl

/-- Inverse reassociation preserves the base point. -/
@[simp]
theorem homeomorphAssoc_symm_apply_proj
    (p : TotalSpace (F₁ × (F₂ × F₃)) (E₁ ×ᵇ (E₂ ×ᵇ E₃))) :
    ((@homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃).symm p).proj = p.proj := rfl

variable (R : Type uR) [Semiring R]
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module R (E₁ b)]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module R (E₂ b)]
  [∀ b, AddCommMonoid (E₃ b)] [∀ b, Module R (E₃ b)]

/-- On each fiber, reassociation is the standard product linear equivalence. -/
theorem homeomorphAssoc_apply_mk (b : B) (v : (E₁ b × E₂ b) × E₃ b) :
    @homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃
      (TotalSpace.mk' ((F₁ × F₂) × F₃) b v) =
        TotalSpace.mk' (F₁ × (F₂ × F₃)) b
          (LinearEquiv.prodAssoc R (E₁ b) (E₂ b) (E₃ b) v) := rfl

/-- On each fiber, inverse reassociation is the inverse product linear equivalence. -/
theorem homeomorphAssoc_symm_apply_mk (b : B) (v : E₁ b × (E₂ b × E₃ b)) :
    (@homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃).symm
      (TotalSpace.mk' (F₁ × (F₂ × F₃)) b v) =
        TotalSpace.mk' ((F₁ × F₂) × F₃) b
          ((LinearEquiv.prodAssoc R (E₁ b) (E₂ b) (E₃ b)).symm v) := rfl

end Assoc

end FiberBundle.Prod


namespace FiberBundle.Prod

universe uA

section Pullback

variable {A : Type uA} {B : Type uB}
  (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  (f : A → B)
  [tA : TopologicalSpace A]
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]

/-- Pullback distributes over a fiberwise product with its canonical total-space topologies.

Both directions send `⟨a, (v₁, v₂)⟩` to `⟨a, (v₁, v₂)⟩`. Only the source base and the two
original total spaces need topologies; no continuity of the base map or original projections is
required. This is the total-space comparison underlying the Whitney-sum pullback identity in
Hatcher, printed p. 20 / PDF p. 24. -/
def homeomorphPullback :
    @Homeomorph (TotalSpace (F₁ × F₂) (f *ᵖ (E₁ ×ᵇ E₂)))
      (TotalSpace (F₁ × F₂) ((f *ᵖ E₁) ×ᵇ (f *ᵖ E₂)))
      (@pullbackTopology B (F₁ × F₂) (E₁ ×ᵇ E₂) A f tA
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂))
      (@FiberBundle.Prod.topologicalSpace A F₁ (f *ᵖ E₁) F₂ (f *ᵖ E₂)
        (@pullbackTopology B F₁ E₁ A f tA t₁)
        (@pullbackTopology B F₂ E₂ A f tA t₂)) :=
  @Equiv.toHomeomorphOfIsInducing _ _
    (@pullbackTopology B (F₁ × F₂) (E₁ ×ᵇ E₂) A f tA
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂))
    (@FiberBundle.Prod.topologicalSpace A F₁ (f *ᵖ E₁) F₂ (f *ᵖ E₂)
      (@pullbackTopology B F₁ E₁ A f tA t₁)
      (@pullbackTopology B F₂ E₂ A f tA t₂))
    (Equiv.refl _)
    (by
      constructor
      -- Both initial topologies record the source base and the two original total-space
      -- coordinates; the product of pullbacks records the same base coordinate twice.
      simp only [FiberBundle.Prod.topologicalSpace, pullbackTopology_def,
        instTopologicalSpaceProd, _root_.induced_inf, _root_.induced_compose,
        Function.comp_def, Bundle.Pullback.lift]
      exact inf_inf_distrib_left _ _ _)

/-- The comparison leaves the base and fiber coordinates unchanged. -/
@[simp]
theorem homeomorphPullback_apply (z : TotalSpace (F₁ × F₂) (f *ᵖ (E₁ ×ᵇ E₂))) :
    homeomorphPullback F₁ E₁ F₂ E₂ f z = TotalSpace.mk' (F₁ × F₂) z.proj z.snd := rfl

/-- The inverse comparison leaves the base and fiber coordinates unchanged. -/
@[simp]
theorem homeomorphPullback_symm_apply
    (z : TotalSpace (F₁ × F₂) ((f *ᵖ E₁) ×ᵇ (f *ᵖ E₂))) :
    (homeomorphPullback F₁ E₁ F₂ E₂ f).symm z =
      TotalSpace.mk' (F₁ × F₂) z.proj z.snd := rfl

/-- The comparison preserves the source base point. -/
@[simp]
theorem homeomorphPullback_apply_proj
    (z : TotalSpace (F₁ × F₂) (f *ᵖ (E₁ ×ᵇ E₂))) :
    (homeomorphPullback F₁ E₁ F₂ E₂ f z).proj = z.proj := rfl

/-- The inverse comparison preserves the source base point. -/
@[simp]
theorem homeomorphPullback_symm_apply_proj
    (z : TotalSpace (F₁ × F₂) ((f *ᵖ E₁) ×ᵇ (f *ᵖ E₂))) :
    ((homeomorphPullback F₁ E₁ F₂ E₂ f).symm z).proj = z.proj := rfl

/-- Lifting the two pulled-back components gives the original product diagonal of the lift. -/
theorem lift_pair_homeomorphPullback
    (z : TotalSpace (F₁ × F₂) (f *ᵖ (E₁ ×ᵇ E₂))) :
    (@Bundle.Pullback.lift B F₁ E₁ A f
        (TotalSpace.mk' F₁ (homeomorphPullback F₁ E₁ F₂ E₂ f z).proj
          (homeomorphPullback F₁ E₁ F₂ E₂ f z).snd.1),
      @Bundle.Pullback.lift B F₂ E₂ A f
        (TotalSpace.mk' F₂ (homeomorphPullback F₁ E₁ F₂ E₂ f z).proj
          (homeomorphPullback F₁ E₁ F₂ E₂ f z).snd.2)) =
      (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
        (TotalSpace.mk' F₁ p.proj p.snd.1, TotalSpace.mk' F₂ p.proj p.snd.2))
        (Bundle.Pullback.lift f z) := rfl

variable (R : Type uR) [Semiring R]
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module R (E₁ b)]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module R (E₂ b)]

/-- On each fiber, the comparison is the standard identity linear equivalence. -/
theorem homeomorphPullback_apply_mk (a : A) (v : E₁ (f a) × E₂ (f a)) :
    homeomorphPullback F₁ E₁ F₂ E₂ f (TotalSpace.mk' (F₁ × F₂) a v) =
      TotalSpace.mk' (F₁ × F₂) a (LinearEquiv.refl R (E₁ (f a) × E₂ (f a)) v) := rfl

/-- On each fiber, the inverse comparison is the standard identity linear equivalence. -/
theorem homeomorphPullback_symm_apply_mk (a : A) (v : E₁ (f a) × E₂ (f a)) :
    (homeomorphPullback F₁ E₁ F₂ E₂ f).symm (TotalSpace.mk' (F₁ × F₂) a v) =
      TotalSpace.mk' (F₁ × F₂) a (LinearEquiv.refl R (E₁ (f a) × E₂ (f a)) v) := rfl

end Pullback

end FiberBundle.Prod


namespace FiberBundle.Prod

section EqualBase

variable {B : Type uB}
  (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]

/-- The total space of a fiberwise product is homeomorphic to the pairs of original total-space
points with equal base projections.

The source carries `FiberBundle.Prod.topologicalSpace`, and the target carries the product and
subtype topologies. The inverse retains the first base and first fiber coordinate, transporting
only the second fiber coordinate along the reversed equality of base projections. No topology
on the base or model parameters, local triviality, or algebraic structure is required. -/
def homeomorphEqualBase :
    @Homeomorph (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂) inferInstance :=
  @Equiv.toHomeomorphOfIsInducing _ _
    (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂) inferInstance
    { toFun := fun p ↦ ⟨(⟨p.proj, p.snd.1⟩, ⟨p.proj, p.snd.2⟩), rfl⟩
      invFun := fun w ↦ ⟨w.1.1.proj,
        (w.1.1.snd, cast (congrArg E₂ w.property.symm) w.1.2.snd)⟩
      left_inv := by rintro ⟨b, e, h⟩; rfl
      right_inv := by
        rintro ⟨⟨⟨b, e⟩, ⟨c, h⟩⟩, q⟩
        apply Subtype.ext
        exact Prod.ext rfl (TotalSpace.mk_cast (F := F₂) q.symm h) }
    (by
      -- Forgetting the equal-base witness gives exactly the stock inducing diagonal.
      exact (Topology.IsInducing.subtypeVal (t :=
        {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ | w.1.proj = w.2.proj})).of_comp_iff.mp
          (isInducing_diag F₁ E₁ F₂ E₂))

/-- The comparison pairs the two original total-space points over the same base. -/
@[simp]
theorem homeomorphEqualBase_apply (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    homeomorphEqualBase F₁ E₁ F₂ E₂ p =
      ⟨(TotalSpace.mk' F₁ p.proj p.snd.1, TotalSpace.mk' F₂ p.proj p.snd.2), rfl⟩ := rfl

/-- The inverse keeps the first base and transports the second fiber coordinate to that base. -/
@[simp]
theorem homeomorphEqualBase_symm_apply
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    (homeomorphEqualBase F₁ E₁ F₂ E₂).symm w =
      TotalSpace.mk' (F₁ × F₂) w.1.1.proj
        (w.1.1.snd, cast (congrArg E₂ w.property.symm) w.1.2.snd) := rfl

/-- On a constructed product point, the comparison preserves both fiber values. -/
theorem homeomorphEqualBase_apply_mk (b : B) (e : E₁ b) (h : E₂ b) :
    homeomorphEqualBase F₁ E₁ F₂ E₂ (TotalSpace.mk' (F₁ × F₂) b (e, h)) =
      ⟨(TotalSpace.mk' F₁ b e, TotalSpace.mk' F₂ b h), rfl⟩ := rfl

/-- For an arbitrary equality of bases, the inverse transports only the second fiber value.
When the bases and equality witness are reflexive, the cast reduces to the original value. -/
theorem homeomorphEqualBase_symm_apply_mk {b c : B} (e : E₁ b) (h : E₂ c) (q : b = c) :
    (homeomorphEqualBase F₁ E₁ F₂ E₂).symm
      ⟨(TotalSpace.mk' F₁ b e, TotalSpace.mk' F₂ c h), q⟩ =
        TotalSpace.mk' (F₁ × F₂) b (e, cast (congrArg E₂ q.symm) h) := rfl

/-- The inverse uses the base projection of the first total-space point. -/
@[simp]
theorem homeomorphEqualBase_symm_apply_proj
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).proj = w.1.1.proj := rfl

/-- The inverse leaves the first fiber coordinate unchanged. -/
@[simp]
theorem homeomorphEqualBase_symm_apply_fst
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).snd.1 = w.1.1.snd := rfl

/-- The second fiber coordinate of the inverse is transported along the reversed base equality. -/
@[simp]
theorem homeomorphEqualBase_symm_apply_snd
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).snd.2 =
      cast (congrArg E₂ w.property.symm) w.1.2.snd := rfl

/-- Reconstructing the first total-space point from the inverse recovers the original point. -/
theorem homeomorphEqualBase_mk_fst_symm_apply
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    TotalSpace.mk' F₁ ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).proj
      ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).snd.1 = w.1.1 := rfl

/-- Reconstructing the second total-space point from the inverse recovers the original point,
including its original base projection. -/
theorem homeomorphEqualBase_mk_snd_symm_apply
    (w : {w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ // w.1.proj = w.2.proj}) :
    TotalSpace.mk' F₂ ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).proj
      ((homeomorphEqualBase F₁ E₁ F₂ E₂).symm w).snd.2 = w.1.2 := by
  exact TotalSpace.mk_cast (F := F₂) w.property.symm w.1.2.snd

end EqualBase

end FiberBundle.Prod


namespace FiberBundle.Prod

section TotalSpaceFactors

variable {B : Type uB}
  (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)

/-- The first original total-space point of a fiberwise-product total-space point. -/
def totalSpaceFst (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) : TotalSpace F₁ E₁ :=
  ⟨p.proj, p.snd.1⟩

/-- The second original total-space point of a fiberwise-product total-space point. -/
def totalSpaceSnd (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) : TotalSpace F₂ E₂ :=
  ⟨p.proj, p.snd.2⟩

/-- The first total-space factor retains the base and first fiber value. -/
@[simp]
theorem totalSpaceFst_mk (b : B) (e₁ : E₁ b) (e₂ : E₂ b) :
    totalSpaceFst F₁ E₁ F₂ E₂ (TotalSpace.mk' (F₁ × F₂) b (e₁, e₂)) =
      TotalSpace.mk' F₁ b e₁ := rfl

/-- The second total-space factor retains the base and second fiber value. -/
@[simp]
theorem totalSpaceSnd_mk (b : B) (e₁ : E₁ b) (e₂ : E₂ b) :
    totalSpaceSnd F₁ E₁ F₂ E₂ (TotalSpace.mk' (F₁ × F₂) b (e₁, e₂)) =
      TotalSpace.mk' F₂ b e₂ := rfl

/-- The two original total-space factors jointly determine a fiberwise-product point. -/
theorem totalSpace_ext {p q : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
    (h₁ : totalSpaceFst F₁ E₁ F₂ E₂ p = totalSpaceFst F₁ E₁ F₂ E₂ q)
    (h₂ : totalSpaceSnd F₁ E₁ F₂ E₂ p = totalSpaceSnd F₁ E₁ F₂ E₂ q) : p = q := by
  rcases p with ⟨b, e₁, e₂⟩
  rcases q with ⟨c, f₁, f₂⟩
  have hbase : b = c := congrArg TotalSpace.proj h₁
  cases hbase
  have hfirst : e₁ = f₁ := by injection h₁
  have hsecond : e₂ = f₂ := by injection h₂
  cases hfirst
  cases hsecond
  rfl

end TotalSpaceFactors

end FiberBundle.Prod


namespace FiberBundle.Prod

section CongrRight

variable {B : Type uB}
  (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  (F₃ : Type uF₃) (E₃ : B → Type uE₃)
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]
  [t₃ : TopologicalSpace (TotalSpace F₃ E₃)]
  (H : @Homeomorph (TotalSpace F₂ E₂) (TotalSpace F₃ E₃) t₂ t₃)
  (hH : ∀ s, (H s).proj = s.proj)

include hH in
private theorem symm_proj_of_proj (t : TotalSpace F₃ E₃) :
    (@Homeomorph.symm _ _ t₂ t₃ H t).proj = t.proj := by
  simpa only [Homeomorph.apply_symm_apply] using
    (hH (@Homeomorph.symm _ _ t₂ t₃ H t)).symm

/-- A base-preserving homeomorphism of the right original total space induces a homeomorphism
of fiberwise-product total spaces, fixing the first original total-space point.

The source and target carry the stock product topologies formed from the same original first
topology and the respective original right topologies. No topology on the base or model tags,
continuity of the projections, local triviality, or algebraic structure is required. -/
def homeomorphCongrRight :
    @Homeomorph (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃))
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₃ E₃ t₁ t₃) :=
  let hProd : @Homeomorph
      (TotalSpace F₁ E₁ × TotalSpace F₂ E₂) (TotalSpace F₁ E₁ × TotalSpace F₃ E₃)
      (@instTopologicalSpaceProd _ _ t₁ t₂) (@instTopologicalSpaceProd _ _ t₁ t₃) :=
    @Homeomorph.prodCongr (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) t₁ t₂
      (TotalSpace F₁ E₁) (TotalSpace F₃ E₃) t₁ t₃
      (@Homeomorph.refl (TotalSpace F₁ E₁) t₁) H
  (@homeomorphEqualBase B F₁ E₁ F₂ E₂ t₁ t₂).trans
    ((hProd.subtype
      (p := fun w : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ ↦ w.1.proj = w.2.proj)
      (q := fun w : TotalSpace F₁ E₁ × TotalSpace F₃ E₃ ↦ w.1.proj = w.2.proj)
      (by
        intro w
        change w.1.proj = w.2.proj ↔ w.1.proj = (H w.2).proj
        rw [hH w.2])).trans
      (@Homeomorph.symm _ _ _ _ (@homeomorphEqualBase B F₁ E₁ F₃ E₃ t₁ t₃)))

/-- The induced homeomorphism fixes the complete first original total-space point. -/
@[simp]
theorem totalSpaceFst_homeomorphCongrRight (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    totalSpaceFst F₁ E₁ F₃ E₃
      (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p) =
        totalSpaceFst F₁ E₁ F₂ E₂ p := by
  exact @homeomorphEqualBase_mk_fst_symm_apply B F₁ E₁ F₃ E₃ t₁ t₃
    ⟨(totalSpaceFst F₁ E₁ F₂ E₂ p, H (totalSpaceSnd F₁ E₁ F₂ E₂ p)),
      (hH (totalSpaceSnd F₁ E₁ F₂ E₂ p)).symm⟩

/-- The second original total-space factor is transformed by the given homeomorphism. -/
@[simp]
theorem totalSpaceSnd_homeomorphCongrRight (p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    totalSpaceSnd F₁ E₁ F₃ E₃
      (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p) =
        H (totalSpaceSnd F₁ E₁ F₂ E₂ p) := by
  exact @homeomorphEqualBase_mk_snd_symm_apply B F₁ E₁ F₃ E₃ t₁ t₃
    ⟨(totalSpaceFst F₁ E₁ F₂ E₂ p, H (totalSpaceSnd F₁ E₁ F₂ E₂ p)),
      (hH (totalSpaceSnd F₁ E₁ F₂ E₂ p)).symm⟩

/-- The inverse induced homeomorphism fixes the complete first original total-space point. -/
@[simp]
theorem totalSpaceFst_homeomorphCongrRight_symm
    (p : TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃)) :
    totalSpaceFst F₁ E₁ F₂ E₂
      (@Homeomorph.symm _ _
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₃ E₃ t₁ t₃)
        (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH) p) =
          totalSpaceFst F₁ E₁ F₃ E₃ p := by
  exact @homeomorphEqualBase_mk_fst_symm_apply B F₁ E₁ F₂ E₂ t₁ t₂
    ⟨(totalSpaceFst F₁ E₁ F₃ E₃ p,
      @Homeomorph.symm _ _ t₂ t₃ H (totalSpaceSnd F₁ E₁ F₃ E₃ p)),
      (@symm_proj_of_proj B F₂ E₂ F₃ E₃ t₂ t₃ H hH (totalSpaceSnd F₁ E₁ F₃ E₃ p)).symm⟩

/-- The inverse second total-space factor is transformed by the original inverse homeomorphism. -/
@[simp]
theorem totalSpaceSnd_homeomorphCongrRight_symm
    (p : TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃)) :
    totalSpaceSnd F₁ E₁ F₂ E₂
      (@Homeomorph.symm _ _
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
        (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₃ E₃ t₁ t₃)
        (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH) p) =
          @Homeomorph.symm _ _ t₂ t₃ H (totalSpaceSnd F₁ E₁ F₃ E₃ p) := by
  exact @homeomorphEqualBase_mk_snd_symm_apply B F₁ E₁ F₂ E₂ t₁ t₂
    ⟨(totalSpaceFst F₁ E₁ F₃ E₃ p,
      @Homeomorph.symm _ _ t₂ t₃ H (totalSpaceSnd F₁ E₁ F₃ E₃ p)),
      (@symm_proj_of_proj B F₂ E₂ F₃ E₃ t₂ t₃ H hH (totalSpaceSnd F₁ E₁ F₃ E₃ p)).symm⟩

end CongrRight

end FiberBundle.Prod


namespace FiberBundle.Prod

section CongrRightLaws

variable {B : Type uB}
  (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
  (F₃ : Type uF₃) (E₃ : B → Type uE₃)
  [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]
  [t₃ : TopologicalSpace (TotalSpace F₃ E₃)]

/-- The two forward total-space factor laws uniquely characterize the right-factor
homeomorphism. -/
theorem homeomorphCongrRight_unique
    (H : @Homeomorph (TotalSpace F₂ E₂) (TotalSpace F₃ E₃) t₂ t₃)
    (hH : ∀ s, (H s).proj = s.proj)
    (J : @Homeomorph (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (TotalSpace (F₁ × F₃) (E₁ ×ᵇ E₃))
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂)
      (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₃ E₃ t₁ t₃))
    (hfst : ∀ p, totalSpaceFst F₁ E₁ F₃ E₃ (J p) = totalSpaceFst F₁ E₁ F₂ E₂ p)
    (hsnd : ∀ p, totalSpaceSnd F₁ E₁ F₃ E₃ (J p) = H (totalSpaceSnd F₁ E₁ F₂ E₂ p)) :
    J = @homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH := by
  apply Homeomorph.ext
  intro p
  apply totalSpace_ext F₁ E₁ F₃ E₃
  · exact (hfst p).trans
      (@totalSpaceFst_homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p).symm
  · exact (hsnd p).trans
      (@totalSpaceSnd_homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p).symm

/-- Applying the identity to the right original total space gives the identity on the
fiberwise-product total space. -/
@[simp]
theorem homeomorphCongrRight_refl :
    @homeomorphCongrRight B F₁ E₁ F₂ E₂ F₂ E₂ t₁ t₂ t₂
      (@Homeomorph.refl (TotalSpace F₂ E₂) t₂) (fun _ ↦ rfl) =
        @Homeomorph.refl (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
          (@FiberBundle.Prod.topologicalSpace B F₁ E₁ F₂ E₂ t₁ t₂) := by
  symm
  apply @homeomorphCongrRight_unique B F₁ E₁ F₂ E₂ F₂ E₂ t₁ t₂ t₂
    (@Homeomorph.refl (TotalSpace F₂ E₂) t₂) (fun _ ↦ rfl)
  · intro p; rfl
  · intro p; rfl

universe uF₄ uE₄

variable (F₄ : Type uF₄) (E₄ : B → Type uE₄)
  [t₄ : TopologicalSpace (TotalSpace F₄ E₄)]

/-- Right-factor homeomorphisms respect composition, with the same original middle
total-space topology used by both given homeomorphisms. -/
theorem homeomorphCongrRight_trans
    (H : @Homeomorph (TotalSpace F₂ E₂) (TotalSpace F₃ E₃) t₂ t₃)
    (hH : ∀ s, (H s).proj = s.proj)
    (K : @Homeomorph (TotalSpace F₃ E₃) (TotalSpace F₄ E₄) t₃ t₄)
    (hK : ∀ t, (K t).proj = t.proj) :
    (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH).trans
      (@homeomorphCongrRight B F₁ E₁ F₃ E₃ F₄ E₄ t₁ t₃ t₄ K hK) =
        @homeomorphCongrRight B F₁ E₁ F₂ E₂ F₄ E₄ t₁ t₂ t₄ (H.trans K)
          (fun s ↦ (hK (H s)).trans (hH s)) := by
  apply @homeomorphCongrRight_unique B F₁ E₁ F₂ E₂ F₄ E₄ t₁ t₂ t₄ (H.trans K)
    (fun s ↦ (hK (H s)).trans (hH s))
  · intro p
    exact (@totalSpaceFst_homeomorphCongrRight B F₁ E₁ F₃ E₃ F₄ E₄ t₁ t₃ t₄ K hK
      (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p)).trans
        (@totalSpaceFst_homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p)
  · intro p
    exact (@totalSpaceSnd_homeomorphCongrRight B F₁ E₁ F₃ E₃ F₄ E₄ t₁ t₃ t₄ K hK
      (@homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p)).trans
        (congrArg K
          (@totalSpaceSnd_homeomorphCongrRight B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃ H hH p))

end CongrRightLaws

end FiberBundle.Prod
