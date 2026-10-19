/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.LinearAlgebra.Prod

/-!
# Symmetry and associativity of fiberwise products

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
