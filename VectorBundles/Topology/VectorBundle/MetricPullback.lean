/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Pullback of Hermitian fiber metrics

`Bundle.HermitianMetric.pullback` reindexes a supplied compatible Hermitian metric along any
map `f : A → B`. It preserves the original fiber topologies, additive groups and modules over
`RCLike κ`. No base topology, model fiber, fiber-bundle or vector-bundle structure is required.

`Bundle.ContinuousHermitianMetric.pullback` reindexes a supplied continuous metric along a
continuous map. It accepts any `FunLike` type with a `ContinuousMapClass` instance, including
`C(A, B)`. The result retains the normed model `F` and the original fiber structures, using
Mathlib's pullback total-space topology, `FiberBundle.pullback f` and `VectorBundle.pullback f`.
The scalar field, bases, fibers, model and type of maps have independent universes.

The pairing laws give `(g.pullback f).inner a v w = g.inner (f a) v w`. Identity and composition
hold for pointwise metric data, and forgetting base continuity commutes with pullback.
No equality of continuous metric structures across different total-space topologies or
bundle atlases is asserted.

## Implementation notes

The pullback additive group is the original group on `E (f a)`. Its additive monoid agrees
by reflexivity with Mathlib's pullback additive monoid, including `nsmul`; the existing scalar
action and module structures are unchanged. Neither construction installs a norm or
inner-product instance on the fibers. When the fiber operations are continuous, the induced
metric norms give the original fiber topologies; they need not agree with the model norm in
bundle coordinates. No finite dimension, separation, compactness, nonemptiness or continuity
of an inverse base map is assumed.

For continuity, the local coefficient in the iterated semilinear Hom bundle is the original
metric's local coefficient composed with `f`. On the inverse image of a chart's base set,
the pulled-back fiber chart has the same inverse linear map as the original chart at the
image base point. The local section-continuity criterion then applies without identifying
the two Hom total-space topologies.

## References

* Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth and Floris van Doorn, the pullback
  constructions in `Mathlib.Topology.FiberBundle.Constructions` and
  `Mathlib.Topology.VectorBundle.Constructions`.
* Sébastien Gouëzel, `Mathlib.Topology.VectorBundle.Riemannian`, for compatible fiber metrics.
* Heather Macbeth and Floris van Doorn, `Mathlib.Topology.VectorBundle.Hom`, for the iterated
  semilinear Hom-bundle topology used by continuous Hermitian metrics.
-/

@[expose] public section

universe uκ uA uB uC uE uF uS

open Bundle

namespace Bundle

namespace Pullback

variable {A : Type uA} {B : Type uB} {E : B → Type uE}

/-- A pullback fiber has the additive group of the original fiber at the image base point. -/
instance instAddCommGroup [∀ b, AddCommGroup (E b)] (f : A → B) (a : A) :
    AddCommGroup ((f *ᵖ E) a) :=
  inferInstanceAs (AddCommGroup (E (f a)))

-- Mathlib's vector-bundle constructions select the same original additive monoid, module and
-- scalar action. Their explicit scalar-action instance avoids an `nsmul` diamond; taking the
-- original group here preserves that monoid, including its `nsmul`.
/-- The pullback group's additive monoid is the original fiber monoid, as in Mathlib's
pullback additive-monoid instance. -/
@[simp]
theorem instAddCommGroup_toAddCommMonoid [∀ b, AddCommGroup (E b)] (f : A → B) (a : A) :
    (instAddCommGroup (E := E) f a).toAddCommMonoid =
      inferInstanceAs (AddCommMonoid (E (f a))) := rfl

end Pullback

section Fiberwise

variable {κ : Type uκ} [RCLike κ]
  {A : Type uA} {B : Type uB} {C : Type uC} {E : B → Type uE}
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]

/-- Reindex a Hermitian metric along an arbitrary map of bases, preserving the original
fiber topologies and algebraic structures. No topology on either base is required. -/
noncomputable def HermitianMetric.pullback (g : HermitianMetric κ E) (f : A → B) :
    HermitianMetric κ (f *ᵖ E) := by
  exact
    { inner := fun a ↦ g.inner (f a)
      symm := fun a ↦ g.symm (f a)
      pos := fun a ↦ g.pos (f a)
      continuousAt := fun a ↦ g.continuousAt (f a)
      isVonNBounded := fun a ↦ g.isVonNBounded (f a) }

/-- The pulled-back pairing is the original pairing at the image base point. -/
@[simp]
theorem HermitianMetric.pullback_inner_apply (g : HermitianMetric κ E) (f : A → B)
    (a : A) (v w : E (f a)) :
    (g.pullback f).inner a v w = g.inner (f a) v w := by
  rfl

/-- Pulling back pointwise metric data along the identity leaves it unchanged. -/
@[simp]
theorem HermitianMetric.pullback_id (g : HermitianMetric κ E) :
    g.pullback (id : B → B) = g := by
  exact HermitianMetric.ext fun _ _ _ ↦ rfl

/-- Successive pullbacks of pointwise metric data agree with pullback along the composite. -/
@[simp]
theorem HermitianMetric.pullback_comp (g : HermitianMetric κ E) (f : A → B) (h : C → A) :
    (g.pullback f).pullback h = g.pullback (f ∘ h) := by
  exact HermitianMetric.ext fun _ _ _ ↦ rfl

end Fiberwise

section Continuous

variable {κ : Type uκ} [RCLike κ]
  {A : Type uA} [TopologicalSpace A] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]
  [FiberBundle F E] [VectorBundle κ F E]
  {S : Type uS} [FunLike S A B] [ContinuousMapClass S A B]

private theorem hermitian_trivializationAt_apply (b₀ b : B)
    (hb : b ∈ (trivializationAt F E b₀).baseSet)
    (L : E b →L⋆[κ] E b →L[κ] κ) (v w : F) :
    (trivializationAt (F →L⋆[κ] F →L[κ] κ)
      (fun b ↦ E b →L⋆[κ] E b →L[κ] κ) b₀
      (TotalSpace.mk' (F →L⋆[κ] F →L[κ] κ) b L)).2 v w =
        L ((trivializationAt F E b₀).symmL κ b v)
          ((trivializationAt F E b₀).symmL κ b w) := by
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem κ _
    (show b ∈ (trivializationAt (F →L[κ] κ) (fun b ↦ E b →L[κ] κ) b₀).baseSet by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hb, Set.mem_univ b⟩)]
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem κ _ (Set.mem_univ b)]
  rfl

/-- Pull back a supplied continuous Hermitian metric along a continuous map of bases.
The result uses the pullback total-space topology and the fiber- and vector-bundle structures
`FiberBundle.pullback f` and `VectorBundle.pullback f`. The model and original fiber structures
are unchanged. In particular, a bundled continuous map `f : C(A, B)` can be used. -/
noncomputable def ContinuousHermitianMetric.pullback (g : ContinuousHermitianMetric κ F E)
    (f : S) : ContinuousHermitianMetric κ F ((f : A → B) *ᵖ E) := by
  exact
    { inner := fun a ↦ g.inner (f a)
      symm := fun a ↦ g.symm (f a)
      pos := fun a ↦ g.pos (f a)
      isVonNBounded := fun a ↦ g.isVonNBounded (f a)
      continuous := by
        refine continuous_iff_continuousAt.mpr ?_
        intro a₀
        -- Apply the section criterion in the Hom bundle built over the pullback bundle.
        refine (FiberBundle.continuousAt_section (F →L⋆[κ] F →L[κ] κ)
          (E := fun a ↦ ((f : A → B) *ᵖ E) a →L⋆[κ] ((f : A → B) *ᵖ E) a →L[κ] κ)
          (s := fun a ↦ g.inner (f a)) a₀).mpr ?_
        have h := (FiberBundle.continuousAt_section (F →L⋆[κ] F →L[κ] κ)
          (E := fun b ↦ E b →L⋆[κ] E b →L[κ] κ) (s := g.inner) (f a₀)).mp
            g.continuous.continuousAt
        refine (h.comp (map_continuous f).continuousAt).congr_of_eventuallyEq ?_
        let e := trivializationAt F E (f a₀)
        have hbase := (map_continuous f).continuousAt (x := a₀)
          (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (f a₀)))
        filter_upwards [hbase] with a ha
        -- Only the chosen fiber charts are compared; the two Hom total-space topologies are not.
        have hsymm (v : F) :
            (trivializationAt F ((f : A → B) *ᵖ E) a₀).symmL κ a v =
              (trivializationAt F E (f a₀)).symmL κ (f a) v := by
          change (e.pullback f).symmL κ a v = e.symmL κ (f a) v
          have h₁ : (e.pullback f).symmL κ a v = (e.pullback f).symm a v :=
            (e.pullback f).symmL_apply ha v
          have h₂ : (e.pullback f).symm a v = e.symm (f a) v :=
            ((e.pullback f).symm_apply ha v).trans (by rfl)
          exact Eq.trans h₁ (Eq.trans h₂ (e.symmL_apply ha v).symm)
        refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
        have hpull := hermitian_trivializationAt_apply (κ := κ) (F := F)
          (E := ((f : A → B) *ᵖ E)) a₀ a ha (g.inner (f a)) v w
        have horig := hermitian_trivializationAt_apply (κ := κ) (F := F)
          (E := E) (f a₀) (f a) ha (g.inner (f a)) v w
        exact hpull.trans ((congrArg₂ (fun v' w' : E (f a) ↦ g.inner (f a) v' w')
          (hsymm v) (hsymm w)).trans horig.symm) }

/-- The continuous pullback metric has the original pairing at the image base point. -/
@[simp]
theorem ContinuousHermitianMetric.pullback_inner_apply (g : ContinuousHermitianMetric κ F E)
    (f : S) (a : A) (v w : E (f a)) :
    (g.pullback f).inner a v w = g.inner (f a) v w := by
  rfl

/-- Forgetting base continuity commutes with pullback of Hermitian metrics. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_pullback
    (g : ContinuousHermitianMetric κ F E) (f : S) :
    (g.pullback f).toHermitianMetric = g.toHermitianMetric.pullback (f : A → B) := by
  refine HermitianMetric.ext fun a v w ↦ ?_
  exact (ContinuousHermitianMetric.pullback_inner_apply g f a v w).trans
    (HermitianMetric.pullback_inner_apply g.toHermitianMetric (f : A → B) a v w).symm

end Continuous

end Bundle
