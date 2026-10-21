/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Pullback total spaces and their universal maps

The total space of `f *ᵖ E` is canonically homeomorphic to the subspace of
`A × Bundle.TotalSpace F E` consisting of pairs whose images in `B` agree.
Compatible continuous maps to `A` and the original total space therefore determine
a unique continuous map to the pullback total space. For a constant base map, an
inducing inclusion of the original fiber identifies the pullback with the product
of the new base and that fiber. For a trivial bundle, equality with the original
new-base trivial topology is characterized by continuity of the old-base coordinate.

The homeomorphism sends `z` to `(z.proj, Bundle.Pullback.lift f z)`. Its inverse
sends a compatible pair `(a, v)` to the point over `a` obtained by transporting
`v.snd` along the equality `f a = v.proj`. The forward-value and inverse-projection
lemmas specify these canonical maps independently of any implementation choices.

## Implementation notes

The raw universal maps need only the domain and original total-space topologies.
In particular, `f` need not be continuous, and neither `B` nor the model-fiber
parameter `F` needs a topology. The constant comparison additionally uses the
given topology of one original fiber and its inducing inclusion. The trivial
comparison uses the stock trivial topologies on both bases. These describe
underlying total spaces, not local triviality for a discontinuous base map or
inverse continuity for arbitrary fiberwise linear equivalences.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, November 2017,
  Proposition 1.5 and the elementary pullback examples, pp. 18–20,
  https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf.
* Mathlib's `Mathlib.Data.Bundle` and
  `Mathlib.Topology.FiberBundle.Constructions` supply the dependent pullback
  family, its map to the original bundle, and its total-space topology.
-/

@[expose] public section

open Bundle

universe uA uB uC uF uE uX

namespace Bundle.Pullback

/-- The canonical pullback lift has exactly the points lying over the range of the base map. -/
theorem range_lift {A : Type uA} {B : Type uB}
    (F : Type uF) (E : B → Type uE) (f : A → B) :
    Set.range (@Bundle.Pullback.lift B F E A f) = (π F E) ⁻¹' Set.range f := by
  ext ⟨b, v⟩
  constructor
  · rintro ⟨⟨a, w⟩, h⟩
    exact ⟨a, congrArg TotalSpace.proj h⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, v⟩, rfl⟩

section LiftTopology

variable {A : Type uA} {B : Type uB}
  (F : Type uF) (E : B → Type uE) (f : A → B)
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]

/-- An inducing base map induces the canonical pullback lift when the original projection
is continuous. -/
theorem isInducing_lift (hf : Topology.IsInducing f) (hπ : Continuous (π F E)) :
    Topology.IsInducing (@Bundle.Pullback.lift B F E A f) := by
  refine ⟨?_⟩
  rw [_root_.Pullback.TotalSpace.topologicalSpace, pullbackTopology_def, hf.eq_induced,
    induced_compose]
  apply inf_eq_right.mpr
  have hh := induced_mono
    (g := @Bundle.Pullback.lift B F E A f) hπ.le_induced
  simpa only [induced_compose, Function.comp_def, Bundle.Pullback.lift] using hh

/-- An embedding of bases gives an embedding of canonical total spaces when the original
projection is continuous. -/
theorem isEmbedding_lift (hf : Topology.IsEmbedding f) (hπ : Continuous (π F E)) :
    Topology.IsEmbedding (@Bundle.Pullback.lift B F E A f) := by
  refine ⟨isInducing_lift F E f hf.isInducing hπ, ?_⟩
  rintro ⟨a, v⟩ ⟨b, w⟩ h
  have hab : a = b := hf.injective (congrArg TotalSpace.proj h)
  subst b
  cases h
  rfl

/-- An open embedding of bases gives an open embedding of canonical total spaces when the
original projection is continuous. -/
theorem isOpenEmbedding_lift (hf : Topology.IsOpenEmbedding f) (hπ : Continuous (π F E)) :
    Topology.IsOpenEmbedding (@Bundle.Pullback.lift B F E A f) := by
  refine ⟨isEmbedding_lift F E f hf.isEmbedding hπ, ?_⟩
  rw [range_lift]
  exact hf.isOpen_range.preimage hπ

/-- A closed embedding of bases gives a closed embedding of canonical total spaces when the
original projection is continuous. -/
theorem isClosedEmbedding_lift (hf : Topology.IsClosedEmbedding f) (hπ : Continuous (π F E)) :
    Topology.IsClosedEmbedding (@Bundle.Pullback.lift B F E A f) := by
  refine ⟨isEmbedding_lift F E f hf.isEmbedding hπ, ?_⟩
  rw [range_lift]
  exact hf.isClosed_range.preimage hπ

end LiftTopology

variable {A : Type uA} {B : Type uB}
  (F : Type uF) (E : B → Type uE) (f : A → B)
  [TopologicalSpace A] [TopologicalSpace (TotalSpace F E)]

/-- The canonical product-subspace model of the pullback total space.

The forward map sends `z` to `⟨(z.proj, Bundle.Pullback.lift f z), rfl⟩`.
The inverse takes `⟨(a, v), h⟩` to the point over `a` whose fiber coordinate is
`v.snd` transported from `E v.proj` to `E (f a)` along `h.symm`.
This identifies the dependent construction with the explicit subspace used in
Hatcher's Proposition 1.5.
-/
def homeomorphProdSubtype :
    TotalSpace F (f *ᵖ E) ≃ₜ
      {p : A × TotalSpace F E // f p.1 = p.2.proj} := by
  let e : TotalSpace F (f *ᵖ E) ≃
      {p : A × TotalSpace F E // f p.1 = p.2.proj} :=
    { toFun := fun z ↦ ⟨(z.proj, Bundle.Pullback.lift f z), rfl⟩
      invFun := fun p ↦ ⟨p.val.1,
        (show E (f p.val.1) from p.property.symm ▸ p.val.2.snd)⟩
      left_inv := by rintro ⟨a, v⟩; rfl
      right_inv := by
        rintro ⟨⟨a, ⟨b, v⟩⟩, h⟩
        dsimp at h
        subst b
        rfl }
  exact e.toHomeomorphOfIsInducing
    (Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (inducing_pullbackTotalSpaceEmbedding F E f))

/-- The forward map in the product-subspace model preserves both projections. -/
@[simp]
theorem homeomorphProdSubtype_apply_val (z : TotalSpace F (f *ᵖ E)) :
    (homeomorphProdSubtype F E f z).val = (z.proj, Bundle.Pullback.lift f z) := by
  rfl

/-- The inverse product-subspace map has the prescribed base coordinate. -/
@[simp]
theorem homeomorphProdSubtype_symm_proj
    (p : {p : A × TotalSpace F E // f p.1 = p.2.proj}) :
    ((homeomorphProdSubtype F E f).symm p).proj = p.val.1 := by
  rfl

/-- The inverse product-subspace map lifts to the prescribed original bundle point. -/
@[simp]
theorem lift_homeomorphProdSubtype_symm
    (p : {p : A × TotalSpace F E // f p.1 = p.2.proj}) :
    Bundle.Pullback.lift f ((homeomorphProdSubtype F E f).symm p) = p.val.2 := by
  exact congrArg (fun q ↦ q.val.2) ((homeomorphProdSubtype F E f).apply_symm_apply p)

variable {X : Type uX} [TopologicalSpace X]

/-- A map into a pullback total space is continuous exactly when both projections are. -/
theorem continuous_iff (k : X → TotalSpace F (f *ᵖ E)) :
    Continuous k ↔
      Continuous (fun x ↦ (k x).proj) ∧
        Continuous (fun x ↦ Bundle.Pullback.lift f (k x)) := by
  rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuous_iff]
  exact continuous_prodMk

/-- The universal continuous map into a pullback total space.

At `x` this is `(homeomorphProdSubtype F E f).symm ⟨(a x, b x), h x⟩`.
Its base coordinate is `a x` and its image in the original total space is `b x`.
-/
def liftMap (a : C(X, A)) (b : C(X, TotalSpace F E))
    (h : ∀ x, f (a x) = (b x).proj) :
    C(X, TotalSpace F (f *ᵖ E)) where
  toFun x := (homeomorphProdSubtype F E f).symm ⟨(a x, b x), h x⟩
  continuous_toFun := (homeomorphProdSubtype F E f).symm.continuous.comp
    ((a.continuous.prodMk b.continuous).subtype_mk h)

variable (a : C(X, A)) (b : C(X, TotalSpace F E))
  (h : ∀ x, f (a x) = (b x).proj)

/-- The universal map into the pullback has the specified base projection. -/
@[simp]
theorem liftMap_proj (x : X) :
    (liftMap F E f a b h x).proj = a x := by
  exact homeomorphProdSubtype_symm_proj F E f ⟨(a x, b x), h x⟩

/-- The universal map into the pullback has the specified image in the original total space. -/
@[simp]
theorem lift_liftMap (x : X) :
    Bundle.Pullback.lift f (liftMap F E f a b h x) = b x := by
  exact lift_homeomorphProdSubtype_symm F E f ⟨(a x, b x), h x⟩

/-- The two projections uniquely determine the continuous map into a pullback. -/
theorem liftMap_unique (g : C(X, TotalSpace F (f *ᵖ E)))
    (hp : ∀ x, (g x).proj = a x)
    (hl : ∀ x, Bundle.Pullback.lift f (g x) = b x) :
    g = liftMap F E f a b h := by
  apply ContinuousMap.ext
  intro x
  apply (homeomorphProdSubtype F E f).injective
  apply Subtype.ext
  simp only [homeomorphProdSubtype_apply_val, liftMap_proj, lift_liftMap, hp, hl]

end Bundle.Pullback

/-!
## Constant maps and trivial bundles

The constant comparison uses the given topology on the original fiber `E b`.
The inducing premise relates this topology to the original total space; a fiber
bundle supplies it through `FiberBundle.totalSpaceMk_isInducing`.

The pullback of `Trivial B F` and `Trivial A F` have definitionally equal total
carriers, but their topologies need not agree. The trivial-topology criterion
refers to continuity on the original `Trivial A F` topology, including when `F`
is empty. Once this criterion holds, the identity equivalence can be packaged
by `Equiv.toHomeomorphOfIsInducing`, then composed with `Trivial.homeomorphProd`.
-/

namespace Bundle.Pullback

section Constant

variable {A : Type uA} {B : Type uB} (F : Type uF) (E : B → Type uE)
  [tA : TopologicalSpace A] [tE : TopologicalSpace (TotalSpace F E)]
  (b : B) [tb : TopologicalSpace (E b)]

/-- The pullback along a constant map is the product with the original fiber.

The forward map is `⟨a, v⟩ ↦ (a, v)` and the inverse is `(a, v) ↦ ⟨a, v⟩`.
The topology on `E b` is its given topology, related to the original total space
by the inducing inclusion. No topology on `B` or `F` is required. This is the
total-space comparison in Hatcher's constant-map example, p. 19, (2). -/
def homeomorphConst
    (hb : Topology.IsInducing (TotalSpace.mk b : E b → TotalSpace F E)) :
    @Homeomorph (TotalSpace F ((fun _ : A ↦ b) *ᵖ E)) (A × E b)
      (@pullbackTopology B F E A (fun _ ↦ b) tA tE)
      (@instTopologicalSpaceProd A (E b) tA tb) where
  toFun z := (z.proj, z.snd)
  invFun p := TotalSpace.mk' F p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine (_root_.Pullback.continuous_proj F E (fun _ : A ↦ b)).prodMk ?_
    exact hb.continuous_iff.2 (_root_.Pullback.continuous_lift F E (fun _ : A ↦ b))
  continuous_invFun := by
    apply (continuous_iff F E (fun _ : A ↦ b) _).2
    exact ⟨continuous_fst, hb.continuous.comp continuous_snd⟩

variable (hb : Topology.IsInducing (TotalSpace.mk b : E b → TotalSpace F E))

/-- The constant comparison reads the base and original fiber coordinates. -/
@[simp]
theorem homeomorphConst_apply (z : TotalSpace F ((fun _ : A ↦ b) *ᵖ E)) :
    homeomorphConst F E b hb z = (z.proj, z.snd) := by
  rfl

/-- The inverse constant comparison inserts the base and original fiber coordinates. -/
@[simp]
theorem homeomorphConst_symm_apply (p : A × E b) :
    (homeomorphConst F E b hb).symm p = TotalSpace.mk' F p.1 p.2 := by
  rfl

/-- The constant comparison preserves the base coordinate. -/
theorem homeomorphConst_apply_fst (z : TotalSpace F ((fun _ : A ↦ b) *ᵖ E)) :
    (homeomorphConst F E b hb z).1 = z.proj := by
  rfl

/-- The constant comparison preserves the original fiber coordinate. -/
theorem homeomorphConst_apply_snd (z : TotalSpace F ((fun _ : A ↦ b) *ᵖ E)) :
    (homeomorphConst F E b hb z).2 = z.snd := by
  rfl

/-- The inverse constant comparison has the prescribed base coordinate. -/
theorem homeomorphConst_symm_apply_proj (p : A × E b) :
    ((homeomorphConst F E b hb).symm p).proj = p.1 := by
  rfl

/-- The inverse constant comparison has the prescribed original fiber coordinate. -/
theorem homeomorphConst_symm_apply_snd (p : A × E b) :
    ((homeomorphConst F E b hb).symm p).snd = p.2 := by
  rfl

/-- The inverse constant comparison lifts to the corresponding point over `b`. -/
theorem lift_homeomorphConst_symm (p : A × E b) :
    Bundle.Pullback.lift (fun _ : A ↦ b) ((homeomorphConst F E b hb).symm p) =
      TotalSpace.mk' F b p.2 := by
  rfl

end Constant

section Trivial

variable {A : Type uA} {B : Type uB} (F : Type uF) (f : A → B)
  [tA : TopologicalSpace A] [tB : TopologicalSpace B] [tF : TopologicalSpace F]

/-- Pulling back the original trivial bundle gives the original new-base trivial
topology exactly when the old-base coordinate is continuous on that original
new-base total space.

In particular, `Continuous f` suffices by composition with the original trivial
projection. The intrinsic condition also applies to empty fibers, where it need
not imply continuity of `f`. Both original trivial topologies are explicit.
This is the topology comparison underlying Hatcher's trivial-bundle pullback
example, p. 19. -/
theorem pullbackTopology_trivial_eq_iff :
    @pullbackTopology B F (Trivial B F) A f tA
        (@Trivial.topologicalSpace B F tB tF) =
      @Trivial.topologicalSpace A F tA tF ↔
        @Continuous (TotalSpace F (Trivial A F)) B
          (@Trivial.topologicalSpace A F tA tF) tB (fun z ↦ f z.proj) := by
  simp only [pullbackTopology_def, Trivial.topologicalSpace, induced_inf,
    induced_compose, continuous_iff_le_induced]
  change
    TopologicalSpace.induced (π F (Trivial A F)) tA ⊓
        (TopologicalSpace.induced (fun z : TotalSpace F (Trivial A F) ↦ f z.proj) tB ⊓
          TopologicalSpace.induced (TotalSpace.trivialSnd A F) tF) =
      TopologicalSpace.induced (π F (Trivial A F)) tA ⊓
        TopologicalSpace.induced (TotalSpace.trivialSnd A F) tF ↔ _
  rw [inf_comm
    (TopologicalSpace.induced (fun z : TotalSpace F (Trivial A F) ↦ f z.proj) tB)
    (TopologicalSpace.induced (TotalSpace.trivialSnd A F) tF),
    ← inf_assoc, inf_eq_left]

end Trivial

end Bundle.Pullback

/-!
## Identity and composition

The identity pullback agrees with the original total space when the original
projection is continuous. For composition, the iterated topology additionally
records the intermediate-base coordinate. Its equality with the composite
pullback topology is equivalent to continuity of that coordinate on the composite
pullback. Continuity of the second base map is a sufficient, but not necessary,
condition.

The topology arguments of the comparison homeomorphisms are explicit: their
underlying family types are definitionally equal, but their topologies need not be.
These comparisons concern total spaces of families, without vector-bundle data;
they give the underlying homeomorphisms in Hatcher's pullback identities,
pp. 20, (i)–(ii), rather than the full vector-bundle isomorphisms.
-/

namespace Bundle.Pullback

section Identity

variable {B : Type uB} (F : Type uF) (E : B → Type uE)
  [tB : TopologicalSpace B] [tE : TopologicalSpace (TotalSpace F E)]

/-- The identity pullback has the original topology exactly when the original
projection is continuous. -/
theorem pullbackTopology_id_eq_iff :
    @pullbackTopology B F E B id tB tE = tE ↔ Continuous (π F E) := by
  rw [pullbackTopology_def]
  change TopologicalSpace.induced (π F E) tB ⊓ TopologicalSpace.induced id tE = tE ↔ _
  rw [induced_id, inf_eq_right, continuous_iff_le_induced]

/-- The canonical identity-pullback homeomorphism, sending `⟨b, v⟩` to `⟨b, v⟩`.

The continuity hypothesis concerns the original total space. Without it the
identity pullback can have a strictly finer topology than the original space.
This is the total-space comparison underlying Hatcher's identity (ii), p. 20. -/
def homeomorphId (hπ : Continuous (π F E)) :
    @Homeomorph (TotalSpace F ((id : B → B) *ᵖ E)) (TotalSpace F E)
      (@pullbackTopology B F E B id tB tE) tE := by
  refine @Equiv.toHomeomorphOfIsInducing _ _
    (@pullbackTopology B F E B id tB tE) tE (Equiv.refl _) ⟨?_⟩
  change @pullbackTopology B F E B id tB tE = TopologicalSpace.induced id tE
  rw [induced_id]
  exact (pullbackTopology_id_eq_iff F E).2 hπ

/-- The identity comparison is the canonical lift to the original total space. -/
@[simp]
theorem homeomorphId_apply (hπ : Continuous (π F E))
    (z : TotalSpace F ((id : B → B) *ᵖ E)) :
    homeomorphId F E hπ z = Bundle.Pullback.lift id z := by
  rfl

/-- The inverse identity comparison leaves the base and fiber coordinates unchanged. -/
@[simp]
theorem homeomorphId_symm_apply (hπ : Continuous (π F E)) (z : TotalSpace F E) :
    (homeomorphId F E hπ).symm z = TotalSpace.mk' F z.proj z.snd := by
  rfl

/-- The identity comparison preserves the base projection. -/
theorem homeomorphId_apply_proj (hπ : Continuous (π F E))
    (z : TotalSpace F ((id : B → B) *ᵖ E)) :
    (homeomorphId F E hπ z).proj = z.proj := by
  rfl

/-- The inverse identity comparison preserves the base projection. -/
theorem homeomorphId_symm_apply_proj (hπ : Continuous (π F E)) (z : TotalSpace F E) :
    ((homeomorphId F E hπ).symm z).proj = z.proj := by
  rfl

end Identity

section Composition

variable {A : Type uA} {B : Type uB} {C : Type uC}
  (F : Type uF) (E : C → Type uE) (f : B → C) (g : A → B)
  [tA : TopologicalSpace A] [tB : TopologicalSpace B]
  [tE : TopologicalSpace (TotalSpace F E)]

/-- Iterated and composite pullbacks have the same topology exactly when their
intermediate-base coordinate is continuous for the composite pullback topology.
No topology on `C`, nor continuity of `f`, is needed. -/
theorem pullbackTopology_comp_eq_iff :
    @pullbackTopology B F (f *ᵖ E) A g tA
        (@pullbackTopology C F E B f tB tE) =
      @pullbackTopology C F E A (f ∘ g) tA tE ↔
        @Continuous (TotalSpace F ((f ∘ g) *ᵖ E)) B
          (@pullbackTopology C F E A (f ∘ g) tA tE) tB
          (fun z ↦ g z.proj) := by
  simp only [pullbackTopology_def, induced_inf,
    induced_compose, continuous_iff_le_induced]
  change
    TopologicalSpace.induced (π F ((f ∘ g) *ᵖ E)) tA ⊓
        (TopologicalSpace.induced (fun z : TotalSpace F ((f ∘ g) *ᵖ E) ↦ g z.proj) tB ⊓
          TopologicalSpace.induced (Bundle.Pullback.lift (f ∘ g)) tE) =
      TopologicalSpace.induced (π F ((f ∘ g) *ᵖ E)) tA ⊓
        TopologicalSpace.induced (Bundle.Pullback.lift (f ∘ g)) tE ↔ _
  rw [inf_comm
    (TopologicalSpace.induced (fun z : TotalSpace F ((f ∘ g) *ᵖ E) ↦ g z.proj) tB)
    (TopologicalSpace.induced (Bundle.Pullback.lift (f ∘ g)) tE),
    ← inf_assoc, inf_eq_left]

/-- The canonical flattening homeomorphism for an iterated pullback, under the
intrinsic intermediate-coordinate continuity condition.

Both directions send `⟨a, v⟩` to `⟨a, v⟩`. The hypothesis is continuity of the
single additional coordinate on the composite pullback, not a supplied
homeomorphism or an equality of topologies. If `g` is continuous, the condition
follows by composing it with `Pullback.continuous_proj` for `f ∘ g`.
No continuity of `f`, topology on `C` or `F`, local triviality or nonempty-fiber
hypothesis is required. This is the total-space comparison underlying Hatcher's
composition identity (i), p. 20. -/
def homeomorphComp
    (h : @Continuous (TotalSpace F ((f ∘ g) *ᵖ E)) B
      (@pullbackTopology C F E A (f ∘ g) tA tE) tB (fun z ↦ g z.proj)) :
    @Homeomorph (TotalSpace F (g *ᵖ (f *ᵖ E)))
      (TotalSpace F ((f ∘ g) *ᵖ E))
      (@pullbackTopology B F (f *ᵖ E) A g tA
        (@pullbackTopology C F E B f tB tE))
      (@pullbackTopology C F E A (f ∘ g) tA tE) := by
  refine @Equiv.toHomeomorphOfIsInducing _ _
    (@pullbackTopology B F (f *ᵖ E) A g tA
      (@pullbackTopology C F E B f tB tE))
    (@pullbackTopology C F E A (f ∘ g) tA tE) (Equiv.refl _) ⟨?_⟩
  change @pullbackTopology B F (f *ᵖ E) A g tA
      (@pullbackTopology C F E B f tB tE) =
    TopologicalSpace.induced id (@pullbackTopology C F E A (f ∘ g) tA tE)
  rw [induced_id]
  exact (pullbackTopology_comp_eq_iff F E f g).2 h

variable
  (h : @Continuous (TotalSpace F ((f ∘ g) *ᵖ E)) B
    (@pullbackTopology C F E A (f ∘ g) tA tE) tB (fun z ↦ g z.proj))

/-- Flattening leaves the base and fiber coordinates unchanged. -/
@[simp]
theorem homeomorphComp_apply (z : TotalSpace F (g *ᵖ (f *ᵖ E))) :
    homeomorphComp F E f g h z = TotalSpace.mk' F z.proj z.snd := by
  rfl

/-- Unflattening leaves the base and fiber coordinates unchanged. -/
@[simp]
theorem homeomorphComp_symm_apply (z : TotalSpace F ((f ∘ g) *ᵖ E)) :
    (homeomorphComp F E f g h).symm z = TotalSpace.mk' F z.proj z.snd := by
  rfl

/-- Flattening preserves the base projection. -/
theorem homeomorphComp_apply_proj (z : TotalSpace F (g *ᵖ (f *ᵖ E))) :
    (homeomorphComp F E f g h z).proj = z.proj := by
  rfl

/-- Unflattening preserves the base projection. -/
theorem homeomorphComp_symm_apply_proj (z : TotalSpace F ((f ∘ g) *ᵖ E)) :
    ((homeomorphComp F E f g h).symm z).proj = z.proj := by
  rfl

/-- The lift from a composite pullback agrees with the two successive lifts. -/
theorem lift_homeomorphComp (z : TotalSpace F (g *ᵖ (f *ᵖ E))) :
    Bundle.Pullback.lift (f ∘ g) (homeomorphComp F E f g h z) =
      Bundle.Pullback.lift f (Bundle.Pullback.lift g z) := by
  rfl

end Composition

end Bundle.Pullback
