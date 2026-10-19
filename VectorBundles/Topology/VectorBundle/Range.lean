/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Algebra.Module.Submodule.Equiv
public import VectorBundles.Topology.VectorBundle.Embedding

/-!
# Linear ranges of fiberwise linear total-space embeddings

A fiberwise linear map whose original total map is an embedding identifies its source
with a vector bundle of linear ranges in the target fibers. The range fibers retain
their subtype algebra and topologies, the total topology is induced from the original
target total space, and the model and chosen atlas come from the source bundle.

`VectorBundle.Range.bundleOfIsEmbedding` returns coupled fiber-bundle and vector-bundle
data. The target needs only a topological fiber-bundle structure, not a normed model
or a vector-bundle structure. `VectorBundle.Range.bundleOfInjective` applies the
finite-dimensional source embedding criterion to a continuous fiberwise injection.

`VectorBundle.rangeBundle` is the specialization to a trivial target. Its total topology
is still defined by inclusion into the product of the base and ambient module; its
construction agrees with the general range construction through the propositional
equality of these topologies. The ambient module needs no norm or continuity of its
algebraic operations. None of these constructions installs a global bundle instance
depending on an embedding proof.

## References

* Mathlib's homeomorphism onto the range of an embedding, linear equivalence onto a
  linear range, and transport of trivializations by homeomorphisms.
* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, November 2017,
  Proposition 1.4, printed page 13 (PDF page 17): the image subbundle step in the
  coordinate-embedding argument.
-/

@[expose] public section

universe u𝕜 uB uF uH uE uκ uG uE' uX

open Bundle

namespace VectorBundle

section Topology

variable {𝕜 : Type u𝕜} {B : Type uB} {F : Type uF} {H : Type uH}
  {E : B → Type uE} [Semiring 𝕜] [TopologicalSpace B] [TopologicalSpace H]
  [AddCommMonoid H] [Module 𝕜 H] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  (L : ∀ b, E b →ₗ[𝕜] H)

/-- The topology on the total space of the linear ranges induced by the total inclusion.
The topology of each range fiber is still its subtype topology in `H`. -/
@[instance_reducible]
def rangeTotalSpaceTopology : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) :=
  TopologicalSpace.induced
    (fun p : TotalSpace F (fun b ↦ (L b).range) ↦ (p.proj, (p.2 : H))) inferInstance

end Topology

end VectorBundle

/-!
## Ranges in varying target fibers

`VectorBundle.Range` retains the target bundle's fibers and total topology. Its range total
space is induced by inclusion into that total space, and its model and chosen atlas come
from the source. `VectorBundle.Range.bundleOfInjective` uses
`VectorBundle.isEmbedding_of_injective`; the more general
`VectorBundle.Range.bundleOfIsEmbedding` only needs a topological target fiber bundle.

The constructions use Mathlib's `LinearEquiv.ofInjective`,
`Equiv.toHomeomorphOfIsInducing`, and `Bundle.Trivialization.compHomeomorph`, together
with transport of local trivializations and the local vector-bundle embedding criterion.
Hatcher's §1.1 supplies vector-bundle context; the varying-target interface is an auxiliary
construction.
-/

namespace VectorBundle.Range

section Inclusion

variable {κ : Type uκ} {B : Type uB} {F : Type uF} {G : Type uG}
  {E : B → Type uE} {E' : B → Type uE'} [Semiring κ]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  (φ : ∀ b, E b →ₗ[κ] E' b)

/-- Inclusion of the linear-range total space into the given target total space. -/
def totalSpaceInclusion : TotalSpace F (fun b ↦ (φ b).range) → TotalSpace G E' :=
  fun p ↦ ⟨p.proj, (p.2 : E' p.proj)⟩

@[simp]
theorem totalSpaceInclusion_mk (b : B) (v : (φ b).range) :
    totalSpaceInclusion (F := F) (G := G) φ (TotalSpace.mk' F b v) =
      TotalSpace.mk' G b (v : E' b) := rfl

@[simp]
theorem totalSpaceInclusion_proj (p : TotalSpace F (fun b ↦ (φ b).range)) :
    (totalSpaceInclusion (G := G) φ p).proj = p.proj := rfl

@[simp]
theorem totalSpaceInclusion_snd (p : TotalSpace F (fun b ↦ (φ b).range)) :
    (totalSpaceInclusion (G := G) φ p).2 = (p.2 : E' p.proj) := rfl

/-- The total inclusion is injective without topological assumptions. -/
theorem totalSpaceInclusion_injective :
    Function.Injective (totalSpaceInclusion (F := F) (G := G) φ) := by
  rintro ⟨b, v⟩ ⟨c, w⟩ h
  obtain rfl : b = c := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk' F b)
    (Subtype.ext (TotalSpace.mk_injective b h))

variable [targetTopology : TopologicalSpace (TotalSpace G E')]

/-- The range total topology induced by inclusion into the given target total space.
No topology on either model, the base, or the individual fibers is needed to define it. -/
@[instance_reducible]
def totalSpaceTopology : TopologicalSpace (TotalSpace F (fun b ↦ (φ b).range)) :=
  TopologicalSpace.induced (totalSpaceInclusion (F := F) (G := G) φ) targetTopology

/-- The named range topology is induced along the prescribed total inclusion. -/
theorem totalSpaceTopology_eq_induced :
    totalSpaceTopology (F := F) (G := G) φ =
      TopologicalSpace.induced (totalSpaceInclusion (F := F) (G := G) φ) targetTopology := rfl

/-- The total range inclusion is an embedding for the induced total topology. -/
theorem totalSpaceInclusion_isEmbedding :
    @Topology.IsEmbedding (TotalSpace F (fun b ↦ (φ b).range)) (TotalSpace G E')
      (totalSpaceTopology (F := F) (G := G) φ) targetTopology
      (totalSpaceInclusion (F := F) (G := G) φ) := by
  let := totalSpaceTopology (F := F) (G := G) φ
  exact ⟨⟨rfl⟩, totalSpaceInclusion_injective (F := F) (G := G) φ⟩

/-- A map into the range total space is continuous exactly when its composite with the
inclusion into the original target total space is continuous. -/
theorem continuous_iff_comp_totalSpaceInclusion {X : Type uX} [TopologicalSpace X]
    (f : X → TotalSpace F (fun b ↦ (φ b).range)) :
    @Continuous X (TotalSpace F (fun b ↦ (φ b).range))
        inferInstance (totalSpaceTopology (F := F) (G := G) φ) f ↔
      Continuous (totalSpaceInclusion (F := F) (G := G) φ ∘ f) := by
  let := totalSpaceTopology (F := F) (G := G) φ
  exact (totalSpaceInclusion_isEmbedding (F := F) (G := G) φ).isInducing.continuous_iff

end Inclusion

section Equivalence

variable {κ : Type uκ} {B : Type uB} {F : Type uF} {G : Type uG}
  {E : B → Type uE} {E' : B → Type uE'} [Semiring κ]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]
  (φ : ∀ b, E b →ₗ[κ] E' b)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦
    (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E')))

/-- The equivalence onto each linear range, with injectivity derived from the total embedding. -/
noncomputable def linearEquiv (b : B) : E b ≃ₗ[κ] (φ b).range :=
  LinearEquiv.ofInjective (φ b) fun _ _ h ↦
    TotalSpace.mk_injective b (hI.injective (congrArg (TotalSpace.mk' G b) h))

@[simp]
theorem linearEquiv_apply (b : B) (v : E b) :
    (linearEquiv φ hI b v : E' b) = φ b v := rfl

/-- The inverse fiber equivalence is an inverse to the given map on its range. -/
@[simp]
theorem linearEquiv_symm_apply (b : B) (v : (φ b).range) :
    φ b ((linearEquiv φ hI b).symm v) = (v : E' b) :=
  LinearEquiv.ofInjective_symm_apply _ _

/-- The total range homeomorphism, with the range topology induced from the original target.
Both directions use the same fiberwise linear equivalences and preserve the base. -/
noncomputable def imageHomeomorph :
    @Homeomorph (TotalSpace F E) (TotalSpace F (fun b ↦ (φ b).range))
      inferInstance (totalSpaceTopology (F := F) (G := G) φ) := by
  letI := totalSpaceTopology (F := F) (G := G) φ
  let e : TotalSpace F E ≃ TotalSpace F (fun b ↦ (φ b).range) :=
    { toFun := fun p ↦ TotalSpace.mk' F p.proj (linearEquiv φ hI p.proj p.2)
      invFun := fun p ↦ TotalSpace.mk' F p.proj ((linearEquiv φ hI p.proj).symm p.2)
      left_inv := by
        rintro ⟨b, v⟩
        exact congrArg (TotalSpace.mk' F b) ((linearEquiv φ hI b).symm_apply_apply v)
      right_inv := by
        rintro ⟨b, v⟩
        exact congrArg (TotalSpace.mk' F b) ((linearEquiv φ hI b).apply_symm_apply v) }
  exact e.toHomeomorphOfIsInducing
    ((totalSpaceInclusion_isEmbedding (F := F) (G := G) φ).isInducing.of_comp_iff.mp
      hI.isInducing)

@[simp]
theorem imageHomeomorph_apply (b : B) (v : E b) :
    imageHomeomorph φ hI (TotalSpace.mk' F b v) =
      TotalSpace.mk' F b (linearEquiv φ hI b v) := rfl

@[simp]
theorem imageHomeomorph_proj (p : TotalSpace F E) :
    (imageHomeomorph φ hI p).proj = p.proj := rfl

@[simp]
theorem imageHomeomorph_symm_apply (b : B) (v : (φ b).range) :
    (@Homeomorph.symm _ _ inferInstance (totalSpaceTopology (F := F) (G := G) φ)
      (imageHomeomorph φ hI)) (TotalSpace.mk' F b v) =
      TotalSpace.mk' F b ((linearEquiv φ hI b).symm v) := rfl

@[simp]
theorem imageHomeomorph_symm_proj (p : TotalSpace F (fun b ↦ (φ b).range)) :
    ((@Homeomorph.symm _ _ inferInstance (totalSpaceTopology (F := F) (G := G) φ)
      (imageHomeomorph φ hI)) p).proj = p.proj := rfl

/-- Inclusion after the range homeomorphism recovers the original total map. -/
theorem imageHomeomorph_inclusion (p : TotalSpace F E) :
    totalSpaceInclusion (G := G) φ (imageHomeomorph φ hI p) =
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E') := rfl

/-- Inclusion of a range point is recovered by the original map after the inverse homeomorphism. -/
theorem imageHomeomorph_symm_inclusion (p : TotalSpace F (fun b ↦ (φ b).range)) :
    (fun q : TotalSpace F E ↦ (⟨q.proj, φ q.proj q.2⟩ : TotalSpace G E'))
        ((@Homeomorph.symm _ _ inferInstance (totalSpaceTopology (F := F) (G := G) φ)
          (imageHomeomorph φ hI)) p) =
      totalSpaceInclusion (G := G) φ p :=
  congrArg (TotalSpace.mk' G p.proj) (linearEquiv_symm_apply φ hI p.proj p.2)

end Equivalence

section Trivialization

variable {κ : Type uκ} {B : Type uB} {F : Type uF} {G : Type uG}
  {E : B → Type uE} {E' : B → Type uE'} [Semiring κ]
  [TopologicalSpace B] [TopologicalSpace F]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]
  (φ : ∀ b, E b →ₗ[κ] E' b)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦
    (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E')))

/-- A source chart transported by the inverse range homeomorphism, over the same base set. -/
noncomputable def trivialization (e : Trivialization F (π F E)) :
    @Trivialization B F _ _ _ (totalSpaceTopology (F := F) (G := G) φ)
      (π F (fun b ↦ (φ b).range)) := by
  letI := totalSpaceTopology (F := F) (G := G) φ
  let e' := e.compHomeomorph (imageHomeomorph φ hI).symm
  exact
    { toOpenPartialHomeomorph := e'.toOpenPartialHomeomorph
      baseSet := e.baseSet
      open_baseSet := e.open_baseSet
      source_eq := e'.source_eq.trans
        (congrArg (fun f : TotalSpace F (fun b ↦ (φ b).range) → B ↦ f ⁻¹' e.baseSet)
          (funext fun p ↦ imageHomeomorph_symm_proj φ hI p))
      target_eq := e'.target_eq
      proj_toFun := by
        intro p hp
        rw [e'.proj_toFun p hp]
        exact imageHomeomorph_symm_proj φ hI p }

@[simp]
theorem trivialization_baseSet (e : Trivialization F (π F E)) :
    @Trivialization.baseSet B F _ _ _ (totalSpaceTopology (F := F) (G := G) φ) _
      (trivialization φ hI e) = e.baseSet := rfl

@[simp]
theorem trivialization_apply (e : Trivialization F (π F E))
    (p : TotalSpace F (fun b ↦ (φ b).range)) :
    trivialization φ hI e p =
      e ((@Homeomorph.symm _ _ inferInstance (totalSpaceTopology (F := F) (G := G) φ)
        (imageHomeomorph φ hI)) p) := rfl

@[simp]
theorem trivialization_symm_apply (e : Trivialization F (π F E)) (p : B × F) :
    (@OpenPartialHomeomorph.symm _ _ (totalSpaceTopology (F := F) (G := G) φ) inferInstance
      (@Trivialization.toOpenPartialHomeomorph B F _ _ _
        (totalSpaceTopology (F := F) (G := G) φ) _ (trivialization φ hI e))) p =
      imageHomeomorph φ hI (e.toOpenPartialHomeomorph.symm p) := rfl

variable [AddCommMonoid F] [Module κ F]

/-- Transport of a fiberwise linear chart is fiberwise linear. -/
theorem trivialization_isLinear (e : Trivialization F (π F E)) [e.IsLinear κ] :
    @Trivialization.IsLinear κ B F (fun b ↦ (φ b).range)
      _ _ _ (totalSpaceTopology (F := F) (G := G) φ) _ _ _ _
      (trivialization φ hI e) := by
  let := totalSpaceTopology (F := F) (G := G) φ
  refine ⟨fun b hb ↦ ?_⟩
  have h := (((e.linear κ hb).mk' _).comp
    (linearEquiv φ hI b).symm.toLinearMap).isLinear
  simpa only [trivialization_apply, imageHomeomorph_symm_apply,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_def, IsLinearMap.mk'_apply] using h

/-- Transport preserves the coordinate operators on the source model over each overlap. -/
theorem trivialization_coordChangeL (e e' : Trivialization F (π F E))
    [e.IsLinear κ] [e'.IsLinear κ] (b : B) (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    @Trivialization.coordChangeL κ B F (fun b ↦ (φ b).range)
      _ _ _ (totalSpaceTopology (F := F) (G := G) φ) _ _ _ _
      (trivialization φ hI e) (trivialization φ hI e')
      (trivialization_isLinear φ hI e) (trivialization_isLinear φ hI e') b =
      e.coordChangeL κ e' b := by
  let := totalSpaceTopology (F := F) (G := G) φ
  let := trivialization_isLinear (F := F) (G := G) φ hI e
  let := trivialization_isLinear (F := F) (G := G) φ hI e'
  have hb' : b ∈ (trivialization (F := F) (G := G) φ hI e).baseSet ∩
      (trivialization (F := F) (G := G) φ hI e').baseSet := by
    simpa only [trivialization_baseSet] using hb
  ext v
  rw [Trivialization.coordChangeL_apply' (trivialization (F := F) (G := G) φ hI e)
      (trivialization (F := F) (G := G) φ hI e') hb',
    Trivialization.coordChangeL_apply' e e' hb,
    trivialization_apply, trivialization_symm_apply, Homeomorph.symm_apply_apply]

end Trivialization

section FiberTopology

variable {κ : Type uκ} [Semiring κ] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} {G : Type uG} [TopologicalSpace G]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {E' : B → Type uE'} [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace G E')]
  (φ : ∀ b, E b →ₗ[κ] E' b)

/-- Each fiber constructor is inducing for the original range subtype topology. -/
theorem totalSpaceMk_isInducing [FiberBundle G E'] (b : B) :
    @Topology.IsInducing (φ b).range (TotalSpace F (fun b ↦ (φ b).range))
      inferInstance (totalSpaceTopology (F := F) (G := G) φ)
      (@TotalSpace.mk B F (fun b ↦ (φ b).range) b) := by
  let := totalSpaceTopology (F := F) (G := G) φ
  exact (totalSpaceInclusion_isEmbedding (F := F) (G := G) φ).isInducing.of_comp_iff.mp
    ((FiberBundle.totalSpaceMk_isInducing G E' b).comp Topology.IsInducing.subtypeVal)

end FiberTopology

section Bundle

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {G : Type uG} [TopologicalSpace G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type uE'} [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace G E')]
  (φ : ∀ b, E b →ₗ[κ] E' b)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦
    (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E')))

@[instance_reducible]
private noncomputable def fiberBundle [FiberBundle F E] [FiberBundle G E']
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) :
    @FiberBundle B F _ _ (fun b ↦ (φ b).range)
      (totalSpaceTopology (F := F) (G := G) φ) _ := by
  letI := totalSpaceTopology (F := F) (G := G) φ
  exact
    { totalSpaceMk_isInducing' := totalSpaceMk_isInducing (F := F) (G := G) φ
      trivializationAtlas' := trivialization φ hI '' trivializationAtlas F E
      trivializationAt' b := trivialization φ hI (trivializationAt F E b)
      mem_baseSet_trivializationAt' := mem_baseSet_trivializationAt F E
      trivialization_mem_atlas' b :=
        ⟨trivializationAt F E b, trivialization_mem_atlas F E b, rfl⟩ }

/-- Coupled fiber-bundle and vector-bundle data on the linear ranges of a total embedding.
The range fibers have their subtype topologies, the total topology is induced from the
original target total space, and the model and atlas are transported from the source.
The target needs only a topological fiber-bundle structure. The embedding is taken between
the original source and target total spaces. -/
@[no_expose] noncomputable def bundleOfIsEmbedding
    [FiberBundle F E] [VectorBundle κ F E] [FiberBundle G E']
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) :
    Σ' fb : @FiberBundle B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _,
      @VectorBundle κ B F (fun b ↦ (φ b).range) _ _ _ _ _ _
        (totalSpaceTopology (F := F) (G := G) φ) _ fb := by
  letI := totalSpaceTopology (F := F) (G := G) φ
  letI := fiberBundle (F := F) (G := G) φ hI
  refine ⟨fiberBundle (F := F) (G := G) φ hI, ?_⟩
  refine
    { trivialization_linear' := ?_
      continuousOn_coordChange' := ?_ }
  · rintro _ ⟨e, he, rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    exact trivialization_isLinear φ hI e
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    have := trivialization_isLinear φ hI e
    have := trivialization_isLinear φ hI e'
    refine (continuousOn_coordChange κ e e').congr ?_
    intro b hb
    exact congrArg (fun f : F ≃L[κ] F ↦ (f : F →L[κ] F))
      (trivialization_coordChangeL φ hI e e' b hb)

variable [FiberBundle F E] [VectorBundle κ F E] [FiberBundle G E']

/-- The chosen chart is the transport of the original chosen source chart. -/
theorem bundleOfIsEmbedding_trivializationAt (b : B) :
    @FiberBundle.trivializationAt' B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _
        (bundleOfIsEmbedding (F := F) (G := G) φ hI).1 b =
      trivialization (F := F) (G := G) φ hI (trivializationAt F E b) := by
  rfl

/-- The output atlas is exactly the image of the source atlas under chart transport. -/
theorem bundleOfIsEmbedding_trivializationAtlas :
    @FiberBundle.trivializationAtlas' B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _
        (bundleOfIsEmbedding (F := F) (G := G) φ hI).1 =
      trivialization (F := F) (G := G) φ hI '' trivializationAtlas F E := by
  rfl

/-- The chosen charts of the range bundle are linear for the original scalar action. -/
theorem bundleOfIsEmbedding_trivializationAt_isLinear (b : B) :
    @Trivialization.IsLinear κ B F (fun b ↦ (φ b).range)
      _ _ _ (totalSpaceTopology (F := F) (G := G) φ) _ _ _ _
      (@FiberBundle.trivializationAt' B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _
        (bundleOfIsEmbedding (F := F) (G := G) φ hI).1 b) := by
  let := totalSpaceTopology (F := F) (G := G) φ
  let := (bundleOfIsEmbedding (F := F) (G := G) φ hI).1
  let := (bundleOfIsEmbedding (F := F) (G := G) φ hI).2
  exact _root_.trivialization_linear κ (trivializationAt F (fun b ↦ (φ b).range) b)

/-- Coordinate changes of the chosen output charts agree with the source operators on `F`. -/
theorem bundleOfIsEmbedding_coordChangeL (b₀ b₁ b : B)
    (hb : b ∈ (trivializationAt F E b₀).baseSet ∩ (trivializationAt F E b₁).baseSet) :
    @Trivialization.coordChangeL κ B F (fun b ↦ (φ b).range)
      _ _ _ (totalSpaceTopology (F := F) (G := G) φ) _ _ _ _
      (@FiberBundle.trivializationAt' B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _
        (bundleOfIsEmbedding (F := F) (G := G) φ hI).1 b₀)
      (@FiberBundle.trivializationAt' B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _
        (bundleOfIsEmbedding (F := F) (G := G) φ hI).1 b₁)
      (bundleOfIsEmbedding_trivializationAt_isLinear (F := F) (G := G) φ hI b₀)
      (bundleOfIsEmbedding_trivializationAt_isLinear (F := F) (G := G) φ hI b₁) b =
      (trivializationAt F E b₀).coordChangeL κ (trivializationAt F E b₁) b := by
  exact trivialization_coordChangeL (F := F) (G := G) φ hI
    (trivializationAt F E b₀) (trivializationAt F E b₁) b hb

end Bundle

section Injective

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F] [FiniteDimensional κ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace κ G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]
  {E' : B → Type uE'} [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace G E')] [FiberBundle G E'] [VectorBundle κ G E']
  (φ : ∀ b, E b →ₗ[κ] E' b) (hf : ∀ b, Function.Injective (φ b))
  [∀ b, IsModuleTopology κ (φ b).range]
  (hφ : Continuous (fun p : TotalSpace F E ↦
    (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E')))

/-- The range bundle of a continuous fiberwise linear injection with finite-dimensional
source model, when each range has the module topology inherited from its target fiber.
No completeness or finite-dimensionality of the target model is required. -/
noncomputable def bundleOfInjective (hf : ∀ b, Function.Injective (φ b))
    (hφ : Continuous (fun p : TotalSpace F E ↦
      (⟨p.proj, φ p.proj p.2⟩ : TotalSpace G E'))) :
    Σ' fb : @FiberBundle B F _ _ (fun b ↦ (φ b).range)
        (totalSpaceTopology (F := F) (G := G) φ) _,
      @VectorBundle κ B F (fun b ↦ (φ b).range) _ _ _ _ _ _
        (totalSpaceTopology (F := F) (G := G) φ) _ fb :=
  bundleOfIsEmbedding (F := F) (G := G) φ
    (VectorBundle.isEmbedding_of_injective (F := F) (G := G) φ hf hφ)

/-- The injective construction uses the general construction with the original
embedding criterion. -/
theorem bundleOfInjective_eq_bundleOfIsEmbedding :
    bundleOfInjective (F := F) (G := G) φ hf hφ =
      bundleOfIsEmbedding (F := F) (G := G) φ
        (VectorBundle.isEmbedding_of_injective (F := F) (G := G) φ hf hφ) := rfl

end Injective

section TrivialTarget

variable {κ : Type uκ} [Semiring κ] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} {H : Type uH} [TopologicalSpace H] [AddCommMonoid H] [Module κ H]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  (L : ∀ b, E b →ₗ[κ] H)

/-- For the original trivial target total topology, the induced range topology agrees
propositionally with the topology induced into the product `B × H`. -/
theorem totalSpaceTopology_trivial :
    totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
      (targetTopology := Trivial.topologicalSpace B H) L =
      VectorBundle.rangeTotalSpaceTopology (F := F) L := by
  rw [totalSpaceTopology_eq_induced (F := F) (G := H) (E' := Trivial B H)
      (targetTopology := Trivial.topologicalSpace B H) L,
    (Trivial.isInducing_toProd B H).eq_induced, induced_compose]
  rfl

end TrivialTarget

end VectorBundle.Range

namespace VectorBundle

section Topology

variable {𝕜 : Type u𝕜} {B : Type uB} {F : Type uF} {H : Type uH}
  {E : B → Type uE} [Semiring 𝕜] [TopologicalSpace B] [TopologicalSpace H]
  [AddCommMonoid H] [Module 𝕜 H] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  (L : ∀ b, E b →ₗ[𝕜] H)

/-- The total inclusion of the range family is an embedding in the induced topology. -/
theorem rangeInclusion_isEmbedding :
    @Topology.IsEmbedding (TotalSpace F (fun b ↦ (L b).range)) (B × H)
      (rangeTotalSpaceTopology L) inferInstance
      (fun p ↦ (p.proj, (p.2 : H))) := by
  let := Range.totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
    (targetTopology := Trivial.topologicalSpace B H) L
  have hI := (Trivial.homeomorphProd B H).isEmbedding.comp
    (Range.totalSpaceInclusion_isEmbedding (F := F) (G := H) (E' := Trivial B H)
      (targetTopology := Trivial.topologicalSpace B H) L)
  rw [← Range.totalSpaceTopology_trivial (F := F) L]
  simpa only [Function.comp_def, Trivial.homeomorphProd_apply,
    Range.totalSpaceInclusion_proj, Range.totalSpaceInclusion_snd] using hI

end Topology

section Equivalence

variable {𝕜 : Type u𝕜} {B : Type uB} {F : Type uF} {H : Type uH}
  {E : B → Type uE} [Semiring 𝕜] [TopologicalSpace B]
  [TopologicalSpace H] [AddCommMonoid H] [Module 𝕜 H]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)]
  (L : ∀ b, E b →ₗ[𝕜] H)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))

/-- The fiberwise linear equivalence with the linear range of a total embedding. -/
noncomputable def rangeLinearEquiv (b : B) : E b ≃ₗ[𝕜] (L b).range :=
  @Range.linearEquiv 𝕜 B F H E (Trivial B H) _ _ _ _ _
    inferInstance (Trivial.topologicalSpace B H) L
    ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI) b

@[simp]
theorem rangeLinearEquiv_apply (b : B) (v : E b) :
    (rangeLinearEquiv L hI b v : H) = L b v := rfl

/-- The original total space is homeomorphic over the base to its linear-range total
space, with the induced product topology and the original model `F`. -/
noncomputable def imageHomeomorph
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2))) :
    @Homeomorph (TotalSpace F E) (TotalSpace F (fun b ↦ (L b).range))
      inferInstance (rangeTotalSpaceTopology L) := by
  letI := rangeTotalSpaceTopology (F := F) L
  let e := @Range.imageHomeomorph 𝕜 B F H E (Trivial B H) _ _ _ _ _
    inferInstance (Trivial.topologicalSpace B H) L
    ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
  let e' := @Homeomorph.toEquiv _ _ inferInstance
    (Range.totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
      (targetTopology := Trivial.topologicalSpace B H) L) e
  refine
    { toEquiv := e'
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change @Continuous _ _ _ (rangeTotalSpaceTopology L) e'
    rw [← Range.totalSpaceTopology_trivial (F := F) L]
    exact @Homeomorph.continuous_toFun _ _ inferInstance
      (Range.totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
        (targetTopology := Trivial.topologicalSpace B H) L) e
  · change @Continuous _ _ (rangeTotalSpaceTopology L) _ e'.symm
    rw [← Range.totalSpaceTopology_trivial (F := F) L]
    exact @Homeomorph.continuous_invFun _ _ inferInstance
      (Range.totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
        (targetTopology := Trivial.topologicalSpace B H) L) e

/-- The range homeomorphism is the prescribed fiberwise range equivalence. -/
@[simp]
theorem imageHomeomorph_apply (b : B) (v : E b) :
    imageHomeomorph L hI (TotalSpace.mk' F b v) =
      TotalSpace.mk' F b (rangeLinearEquiv L hI b v) := rfl

@[simp]
theorem imageHomeomorph_proj (p : TotalSpace F E) :
    (imageHomeomorph L hI p).proj = p.proj := by
  obtain ⟨b, v⟩ := p
  simp

/-- The inverse range homeomorphism uses the inverse of the same fiber equivalence. -/
@[simp]
theorem imageHomeomorph_symm_apply (b : B) (v : (L b).range) :
    (@Homeomorph.symm _ _ inferInstance (rangeTotalSpaceTopology L)
      (imageHomeomorph L hI)) (TotalSpace.mk' F b v) =
      TotalSpace.mk' F b ((rangeLinearEquiv L hI b).symm v) := by
  let : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) := rangeTotalSpaceTopology L
  apply (imageHomeomorph L hI).symm_apply_eq.mpr
  simp

@[simp]
theorem imageHomeomorph_symm_proj (p : TotalSpace F (fun b ↦ (L b).range)) :
    ((@Homeomorph.symm _ _ inferInstance (rangeTotalSpaceTopology L)
      (imageHomeomorph L hI)) p).proj = p.proj := by
  obtain ⟨b, v⟩ := p
  simp

/-- Composing the range homeomorphism with the total inclusion recovers the input map. -/
theorem imageHomeomorph_inclusion (p : TotalSpace F E) :
    ((imageHomeomorph L hI p).proj, ((imageHomeomorph L hI p).2 : H)) =
      (p.proj, L p.proj p.2) := by
  obtain ⟨b, v⟩ := p
  rw [imageHomeomorph_apply]
  rfl

/-- Addition in each fiber is respected by the range homeomorphism. -/
theorem imageHomeomorph_map_add (b : B) (v w : E b) :
    imageHomeomorph L hI (TotalSpace.mk' F b (v + w)) =
      TotalSpace.mk' F b (rangeLinearEquiv L hI b v + rangeLinearEquiv L hI b w) := by
  simp

/-- Scalar multiplication in each fiber is respected by the range homeomorphism. -/
theorem imageHomeomorph_map_smul (b : B) (a : 𝕜) (v : E b) :
    imageHomeomorph L hI (TotalSpace.mk' F b (a • v)) =
      TotalSpace.mk' F b (a • rangeLinearEquiv L hI b v) := by
  simp

end Equivalence

section Bundle

variable {𝕜 : Type u𝕜} {B : Type uB} {F : Type uF} {H : Type uH}
  {E : B → Type uE} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [AddCommMonoid H] [Module 𝕜 H]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)]
  (L : ∀ b, E b →ₗ[𝕜] H)

/-- Fiber-bundle and vector-bundle data on the linear ranges of a fiberwise linear total embedding.
The model is `F`, the fiber topologies are the subtype topologies from `H`, and the
range total topology is induced by the total inclusion into `B × H`. -/
@[no_expose] noncomputable def rangeBundle [FiberBundle F E] [VectorBundle 𝕜 F E]
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2))) :
    Σ' fb : @FiberBundle B F _ _ (fun b ↦ (L b).range) (rangeTotalSpaceTopology L) _,
      @VectorBundle 𝕜 B F (fun b ↦ (L b).range) _ _ _ _ _ _
        (rangeTotalSpaceTopology L) _ fb := by
  have hTopology := Range.totalSpaceTopology_trivial (F := F) L
  exact Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
      Σ' fb : @FiberBundle B F _ _ (fun b ↦ (L b).range) t _,
        @VectorBundle 𝕜 B F (fun b ↦ (L b).range) _ _ _ _ _ _ t _ fb) hTopology)
    (@Range.bundleOfIsEmbedding 𝕜 inferInstance B inferInstance
      F inferInstance inferInstance H inferInstance
      E inferInstance inferInstance inferInstance inferInstance
      (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
      L inferInstance inferInstance (Trivial.fiberBundle B H)
      ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI))

end Bundle

end VectorBundle

namespace VectorBundle.Range

section TrivialTarget

variable {κ : Type uκ} [Semiring κ] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} {H : Type uH} [TopologicalSpace H] [AddCommMonoid H] [Module κ H]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  (L : ∀ b, E b →ₗ[κ] H)

variable [TopologicalSpace (TotalSpace F E)]
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))

/-- For a trivial target, the fiber equivalence agrees with the original range equivalence. -/
theorem linearEquiv_trivial (b : B) :
    @linearEquiv κ B F H E (Trivial B H) _ _ _ _ _ _
        (Trivial.topologicalSpace B H) L
        ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI) b =
      VectorBundle.rangeLinearEquiv L hI b := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rfl

/-- For a trivial target, the underlying total-space equivalence agrees with the original
range equivalence, without identifying the codomain topologies definitionally. -/
theorem imageHomeomorph_trivial_toEquiv :
    @Homeomorph.toEquiv _ _ inferInstance
        (totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
          (targetTopology := Trivial.topologicalSpace B H) L)
        (@imageHomeomorph κ B F H E (Trivial B H) _ _ _ _ _ _
          (Trivial.topologicalSpace B H) L
          ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)) =
      @Homeomorph.toEquiv _ _ inferInstance (VectorBundle.rangeTotalSpaceTopology L)
        (VectorBundle.imageHomeomorph L hI) := by
  apply Equiv.ext
  rintro ⟨b, v⟩
  exact congrArg (@TotalSpace.mk B F (fun b ↦ (L b).range) b)
    (LinearEquiv.congr_fun
      (linearEquiv_trivial (κ := κ) (F := F) (E := E) L hI b) v)

end TrivialTarget

end VectorBundle.Range

namespace VectorBundle.Range

section TrivialChart

variable {κ : Type uκ} [Semiring κ] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [TopologicalSpace F] {H : Type uH}
  [TopologicalSpace H] [AddCommMonoid H] [Module κ H]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)]
  (L : ∀ b, E b →ₗ[κ] H)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))

/-- For a trivial target, the whole partial equivalence of a transported chart is
precomposition by the original range homeomorphism. Together with
`VectorBundle.Range.trivialization_baseSet`, this identifies all chart data without
identifying the range total topologies definitionally. -/
theorem trivialization_trivial_toPartialEquiv (e : Trivialization F (π F E)) :
    @PartialHomeomorph.toPartialEquiv _ _
        (totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
          (targetTopology := Trivial.topologicalSpace B H) L) inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph _ _
          (totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
            (targetTopology := Trivial.topologicalSpace B H) L) inferInstance
          (@Trivialization.toOpenPartialHomeomorph B F _ _ _
            (totalSpaceTopology (F := F) (G := H) (E' := Trivial B H)
              (targetTopology := Trivial.topologicalSpace B H) L) _
            (@trivialization κ B F H E (Trivial B H) _ _ _ _ _ _ _
              inferInstance (Trivial.topologicalSpace B H) L
              ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI) e))) =
      @PartialHomeomorph.toPartialEquiv _ _ (VectorBundle.rangeTotalSpaceTopology L)
        inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph _ _
          (VectorBundle.rangeTotalSpaceTopology L) inferInstance
          (@Trivialization.toOpenPartialHomeomorph B F _ _ _
            (VectorBundle.rangeTotalSpaceTopology L) _
            (@Trivialization.compHomeomorph _ _ _ _ _ _ _ e
              (TotalSpace F (fun b ↦ (L b).range))
              (VectorBundle.rangeTotalSpaceTopology L)
              (@Homeomorph.symm _ _ inferInstance (VectorBundle.rangeTotalSpaceTopology L)
                (VectorBundle.imageHomeomorph L hI))))) := by
  rfl

end TrivialChart

section TrivialBundle

variable {κ : Type uκ} [NontriviallyNormedField κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {H : Type uH} [TopologicalSpace H] [AddCommMonoid H] [Module κ H]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]
  (L : ∀ b, E b →ₗ[κ] H)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))

/-- Specializing the target to a trivial bundle recovers the coupled product-topology
range bundle by transport of the entire bundle data along the range topology equality. -/
theorem bundleOfIsEmbedding_trivial :
    Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
      Σ' fb : @FiberBundle B F _ _ (fun b ↦ (L b).range) t _,
        @VectorBundle κ B F (fun b ↦ (L b).range) _ _ _ _ _ _ t _ fb)
      (totalSpaceTopology_trivial (F := F) L))
      (@bundleOfIsEmbedding κ inferInstance B inferInstance
        F inferInstance inferInstance H inferInstance
        E inferInstance inferInstance inferInstance inferInstance
        (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
        (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
        L inferInstance inferInstance (Trivial.fiberBundle B H)
        ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)) =
      VectorBundle.rangeBundle L hI := by
  rfl

end TrivialBundle

end VectorBundle.Range

namespace VectorBundle.Range

section BundleCast

variable {κ : Type uκ} {B : Type uB} {F : Type uF} {E : B → Type uE}
  [NontriviallyNormedField κ] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace κ F]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {τ τ' : TopologicalSpace (TotalSpace F E)}

/-- Projecting the chosen chart commutes with casting the coupled bundle data. -/
private theorem bundle_cast_trivializationAt (hτ : τ = τ')
    (q : Σ' fb : @FiberBundle B F _ _ E τ _,
      @VectorBundle κ B F E _ _ _ _ _ _ τ _ fb) (b : B) :
    @FiberBundle.trivializationAt' B F _ _ E τ' _
        (Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F E) ↦
          Σ' fb : @FiberBundle B F _ _ E t _,
            @VectorBundle κ B F E _ _ _ _ _ _ t _ fb) hτ) q).1 b =
      Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F E) ↦
        @Trivialization B F (TotalSpace F E) _ _ t (π F E)) hτ)
        (@FiberBundle.trivializationAt' B F _ _ E τ _ q.1 b) := by
  cases hτ
  rfl

/-- Projecting the full chart atlas commutes with casting the coupled bundle data. -/
private theorem bundle_cast_trivializationAtlas (hτ : τ = τ')
    (q : Σ' fb : @FiberBundle B F _ _ E τ _,
      @VectorBundle κ B F E _ _ _ _ _ _ τ _ fb) :
    @FiberBundle.trivializationAtlas' B F _ _ E τ' _
        (Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F E) ↦
          Σ' fb : @FiberBundle B F _ _ E t _,
            @VectorBundle κ B F E _ _ _ _ _ _ t _ fb) hτ) q).1 =
      Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F E) ↦
        Set (@Trivialization B F (TotalSpace F E) _ _ t (π F E))) hτ)
        (@FiberBundle.trivializationAtlas' B F _ _ E τ _ q.1) := by
  cases hτ
  rfl

end BundleCast

section TrivializationCast

variable {B : Type uB} {F : Type uF} {Z : Type uX}
  [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}
  {τ τ' : TopologicalSpace Z}

/-- Casting the domain topology preserves the whole underlying partial equivalence. -/
private theorem trivialization_cast_toPartialEquiv (hτ : τ = τ')
    (e : @Trivialization B F Z _ _ τ proj) :
    @PartialHomeomorph.toPartialEquiv Z (B × F) τ' inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph Z (B × F) τ' inferInstance
          (@Trivialization.toOpenPartialHomeomorph B F Z _ _ τ' proj
            (Eq.mp (congrArg (fun t : TopologicalSpace Z ↦
              @Trivialization B F Z _ _ t proj) hτ) e))) =
      @PartialHomeomorph.toPartialEquiv Z (B × F) τ inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph Z (B × F) τ inferInstance
          (@Trivialization.toOpenPartialHomeomorph B F Z _ _ τ proj e)) := by
  cases hτ
  rfl

/-- Casting the domain topology preserves the chart's base set. -/
private theorem trivialization_cast_baseSet (hτ : τ = τ')
    (e : @Trivialization B F Z _ _ τ proj) :
    @Trivialization.baseSet B F Z _ _ τ' proj
        (Eq.mp (congrArg (fun t : TopologicalSpace Z ↦
          @Trivialization B F Z _ _ t proj) hτ) e) =
      @Trivialization.baseSet B F Z _ _ τ proj e := by
  cases hτ
  rfl

end TrivializationCast

end VectorBundle.Range

namespace VectorBundle

section TrivialBundleCharts

variable {κ : Type uκ} {B : Type uB} {F : Type uF} {H : Type uH}
  {E : B → Type uE} [NontriviallyNormedField κ] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace κ F]
  [TopologicalSpace H] [AddCommMonoid H] [Module κ H]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  [sourceTopology : TopologicalSpace (TotalSpace F E)]
  [sourceFB : FiberBundle F E] [sourceVB : VectorBundle κ F E]
  (L : ∀ b, E b →ₗ[κ] H)
  (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))

/-- The chosen chart of the range bundle is the transported source chart, with its
whole trivialization cast to the topology induced from the product. -/
theorem rangeBundle_trivializationAt (b : B) :
    @FiberBundle.trivializationAt' B F _ _ (fun b ↦ (L b).range)
        (rangeTotalSpaceTopology L) _ (rangeBundle L hI).1 b =
      Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
        @Trivialization B F (TotalSpace F (fun b ↦ (L b).range)) _ _ t
          (π F (fun b ↦ (L b).range)))
        (Range.totalSpaceTopology_trivial (F := F) L))
        (@Range.trivialization κ B F H E (Trivial B H)
          _ _ _ _ _ (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
          sourceTopology (Trivial.topologicalSpace B H) L
          ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
          (trivializationAt F E b)) := by
  unfold rangeBundle
  have hTopology := Range.totalSpaceTopology_trivial (F := F) L
  let canonQ := @Range.bundleOfIsEmbedding κ inferInstance B inferInstance
    F inferInstance inferInstance H inferInstance
    E inferInstance inferInstance inferInstance sourceTopology
    (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
    L sourceFB sourceVB (Trivial.fiberBundle B H)
    ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
  refine (Range.bundle_cast_trivializationAt hTopology canonQ b).trans ?_
  exact congrArg
    (Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
      @Trivialization B F (TotalSpace F (fun b ↦ (L b).range)) _ _ t
        (π F (fun b ↦ (L b).range))) hTopology))
    (@Range.bundleOfIsEmbedding_trivializationAt κ inferInstance B inferInstance
      F inferInstance inferInstance H inferInstance
      E inferInstance inferInstance inferInstance sourceTopology
      (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
      L ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
      sourceFB sourceVB (Trivial.fiberBundle B H) b)

/-- The full atlas of the range bundle is the image of the source atlas under chart
transport, cast to the topology induced from the product. -/
theorem rangeBundle_trivializationAtlas :
    @FiberBundle.trivializationAtlas' B F _ _ (fun b ↦ (L b).range)
        (rangeTotalSpaceTopology L) _ (rangeBundle L hI).1 =
      Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
        Set (@Trivialization B F (TotalSpace F (fun b ↦ (L b).range)) _ _ t
          (π F (fun b ↦ (L b).range))))
        (Range.totalSpaceTopology_trivial (F := F) L))
        ((@Range.trivialization κ B F H E (Trivial B H)
          _ _ _ _ _ (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
          sourceTopology (Trivial.topologicalSpace B H) L
          ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)) ''
          trivializationAtlas F E) := by
  unfold rangeBundle
  have hTopology := Range.totalSpaceTopology_trivial (F := F) L
  let canonQ := @Range.bundleOfIsEmbedding κ inferInstance B inferInstance
    F inferInstance inferInstance H inferInstance
    E inferInstance inferInstance inferInstance sourceTopology
    (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
    L sourceFB sourceVB (Trivial.fiberBundle B H)
    ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
  refine (Range.bundle_cast_trivializationAtlas hTopology canonQ).trans ?_
  exact congrArg
    (Eq.mp (congrArg (fun t : TopologicalSpace (TotalSpace F (fun b ↦ (L b).range)) ↦
      Set (@Trivialization B F (TotalSpace F (fun b ↦ (L b).range)) _ _ t
        (π F (fun b ↦ (L b).range)))) hTopology))
    (@Range.bundleOfIsEmbedding_trivializationAtlas κ inferInstance B inferInstance
      F inferInstance inferInstance H inferInstance
      E inferInstance inferInstance inferInstance sourceTopology
      (Trivial B H) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance) (Trivial.topologicalSpace B H)
      L ((Trivial.homeomorphProd B H).symm.isEmbedding.comp hI)
      sourceFB sourceVB (Trivial.fiberBundle B H))

end TrivialBundleCharts

end VectorBundle
