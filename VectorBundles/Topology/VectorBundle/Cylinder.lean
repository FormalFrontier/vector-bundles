/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinder
public import VectorBundles.Topology.FiberBundle.Pullback
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Linear trivializations near a compact cylinder

A vector bundle over `X × unitInterval` admits, near each `x : X`, a single
fiberwise-linear trivialization whose base set contains a product of an open
neighborhood of `x` with the whole time interval. The space `X` is arbitrary.

`VectorBundle.cylinderTrivialization` chooses the trivialization together with
its linearity condition. `VectorBundle.cylinderTrivializationNhds` is an open
neighborhood on which that same chart is valid at every time. Forward maps,
inverses, and restrictions to closed subsets use `Bundle.Trivialization`'s API,
in particular `preimageHomeomorph`; they do not require a separate bundle object.

## Implementation notes

The scalar field and normed model space have the hypotheses of Mathlib's
`VectorBundle` class. The fibers need only their given additive, module, and
topological structures. There is no completeness or dimension assumption, and
no separation, paracompactness, or nonemptiness assumption on `X`. This is a
local triviality statement, not an endpoint-isomorphism or classification theorem.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.7, preliminary fact (2), printed pp. 20–21.
* Mathlib's `FiberBundle.exists_trivialization_Icc_subset` gives the topological,
  nonparameterized interval statement. Its conclusion does not assert linearity.
* Mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval` supplies a finite
  closed-interval subdivision subordinate to an open cover. Adjacent restricted
  charts are combined by `Bundle.Trivialization.glueClosedCylinder` and its
  fiberwise-linearity theorem.
-/

@[expose] public section

open Bundle Set TopologicalSpace Topology

universe uX uK uF uE uB uC

namespace VectorBundle

section RestrictedCharts

variable {B : Type uB} {C : Type uC} {F : Type uF} {E : B → Type uE}
  [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)]

private noncomputable def pullbackRestrictedChart {f : C → B} (hf : IsEmbedding f)
    (hp : Continuous (π F E)) {s : Set B} (hs : s ⊆ range f)
    (h : ((π F E) ⁻¹' s) ≃ₜ s × F) :
    ((π F (f *ᵖ E)) ⁻¹' (f ⁻¹' s)) ≃ₜ (f ⁻¹' s) × F :=
  ((Bundle.Pullback.isEmbedding_lift F E f hf hp).homeomorphOfSubsetRange
    ((preimage_mono hs).trans (Bundle.Pullback.range_lift F E f).ge)).trans
    (h.trans ((hf.homeomorphOfSubsetRange hs).symm.prodCongr (Homeomorph.refl F)))

private theorem pullbackRestrictedChart_fst {f : C → B} (hf : IsEmbedding f)
    (hp : Continuous (π F E)) {s : Set B} (hs : s ⊆ range f)
    (h : ((π F E) ⁻¹' s) ≃ₜ s × F)
    (hh : ∀ z, (h z).1.val = z.val.proj)
    (z : (π F (f *ᵖ E)) ⁻¹' (f ⁻¹' s)) :
    (pullbackRestrictedChart hf hp hs h z).1.val = z.val.proj := by
  let g := hf.homeomorphOfSubsetRange hs
  have he : (pullbackRestrictedChart hf hp hs h z).1 = ⟨z.val.proj, z.property⟩ := by
    apply g.injective
    change g (g.symm _) = _
    rw [g.apply_symm_apply]
    apply Subtype.ext
    exact hh _
  exact congrArg Subtype.val he

private noncomputable def descendRestrictedChart {f : C → B} (hf : IsEmbedding f)
    (hp : Continuous (π F E)) {s : Set B} (hs : s ⊆ range f)
    (e : Trivialization F (π F (f *ᵖ E))) (he : f ⁻¹' s ⊆ e.baseSet) :
    ((π F E) ⁻¹' s) ≃ₜ s × F :=
  ((Bundle.Pullback.isEmbedding_lift F E f hf hp).homeomorphOfSubsetRange
    ((preimage_mono hs).trans (Bundle.Pullback.range_lift F E f).ge)).symm.trans
    ((e.preimageHomeomorph he).trans
      ((hf.homeomorphOfSubsetRange hs).prodCongr (Homeomorph.refl F)))

private theorem descendRestrictedChart_fst {f : C → B} (hf : IsEmbedding f)
    (hp : Continuous (π F E)) {s : Set B} (hs : s ⊆ range f)
    (e : Trivialization F (π F (f *ᵖ E))) (he : f ⁻¹' s ⊆ e.baseSet)
    (z : (π F E) ⁻¹' s) :
    (descendRestrictedChart hf hp hs e he z).1.val = z.val.proj := by
  let D := (Bundle.Pullback.isEmbedding_lift F E f hf hp).homeomorphOfSubsetRange
    ((preimage_mono hs).trans (Bundle.Pullback.range_lift F E f).ge)
  have hz := congrArg (fun q ↦ q.val.proj) (D.apply_symm_apply z)
  change f (D.symm z).val.proj = z.val.proj at hz
  change ((hf.homeomorphOfSubsetRange hs)
    (e.preimageHomeomorph he (D.symm z)).1).val = z.val.proj
  rw [IsEmbedding.homeomorphOfSubsetRange_apply_coe]
  erw [Trivialization.preimageHomeomorph_apply]
  exact hz

variable {K : Type uK} [Semiring K] [AddCommMonoid F] [Module K F]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]

private theorem descendRestrictedChart_linear {f : C → B} (hf : IsEmbedding f)
    (hp : Continuous (π F E)) {s : Set B} (hs : s ⊆ range f)
    (e : Trivialization F (π F (f *ᵖ E))) [e.IsLinear K]
    (he : f ⁻¹' s ⊆ e.baseSet) (b : B) (hb : b ∈ s) :
    IsLinearMap K (fun v : E b ↦ (descendRestrictedChart hf hp hs e he ⟨⟨b, v⟩, hb⟩).2) := by
  obtain ⟨c, rfl⟩ := hs hb
  let D := (Bundle.Pullback.isEmbedding_lift F E f hf hp).homeomorphOfSubsetRange
    ((preimage_mono hs).trans (Bundle.Pullback.range_lift F E f).ge)
  have hh (v : E (f c)) : D.symm ⟨⟨f c, v⟩, hb⟩ = ⟨⟨c, v⟩, hb⟩ := by
    apply D.injective
    rw [D.apply_symm_apply]
    rfl
  have hlin := e.linear K (he hb)
  change IsLinearMap K (fun v : E (f c) ↦ (e ⟨c, v⟩).2) at hlin
  have heq : (fun v : E (f c) ↦ (descendRestrictedChart hf hp hs e he ⟨⟨f c, v⟩, hb⟩).2) =
      (fun v : E (f c) ↦ (e ⟨c, v⟩).2) := by
    funext v
    change (e.preimageHomeomorph he (D.symm ⟨⟨f c, v⟩, hb⟩)).2 = _
    rw [hh]
    exact congrArg Prod.snd (e.preimageHomeomorph_apply he ⟨⟨c, v⟩, hb⟩)
  rw [heq]
  exact hlin

end RestrictedCharts

section Slab

variable {X : Type*} {F : Type*} {K : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [Semiring K]
    [AddCommMonoid F] [Module K F]
    {E : X × unitInterval → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]

private noncomputable def restrictedChartCongr {B Z : Type*}
    [TopologicalSpace B] [TopologicalSpace Z] {p : Z → B}
    {s t : Set B} (hst : s = t) (h : (p ⁻¹' s) ≃ₜ s × F) :
    (p ⁻¹' t) ≃ₜ t × F :=
  (Homeomorph.setCongr (congrArg (fun s ↦ p ⁻¹' s) hst)).symm.trans
    (h.trans ((Homeomorph.setCongr hst).prodCongr (Homeomorph.refl F)))

-- Transport the two proper closed restrictions to a pullback bundle before gluing.
-- No intermediate closed-slab chart is extended to an open ambient chart.
private theorem exists_linearChart_union_slabs (U : Set X) {a c b : unitInterval}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hp : Continuous (π F E))
    (h₀ : ((π F E) ⁻¹' (U ×ˢ Icc a c)) ≃ₜ (U ×ˢ Icc a c) × F)
    (h₁ : ((π F E) ⁻¹' (U ×ˢ Icc c b)) ≃ₜ (U ×ˢ Icc c b) × F)
    (hp₀ : ∀ z, (h₀ z).1.val = z.val.proj)
    (hp₁ : ∀ z, (h₁ z).1.val = z.val.proj)
    (hl₀ : ∀ q (hq : q ∈ U ×ˢ Icc a c),
      IsLinearMap K (fun v : E q ↦ (h₀ ⟨⟨q, v⟩, hq⟩).2))
    (hl₁ : ∀ q (hq : q ∈ U ×ˢ Icc c b),
      IsLinearMap K (fun v : E q ↦ (h₁ ⟨⟨q, v⟩, hq⟩).2)) :
    ∃ h : ((π F E) ⁻¹' (U ×ˢ Icc a b)) ≃ₜ (U ×ˢ Icc a b) × F,
      (∀ z, (h z).1.val = z.val.proj) ∧
      ∀ q (hq : q ∈ U ×ˢ Icc a b),
        IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
  let f : U × Icc a b → X × unitInterval := fun q ↦ (q.1.val, q.2.val)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal
  have hs₀ : U ×ˢ Icc a c ⊆ range f := by
    rintro ⟨x, t⟩ ⟨hx, hat, htc⟩
    exact ⟨(⟨x, hx⟩, ⟨t, hat, htc.trans hcb⟩), rfl⟩
  have hs₁ : U ×ˢ Icc c b ⊆ range f := by
    rintro ⟨x, t⟩ ⟨hx, hct, htb⟩
    exact ⟨(⟨x, hx⟩, ⟨t, hac.trans hct, htb⟩), rfl⟩
  have hs : U ×ˢ Icc a b ⊆ range f := by
    rintro ⟨x, t⟩ ⟨hx, hat, htb⟩
    exact ⟨(⟨x, hx⟩, ⟨t, hat, htb⟩), rfl⟩
  let cut : Icc a b := ⟨c, hac, hcb⟩
  have eq₀ : f ⁻¹' (U ×ˢ Icc a c) = {q : U × Icc a b | q.2 ≤ cut} := by
    ext q
    exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨q.1.property, q.2.property.1, h⟩⟩
  have eq₁ : f ⁻¹' (U ×ˢ Icc c b) = {q : U × Icc a b | cut ≤ q.2} := by
    ext q
    exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨q.1.property, h, q.2.property.2⟩⟩
  let H₀ := restrictedChartCongr eq₀ (pullbackRestrictedChart hf hp hs₀ h₀)
  let H₁ := restrictedChartCongr eq₁ (pullbackRestrictedChart hf hp hs₁ h₁)
  have HP₀ (z) : (H₀ z).1.val = z.val.proj :=
    pullbackRestrictedChart_fst hf hp hs₀ h₀ hp₀ ⟨z.val, eq₀.symm ▸ z.property⟩
  have HP₁ (z) : (H₁ z).1.val = z.val.proj :=
    pullbackRestrictedChart_fst hf hp hs₁ h₁ hp₁ ⟨z.val, eq₁.symm ▸ z.property⟩
  have HL₀ (q : U × Icc a b) (hq : q.2 ≤ cut) :
      IsLinearMap K (fun v : (f *ᵖ E) q ↦ (H₀ ⟨⟨q, v⟩, hq⟩).2) :=
    hl₀ (f q) ⟨q.1.property, q.2.property.1, hq⟩
  have HL₁ (q : U × Icc a b) (hq : cut ≤ q.2) :
      IsLinearMap K (fun v : (f *ᵖ E) q ↦ (H₁ ⟨⟨q, v⟩, hq⟩).2) :=
    hl₁ (f q) ⟨q.1.property, hq, q.2.property.2⟩
  let e := Trivialization.glueClosedCylinder cut (π F (f *ᵖ E)) H₀ H₁ HP₀ HP₁
    (Pullback.continuous_proj F E f)
  have : e.IsLinear K := Trivialization.glueClosedCylinder_isLinear cut H₀ H₁ HP₀ HP₁
    (Pullback.continuous_proj F E f) HL₀ HL₁
  have he : f ⁻¹' (U ×ˢ Icc a b) ⊆ e.baseSet := by
    rw [Trivialization.glueClosedCylinder_baseSet]
    exact subset_univ _
  exact ⟨descendRestrictedChart hf hp hs e he, descendRestrictedChart_fst hf hp hs e he,
    descendRestrictedChart_linear hf hp hs e he⟩

end Slab

section OpenChart

variable {B : Type*} {F : Type*} {K : Type*}
    [TopologicalSpace B] [TopologicalSpace F] [Semiring K]
    [AddCommMonoid F] [Module K F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]

-- Domain and codomain extension are used only when the entire base subset is open.
private theorem exists_trivialization_of_open_chart (s : Set B) (hs : IsOpen s) (hne : s.Nonempty)
    (hp : Continuous (π F E))
    (h : ((π F E) ⁻¹' s) ≃ₜ s × F)
    (hh : ∀ z, (h z).1.val = z.val.proj)
    (hl : ∀ q (hq : q ∈ s), IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2)) :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧ e.baseSet = s := by
  classical
  let e : Trivialization F (s.restrictPreimage (π F E)) :=
    { toOpenPartialHomeomorph := h.toOpenPartialHomeomorph
      baseSet := univ
      open_baseSet := isOpen_univ
      source_eq := by ext; simp
      target_eq := by simp
      proj_toFun := fun z _ ↦ Subtype.ext (hh z) }
  let g := (e.codExtend hs hne).domExtend (hs.preimage hp)
  have hg : g.baseSet = s := by
    change Subtype.val '' (univ : Set s) = s
    exact Subtype.coe_image_univ s
  refine ⟨g, ?_, hg⟩
  constructor
  intro q hq
  rw [hg] at hq
  have heq : (fun v : E q ↦ (g ⟨q, v⟩).2) =
      (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
    funext v
    change (if ht : q ∈ s then
      ((e.codExtend hs hne) ⟨⟨q, v⟩, ht⟩) else _).2 = _
    rw [dite_eq_left hq]
    rfl
  rw [heq]
  exact hl q hq

end OpenChart

section Cylinder

variable {X : Type uX} [TopologicalSpace X]
  (K : Type uK) [NontriviallyNormedField K]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
  (E : X × unitInterval → Type uE)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
  [FiberBundle F E] [VectorBundle K F E]

/-- A linear chart for a vector bundle over a cylinder contains a whole time
slice and a uniform open neighborhood of it. This is preliminary fact (2) in
Hatcher's proof of Proposition 1.7. -/
theorem exists_trivialization_cylinder (x : X) :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧
      ∃ U : OpenNhdsOf x, (U : Set X) ×ˢ (univ : Set unitInterval) ⊆ e.baseSet := by
  classical
  -- Linear atlas charts contain open product boxes along the central time slice.
  have boxes (t : unitInterval) : ∃ U V, IsOpen U ∧ IsOpen V ∧
      x ∈ U ∧ t ∈ V ∧ U ×ˢ V ⊆ (trivializationAt F E (x, t)).baseSet :=
    isOpen_prod_iff.mp (trivializationAt F E (x, t)).open_baseSet x t
      (mem_baseSet_trivializationAt F E (x, t))
  choose U V hU hV hxU htV hUV using boxes
  -- Only a finite prefix of the ordered subdivision is needed.
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hV
      (fun t _ ↦ mem_iUnion.mpr ⟨t, htV t⟩)
  choose i hi using hsub
  let W : Set X := ⋂ j ∈ Finset.range (N + 1), U (i j)
  have hW : IsOpen W := isOpen_biInter_finset fun j _ ↦ hU (i j)
  have hxW : x ∈ W := by
    simp only [W, mem_iInter]
    intro j _
    exact hxU (i j)
  have hWj (j : ℕ) (hj : j ≤ N) : W ⊆ U (i j) :=
    iInter₂_subset j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hp := FiberBundle.continuous_proj F E
  have cell (j : ℕ) (hj : j ≤ N) :
      ∃ h : ((π F E) ⁻¹' (W ×ˢ Icc (t j) (t (j + 1)))) ≃ₜ
          (W ×ˢ Icc (t j) (t (j + 1))) × F,
        (∀ z, (h z).1.val = z.val.proj) ∧
        ∀ q (hq : q ∈ W ×ˢ Icc (t j) (t (j + 1))),
          IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
    let e := trivializationAt F E (x, i j)
    have hs : W ×ˢ Icc (t j) (t (j + 1)) ⊆ e.baseSet :=
      fun q hq ↦ hUV (i j) ⟨hWj j hj hq.1, hi j hq.2⟩
    refine ⟨e.preimageHomeomorph hs, ?_, ?_⟩
    · intro z
      simp only [Trivialization.preimageHomeomorph_apply]
    · intro q hq
      simpa only [Trivialization.preimageHomeomorph_apply] using e.linear K (hs hq)
  -- Every induction step glues closed restrictions, including their inverses.
  have accumulated : ∀ n, n ≤ N →
      ∃ h : ((π F E) ⁻¹' (W ×ˢ Icc 0 (t (n + 1)))) ≃ₜ
          (W ×ˢ Icc 0 (t (n + 1))) × F,
        (∀ z, (h z).1.val = z.val.proj) ∧
        ∀ q (hq : q ∈ W ×ˢ Icc 0 (t (n + 1))),
          IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [← ht0]
      exact cell 0 (Nat.zero_le N)
    | succ n ih =>
      intro hn
      obtain ⟨h₀, hp₀, hl₀⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨h₁, hp₁, hl₁⟩ := cell (n + 1) hn
      exact exists_linearChart_union_slabs W bot_le (hmono (Nat.le_succ (n + 1))) hp
        h₀ h₁ hp₀ hp₁ hl₀ hl₁
  have whole : ∃ h : ((π F E) ⁻¹' (W ×ˢ (univ : Set unitInterval))) ≃ₜ
        (W ×ˢ (univ : Set unitInterval)) × F,
      (∀ z, (h z).1.val = z.val.proj) ∧
      ∀ q (hq : q ∈ W ×ˢ (univ : Set unitInterval)),
        IsLinearMap K (fun v : E q ↦ (h ⟨⟨q, v⟩, hq⟩).2) := by
    rw [unitInterval.univ_eq_Icc, ← hN (N + 1) (Nat.le_succ N)]
    exact accumulated N le_rfl
  obtain ⟨h, hh, hl⟩ := whole
  obtain ⟨e, he, hbase⟩ := exists_trivialization_of_open_chart (W ×ˢ (univ : Set unitInterval))
    (hW.prod isOpen_univ) ⟨(x, 0), hxW, mem_univ _⟩ hp h hh hl
  refine ⟨e, he, ⟨⟨⟨W, hW⟩, hxW⟩, ?_⟩⟩
  rw [hbase]
  exact subset_rfl

/-- A fiberwise-linear trivialization valid near the entire time slice over `x`.
The choice includes linearity, not just the underlying topological chart. -/
noncomputable def cylinderTrivialization (x : X) : Trivialization F (π F E) :=
  Classical.choose (exists_trivialization_cylinder K F E x)

/-- The chosen cylinder chart is linear on every fiber in its base set. -/
instance cylinderTrivialization_isLinear (x : X) :
    (cylinderTrivialization K F E x).IsLinear K := by
  exact (Classical.choose_spec (exists_trivialization_cylinder K F E x)).1

/-- An open neighborhood of `x` on which the chosen chart works for all times. -/
noncomputable def cylinderTrivializationNhds (x : X) : OpenNhdsOf x :=
  Classical.choose (Classical.choose_spec (exists_trivialization_cylinder K F E x)).2

/-- The entire product neighborhood lies in the base set of the chosen chart. -/
theorem cylinderTrivializationNhds_prod_subset (x : X) :
    (cylinderTrivializationNhds K F E x : Set X) ×ˢ (univ : Set unitInterval) ⊆
      (cylinderTrivialization K F E x).baseSet := by
  exact Classical.choose_spec
    (Classical.choose_spec (exists_trivialization_cylinder K F E x)).2

/-- Every time over a point of the chosen open neighborhood belongs to the chart. -/
theorem mem_cylinderTrivialization_baseSet (x : X) {y : X}
    (hy : y ∈ cylinderTrivializationNhds K F E x) (t : unitInterval) :
    (y, t) ∈ (cylinderTrivialization K F E x).baseSet := by
  exact cylinderTrivializationNhds_prod_subset K F E x ⟨hy, mem_univ t⟩

/-- The chosen chart contains the whole time slice over its center. -/
theorem mem_cylinderTrivialization_baseSet_self (x : X) (t : unitInterval) :
    (x, t) ∈ (cylinderTrivialization K F E x).baseSet := by
  exact mem_cylinderTrivialization_baseSet K F E x
    (cylinderTrivializationNhds K F E x).mem t

end Cylinder

section Interval

variable (K : Type uK) [NontriviallyNormedField K]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
  (E : unitInterval → Type uE)
  [TopologicalSpace (TotalSpace F E)] [∀ t, TopologicalSpace (E t)]
  [∀ t, AddCommMonoid (E t)] [∀ t, Module K (E t)]
  [FiberBundle F E] [VectorBundle K F E]

/-- A vector bundle over the unit interval has a global linear trivialization.
Forgetting linearity gives the conclusion of
`FiberBundle.exists_trivialization_Icc_subset F E 0 1`, since the closed interval
between these endpoints is the whole base. No equality of chosen charts is asserted. -/
theorem exists_linearTrivialization_unitInterval :
    ∃ e : Trivialization F (π F E), e.IsLinear K ∧ e.baseSet = univ := by
  let f : C(PUnit.{1} × unitInterval, unitInterval) := ⟨Prod.snd, continuous_snd⟩
  let E' := (f : PUnit.{1} × unitInterval → unitInterval) *ᵖ E
  let h : @Homeomorph (TotalSpace F E) (TotalSpace F E')
      ‹TopologicalSpace (TotalSpace F E)› (Pullback.TotalSpace.topologicalSpace F E f) :=
    { toFun := fun z ↦ ⟨(PUnit.unit, z.proj), z.2⟩
      invFun := Pullback.lift f
      left_inv := fun _ ↦ rfl
      right_inv := by rintro ⟨⟨u, t⟩, v⟩; cases u; rfl
      continuous_toFun := by
        apply (inducing_pullbackTotalSpaceEmbedding F E f).continuous_iff.mpr
        exact (continuous_const.prodMk (FiberBundle.continuous_proj F E)).prodMk continuous_id
      continuous_invFun := Pullback.continuous_lift F E f }
  obtain ⟨e, he, U, hU⟩ := exists_trivialization_cylinder K F E' PUnit.unit
  let e' : Trivialization F (π F E) :=
    (e.compHomeomorph h).homeomorphComp (Homeomorph.punitProd unitInterval)
  have hbase (t : unitInterval) : (PUnit.unit, t) ∈ e.baseSet :=
    hU ⟨U.mem, mem_univ t⟩
  refine ⟨e', ?_, ?_⟩
  · let := he
    constructor
    intro t _
    exact e.linear K (hbase t)
  · exact eq_univ_iff_forall.mpr hbase

end Interval

end VectorBundle
