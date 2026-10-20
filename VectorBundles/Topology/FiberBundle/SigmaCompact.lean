/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.LocalAtTarget

/-!
# Sigma-compactness of fiber-bundle total spaces

A fiber bundle over an R₁ sigma-compact base with a sigma-compact model has
sigma-compact total space. The given topologies on the base, model, total space,
and individual fibers, together with their coupled `FiberBundle` structure, are retained.
No separation assumption on the model or total space, or nonemptiness assumption on
any of these spaces, is required.

## References

* Mathlib's `IsCompact.finite_compact_cover` gives compact refinements of finite
  open covers in R₁ spaces.
* Mathlib's `Bundle.Trivialization.preimageHomeomorph` identifies a chart-supported
  preimage with the product of the base subset and the model.
* Mathlib's `SigmaCompactSpace`, compact-product and continuous-image APIs, and
  `isSigmaCompact_univ_iff` provide the sigma-compactness framework.
-/

@[expose] public section

open Bundle

universe uB uF uE

namespace FiberBundle

/-- The total space of a fiber bundle with sigma-compact base and model is sigma-compact
when the base is R₁. -/
instance sigmaCompactSpace
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [R1Space B] [SigmaCompactSpace B] [SigmaCompactSpace F] :
    SigmaCompactSpace (TotalSpace F E) := by
  classical
  -- A compact base subset inside a chart gives a sigma-compact product, using its
  -- inherited subtype topology and the original bundle trivialization.
  have hpreimage {K : Set B} (hK : IsCompact K) (b : B)
      (hKb : K ⊆ (trivializationAt F E b).baseSet) :
      IsSigmaCompact ((π F E) ⁻¹' K) := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [isSigmaCompact_iff_isSigmaCompact_univ]
    simpa only [Set.image_univ_of_surjective
      ((trivializationAt F E b).preimageHomeomorph hKb).symm.surjective] using
      (isSigmaCompact_univ : IsSigmaCompact (Set.univ : Set (K × F))).image
        ((trivializationAt F E b).preimageHomeomorph hKb).symm.continuous
  have hcompact (K : Set B) (hK : IsCompact K) :
      IsSigmaCompact ((π F E) ⁻¹' K) := by
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun b : B ↦ (trivializationAt F E b).baseSet)
      (fun b ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ Set.mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F E b⟩)
    -- R₁ compact refinement avoids requiring compact subsets to be ambient closed.
    obtain ⟨L, hLcompact, hLsub, hLcover⟩ := hK.finite_compact_cover t
      (fun b : B ↦ (trivializationAt F E b).baseSet)
      (fun b _ ↦ (trivializationAt F E b).open_baseSet) ht
    rw [hLcover]
    simp only [Set.preimage_iUnion]
    exact isSigmaCompact_biUnion t.countable_toSet
      (fun b _ ↦ hpreimage (hLcompact b) b (hLsub b))
  apply isSigmaCompact_univ_iff.mp
  simpa only [← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ] using
    isSigmaCompact_iUnion (fun n : ℕ ↦ (π F E) ⁻¹' compactCovering B n)
      (fun n ↦ hcompact _ (isCompact_compactCovering B n))

end FiberBundle

namespace Bundle.Trivialization

universe uZ

/-- A chart of a sigma-compact space has sigma-compact model if its base set contains a
closed nonempty subset and its original projection is continuous. No separation assumption
on the base or model is needed. -/
theorem sigmaCompactSpace_model_of_isClosed
    {B : Type uB} {Z : Type uZ} {F : Type uF}
    [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace F]
    {p : Z → B} (e : Trivialization F p) (hp : Continuous p)
    [SigmaCompactSpace Z] {s : Set B} (hs : IsClosed s) (hne : s.Nonempty)
    (hsub : s ⊆ e.baseSet) : SigmaCompactSpace F := by
  let : SigmaCompactSpace (p ⁻¹' s) := (hs.preimage hp).sigmaCompactSpace
  let : SigmaCompactSpace (s × F) := isSigmaCompact_univ_iff.mp (by
    simpa only [(e.preimageHomeomorph hsub).surjective.range_eq] using
      isSigmaCompact_range (e.preimageHomeomorph hsub).continuous)
  obtain ⟨b, hb⟩ := hne
  have hsurj : Function.Surjective (Prod.snd : s × F → F) :=
    fun y ↦ ⟨(⟨b, hb⟩, y), rfl⟩
  apply isSigmaCompact_univ_iff.mp
  simpa only [hsurj.range_eq] using
    isSigmaCompact_range (continuous_snd : Continuous (Prod.snd : s × F → F))

end Bundle.Trivialization

namespace FiberBundle

/-- If the original total space of a fiber bundle is sigma-compact and the base is R₀,
then the model is sigma-compact at any specified base point. The model may be empty. -/
theorem sigmaCompactSpace_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [R0Space B] [SigmaCompactSpace (TotalSpace F E)] (b : B) :
    SigmaCompactSpace F := by
  refine (trivializationAt F E b).sigmaCompactSpace_model_of_isClosed
    (continuous_proj F E) (isClosed_closure : IsClosed (closure ({b} : Set B)))
    ⟨b, subset_closure (by rfl)⟩ ?_
  intro y hy
  have hby : b ⤳ y := specializes_iff_mem_closure.mpr hy
  exact hby.symm.mem_open (trivializationAt F E b).open_baseSet
    (mem_baseSet_trivializationAt F E b)

/-- For a fiber bundle over a nonempty R₁ base with nonempty model, the original total space
is sigma-compact exactly when the base and model are both sigma-compact. -/
theorem sigmaCompactSpace_totalSpace_iff
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [R1Space B] [Nonempty B] [Nonempty F] :
    SigmaCompactSpace (TotalSpace F E) ↔ SigmaCompactSpace B ∧ SigmaCompactSpace F := by
  constructor
  · intro h
    let : SigmaCompactSpace (TotalSpace F E) := h
    have hB : SigmaCompactSpace B := by
      apply isSigmaCompact_univ_iff.mp
      simpa only [(surjective_proj F E).range_eq] using
        isSigmaCompact_range (continuous_proj F E)
    exact ⟨hB, sigmaCompactSpace_model F E (Classical.choice ‹Nonempty B›)⟩
  · rintro ⟨hB, hF⟩
    let : SigmaCompactSpace B := hB
    let : SigmaCompactSpace F := hF
    exact FiberBundle.sigmaCompactSpace F E

end FiberBundle

namespace FiberBundle

private theorem isSigmaCompact_preimage_of_isCompact_of_monotone_closed_compact_cover
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E]
    (K : ℕ → Set F) (hclosed : ∀ n, IsClosed (K n))
    (hcompact : ∀ n, IsCompact (K n)) (hmono : Monotone K)
    (hcover : ∀ v, ∃ n, v ∈ K n) (s : Set B) (hs : IsCompact s) :
    IsSigmaCompact ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' s) := by
  classical
  let p : Bundle.TotalSpace F E → B := Bundle.TotalSpace.proj
  let X := p ⁻¹' s
  let q : X → s := fun x => ⟨p x.1, x.2⟩
  have hq : Continuous q :=
    ((FiberBundle.continuous_proj (F := F) (E := E)).comp
      continuous_subtype_val).subtype_mk _
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover
    (fun b => (FiberBundle.trivializationAt F E b).baseSet)
    (fun b => (FiberBundle.trivializationAt F E b).open_baseSet) (by
      intro b hb
      exact Set.mem_iUnion.mpr ⟨b, FiberBundle.mem_baseSet_trivializationAt F E b⟩)
  let I := {b : B // b ∈ t}
  let : Fintype I := inferInstance
  let e (i : I) := FiberBundle.trivializationAt F E i.1
  let V (i : I) : TopologicalSpace.Opens s :=
    ⟨(Subtype.val : s → B) ⁻¹' (e i).baseSet,
      (e i).open_baseSet.preimage continuous_subtype_val⟩
  have hV : ∀ b : s, ∃ i : I, b ∈ V i := by
    intro b
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht b.2)
    obtain ⟨hit, hbi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, hit⟩, hbi⟩
  have hVcover : TopologicalSpace.IsOpenCover V := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro b _
    obtain ⟨i, hi⟩ := hV b
    exact (le_iSup V i) hi
  let S (i : I) : Set B := s ∩ (e i).baseSet
  let H (i : I) := (e i).preimageHomeomorph (s := S i) (fun _ h => h.2)
  have hHapply (i : I) (x : p ⁻¹' S i) :
      H i x = (⟨p x.1, x.2⟩, (e i x.1).2) := by
    exact (e i).preimageHomeomorph_apply (fun _ h => h.2) x
  let lift (i : I) (z : V i × F) : S i × F :=
    (⟨z.1.1.1, z.1.1.2, z.1.2⟩, z.2)
  let inv (i : I) (z : V i × F) : X :=
    ⟨((H i).symm (lift i z)).1, ((H i).symm (lift i z)).2.1⟩
  have hlift (i : I) : Continuous (lift i) := by
    have hc : Continuous (fun z : V i × F => z.1.1.1) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    exact (hc.subtype_mk _).prodMk continuous_snd
  have hinv (i : I) : Continuous (inv i) :=
    (continuous_subtype_val.comp ((H i).symm.continuous.comp (hlift i))).subtype_mk _
  have hinv_proj (i : I) (z : V i × F) : q (inv i z) = z.1.1 := by
    apply Subtype.ext
    have hh := congrArg (fun w : S i × F => w.1.1)
      ((H i).apply_symm_apply (lift i z))
    rw [hHapply] at hh
    simpa only [lift, inv, q] using hh
  have hinv_coord (i : I) (z : V i × F) : (e i (inv i z).1).2 = z.2 := by
    have hh := congrArg (fun w : S i × F => w.2)
      ((H i).apply_symm_apply (lift i z))
    rw [hHapply] at hh
    simpa only [lift, inv] using hh
  have hinv_recover (i : I) (x : X) (hx : q x ∈ V i) :
      inv i (⟨q x, hx⟩, (e i x.1).2) = x := by
    apply Subtype.ext
    have hh := congrArg Subtype.val ((H i).symm_apply_apply
      (⟨x.1, x.2, hx⟩ : p ⁻¹' S i))
    rw [hHapply] at hh
    simpa only [lift, inv, q] using hh
  let T (n : ℕ) : Set X := {x | ∀ i : I, q x ∈ V i → (e i x.1).2 ∈ K n}
  have hTclosed (n : ℕ) : IsClosed (T n) := by
    have hbad (i : I) :
        IsOpen {x : X | q x ∈ V i ∧ (e i x.1).2 ∉ K n} := by
      have hh := (e i).continuousOn.snd.isOpen_inter_preimage
        (e i).open_source (hclosed n).isOpen_compl
      have hh' : IsOpen {x : Bundle.TotalSpace F E |
          p x ∈ (e i).baseSet ∧ (e i x).2 ∉ K n} := by
        have heq : {x : Bundle.TotalSpace F E |
            p x ∈ (e i).baseSet ∧ (e i x).2 ∉ K n} =
            (e i).source ∩ (fun x => (e i x).2) ⁻¹' (K n)ᶜ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_compl_iff, (e i).mem_source, p]
        rw [heq]
        exact hh
      exact hh'.preimage continuous_subtype_val
    have heq : (T n)ᶜ = ⋃ i : I,
        {x : X | q x ∈ V i ∧ (e i x.1).2 ∉ K n} := by
      ext x
      simp only [T, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hn⟩
        exact ⟨i, hi, hn⟩
      · rintro ⟨i, hi, hn⟩
        exact ⟨i, hi, hn⟩
    apply isOpen_compl_iff.mp
    rw [heq]
    exact isOpen_iUnion hbad
  have hTcover : ⋃ n, T n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hidx : ∀ i : I, ∃ n, q x ∈ V i → (e i x.1).2 ∈ K n := by
      intro i
      by_cases hi : q x ∈ V i
      · obtain ⟨n, hn⟩ := hcover ((e i x.1).2)
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun h => False.elim (hi h)⟩
    choose f hf using hidx
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup f, ?_⟩
    intro i hi
    exact hmono (Finset.le_sup (Finset.mem_univ i)) (hf i hi)
  have hTcompact (n : ℕ) : IsCompact (T n) := by
    let : CompactSpace s := isCompact_iff_compactSpace.mp hs
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hcompact n)
    let r : T n → s := fun x => q x.1
    have hr : Continuous r := hq.comp continuous_subtype_val
    have hrclosed : IsClosedMap r := by
      intro A hA
      let A₀ : Set X := Subtype.val '' A
      have hA₀ : IsClosed A₀ := (hTclosed n).isClosedMap_subtype_val A hA
      apply hVcover.isClosed_iff_coe_preimage.mpr
      intro i
      let j : V i × K n → V i × F := fun z => (z.1, z.2.1)
      have hj : Continuous j :=
        continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
      let Q : Set (V i × K n) := (inv i ∘ j) ⁻¹' A₀
      have hQ : IsClosed Q := hA₀.preimage ((hinv i).comp hj)
      have hfst : IsClosed (Prod.fst '' Q) := isClosedMap_fst_of_compactSpace Q hQ
      have heq : (Subtype.val : V i → s) ⁻¹' (r '' A) = Prod.fst '' Q := by
        ext b
        constructor
        · rintro ⟨x, hx, hxb⟩
          have hactive : q x.1 ∈ V i := by
            rw [show q x.1 = b.1 from hxb]
            exact b.2
          have hk : (e i x.1.1).2 ∈ K n := x.2 i hactive
          refine ⟨(b, ⟨(e i x.1.1).2, hk⟩), ?_, rfl⟩
          change inv i (b, (e i x.1.1).2) ∈ A₀
          have hb : b = (⟨q x.1, hactive⟩ : V i) := by
            apply Subtype.ext
            exact hxb.symm
          rw [hb, hinv_recover]
          exact ⟨x, hx, rfl⟩
        · rintro ⟨z, hz, hzb⟩
          obtain ⟨x, hx, hxeq⟩ := hz
          refine ⟨x, hx, ?_⟩
          change q x.1 = b.1
          rw [hxeq]
          exact (hinv_proj i (j z)).trans (congrArg Subtype.val hzb)
      rw [heq]
      exact hfst
    have hrfiber (b : s) : IsCompact (r ⁻¹' {b}) := by
      obtain ⟨i, hi⟩ := hV b
      let b' : V i := ⟨b, hi⟩
      let D : Set (K n) := {k | inv i (b', k.1) ∈ T n}
      have hD : IsClosed D := (hTclosed n).preimage
        ((hinv i).comp (continuous_const.prodMk continuous_subtype_val))
      let f : D → T n := fun k => ⟨inv i (b', k.1.1), k.2⟩
      have hf : Continuous f :=
        ((hinv i).comp (continuous_const.prodMk
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _
      have heq : r ⁻¹' {b} = f '' Set.univ := by
        ext x
        constructor
        · intro hx
          have hxb : q x.1 = b := hx
          have hactive : q x.1 ∈ V i := by simpa only [hxb] using hi
          have hk : (e i x.1.1).2 ∈ K n := x.2 i hactive
          have hb : b' = (⟨q x.1, hactive⟩ : V i) := by
            apply Subtype.ext
            exact hxb.symm
          have hrec : inv i (b', (e i x.1.1).2) = x.1 := by
            rw [hb, hinv_recover]
          refine ⟨⟨⟨(e i x.1.1).2, hk⟩, ?_⟩, Set.mem_univ _, ?_⟩
          · change inv i (b', (e i x.1.1).2) ∈ T n
            rw [hrec]
            exact x.2
          · apply Subtype.ext
            exact hrec
        · rintro ⟨k, _, rfl⟩
          exact hinv_proj i (b', k.1.1)
      rw [heq]
      let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
      exact isCompact_univ.image hf
    have hproper : IsProperMap r :=
      isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hr, hrclosed, hrfiber⟩
    have hu : IsCompact (Set.univ : Set (T n)) := by
      simpa only [Set.preimage_univ] using hproper.isCompact_preimage
        (isCompact_univ : IsCompact (Set.univ : Set s))
    have himage : (Subtype.val : T n → X) '' Set.univ = T n := by
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    rw [← himage]
    exact hu.image (continuous_subtype_val : Continuous (Subtype.val : T n → X))
  apply isSigmaCompact_iff_isSigmaCompact_univ.mpr
  rw [← hTcover]
  exact isSigmaCompact_iUnion_of_isCompact T hTcompact

/-- A fiber bundle over a sigma-compact base has sigma-compact total space if its model
has a countable cover by closed compact sets. This sufficient condition retains all given
topologies and the coupled bundle structure, without separation or nonemptiness assumptions. -/
theorem sigmaCompactSpace_of_countable_closed_compact_cover
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SigmaCompactSpace B]
    (K : ℕ → Set F) (hclosed : ∀ n, IsClosed (K n))
    (hcompact : ∀ n, IsCompact (K n)) (hcover : ⋃ n, K n = Set.univ) :
    SigmaCompactSpace (Bundle.TotalSpace F E) := by
  classical
  let L (n : ℕ) : Set F := ⋃ m ∈ Finset.range (n + 1), K m
  have hLclosed (n : ℕ) : IsClosed (L n) :=
    isClosed_biUnion_finset (fun m _ => hclosed m)
  have hLcompact (n : ℕ) : IsCompact (L n) :=
    (Finset.range (n + 1)).isCompact_biUnion (fun m _ => hcompact m)
  have hLmono : Monotone L := by
    intro m n hmn v hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hkm, hkv⟩ := Set.mem_iUnion.mp hk
    refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨?_, hkv⟩⟩
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hkm) (Nat.add_le_add_right hmn 1))
  have hLcover (v : F) : ∃ n, v ∈ L n := by
    have hv : v ∈ ⋃ n, K n := by rw [hcover]; exact Set.mem_univ v
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    exact ⟨n, Set.mem_iUnion.mpr ⟨n,
      Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hn⟩⟩⟩
  apply isSigmaCompact_univ_iff.mp
  have hpre (j : ℕ) : IsSigmaCompact
      ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' compactCovering B j) :=
    isSigmaCompact_preimage_of_isCompact_of_monotone_closed_compact_cover F E
      L hLclosed hLcompact hLmono hLcover (compactCovering B j)
      (isCompact_compactCovering B j)
  have heq : (⋃ j, (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹'
      compactCovering B j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_mem_compactCovering x.proj
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  rw [← heq]
  exact isSigmaCompact_iUnion _ hpre

/-- A fiber bundle with sigma-compact base and R₁ sigma-compact model has sigma-compact
total space. This is a sufficient condition on the model, with no separation assumption on
the base and no nonemptiness assumption; all given topologies and bundle data are retained. -/
theorem sigmaCompactSpace_of_r1Space_model
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SigmaCompactSpace B] [R1Space F] [SigmaCompactSpace F] :
    SigmaCompactSpace (Bundle.TotalSpace F E) := by
  exact sigmaCompactSpace_of_countable_closed_compact_cover F E
    (fun n => closure (compactCovering F n))
    (fun _ => isClosed_closure)
    (fun n => (isCompact_compactCovering F n).closure)
    (iUnion_closure_compactCovering F)

end FiberBundle
