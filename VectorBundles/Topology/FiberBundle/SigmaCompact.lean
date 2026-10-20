/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.Compactness.NhdsKer
import VectorBundles.Topology.CompactOpen
import VectorBundles.Topology.FiberBundle.CoordChange
import VectorBundles.Topology.Maps.Proper

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Sets.Compacts

/-!
# Sigma-compactness of fiber-bundle total spaces

A fiber bundle over an R₁ sigma-compact base with a sigma-compact model has
sigma-compact total space. The given topologies on the base, model, total space,
and individual fibers, together with their coupled `FiberBundle` structure, are retained.
No separation assumption on the model or total space, or nonemptiness assumption on
any of these spaces, is required.

A quasi-separated model with a countable compact-open cover also gives sigma-compact
total space, without a separation assumption on the base. The theorem
`sigmaCompactSpace_of_countable_open_compact_cover` needs no separate sigma-compactness
assumption on the model, since the cover already implies it.

Another sufficient condition is a sigma-compact, quasi-separated model covered by open
neighborhood kernels of singletons. The theorem
`sigmaCompactSpace_of_open_nhdsKer_cover` requires neither separation of the base nor
openness of every singleton kernel, and does not require countably many distinct kernels.

## References

* Mathlib's `IsCompact.finite_compact_cover` gives compact refinements of finite
  open covers in R₁ spaces.
* Mathlib's `Bundle.Trivialization.preimageHomeomorph` identifies a chart-supported
  preimage with the product of the base subset and the model.
* Mathlib's `SigmaCompactSpace`, compact-product and continuous-image APIs, and
  `isSigmaCompact_univ_iff` provide the sigma-compactness framework.
* Mathlib's `CompactOpens`, `nhdsKer` and `QuasiSeparatedSpace` give the compact-open
  covers, neighborhood kernels and compact-open intersection conditions on the model.
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

section CompactOpenConstraints

open Filter
open scoped Topology

universe uZc uIc

variable {B : Type uB} {F : Type uF} {Z : Type uZc} {I : Type uIc}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z] {p : Z → B}

/-- The inverse chart on the product with its original base-set subtype. -/
private def constraintChartInverse (e : Trivialization F p) (q : e.baseSet × F) : Z :=
  ((e.preimageHomeomorph (s := e.baseSet) subset_rfl).symm q).val

private theorem continuous_constraintChartInverse (e : Trivialization F p) :
    Continuous (constraintChartInverse e) :=
  continuous_subtype_val.comp
    (e.preimageHomeomorph (s := e.baseSet) subset_rfl).symm.continuous

private theorem constraintChartInverse_proj (e : Trivialization F p)
    (q : e.baseSet × F) : p (constraintChartInverse e q) = q.1.val := by
  have h := congrArg (fun w : e.baseSet × F ↦ w.1.val)
    ((e.preimageHomeomorph (s := e.baseSet) subset_rfl).apply_symm_apply q)
  rw [e.preimageHomeomorph_apply] at h
  exact h

private theorem constraintChartInverse_coord (e : Trivialization F p)
    (q : e.baseSet × F) : (e (constraintChartInverse e q)).2 = q.2 := by
  have h := congrArg (fun w : e.baseSet × F ↦ w.2)
    ((e.preimageHomeomorph (s := e.baseSet) subset_rfl).apply_symm_apply q)
  rw [e.preimageHomeomorph_apply] at h
  exact h

/-- The inverse chart recovers a point whose projection lies in its base set. -/
private theorem constraintChartInverse_apply (e : Trivialization F p) (z : Z)
    (hz : p z ∈ e.baseSet) :
    constraintChartInverse e (⟨p z, hz⟩, (e z).2) = z := by
  have h := congrArg Subtype.val
    ((e.preimageHomeomorph (s := e.baseSet) subset_rfl).symm_apply_apply
      (⟨z, hz⟩ : p ⁻¹' e.baseSet))
  rw [e.preimageHomeomorph_apply] at h
  exact h

private theorem coordChange_constraintChartInverse (e e' : Trivialization F p)
    (q : e.baseSet × F) :
    e.coordChange e' q.1.val q.2 = (e' (constraintChartInverse e q)).2 := by
  have hb : p (constraintChartInverse e q) ∈ e.baseSet := by
    rw [constraintChartInverse_proj e q]
    exact q.1.property
  have h := e.coordChange_apply_snd e' hb
  rw [constraintChartInverse_proj e q, constraintChartInverse_coord] at h
  exact h

/-- The active chart's constraint is the image of `A` under the reverse coordinate change. -/
private theorem mem_map_coordChange_iff (e e' : Trivialization F p)
    (A : TopologicalSpace.CompactOpens F) (b : e.baseSet)
    (hb : b.val ∈ e'.baseSet) (y : F) :
    y ∈ A.map (e'.coordChangeHomeomorph e hb b.property)
      (e'.coordChangeHomeomorph e hb b.property).continuous
      (e'.coordChangeHomeomorph e hb b.property).isOpenMap ↔
      (e' (constraintChartInverse e (b, y))).2 ∈ A := by
  let c : F ≃ₜ F := e'.coordChangeHomeomorph e hb b.property
  have hc : c.symm y = (e' (constraintChartInverse e (b, y))).2 := by
    change e.coordChange e' b.val y = _
    exact coordChange_constraintChartInverse e e' (b, y)
  change y ∈ (A.map c c.continuous c.isOpenMap : Set F) ↔ _
  rw [TopologicalSpace.CompactOpens.coe_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hy : c.symm y ∈ A := by
      rw [← hzy, c.symm_apply_apply]
      exact hz
    rwa [hc] at hy
  · intro hy
    refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
    rwa [hc]

/-- All charts whose base sets contain the base coordinate impose their constraint. -/
private def compactOpenConstraintGraph (e : I → Trivialization F p) (i : I)
    (A : TopologicalSpace.CompactOpens F) : Set ((e i).baseSet × F) :=
  {q | ∀ j, q.1.val ∈ (e j).baseSet →
    (e j (constraintChartInverse (e i) q)).2 ∈ A}

private theorem mem_compactOpenConstraintGraph_iff (e : I → Trivialization F p) (i : I)
    (A : TopologicalSpace.CompactOpens F) (q : (e i).baseSet × F) :
    q ∈ compactOpenConstraintGraph e i A ↔
      ∀ j, q.1.val ∈ (e j).baseSet →
        (e j (constraintChartInverse (e i) q)).2 ∈ A := Iff.rfl

private theorem isCompact_fiber_compactOpenConstraintGraph [Finite I]
    [QuasiSeparatedSpace F] (e : I → Trivialization F p) (i : I)
    (A : TopologicalSpace.CompactOpens F) (b : (e i).baseSet) :
    IsCompact {y : F | (b, y) ∈ compactOpenConstraintGraph e i A} := by
  classical
  let J := {j : I // b.val ∈ (e j).baseSet}
  let : Fintype J := Fintype.ofFinite J
  let C (j : J) : TopologicalSpace.CompactOpens F :=
    A.map ((e j.val).coordChangeHomeomorph (e i) j.property b.property)
      ((e j.val).coordChangeHomeomorph (e i) j.property b.property).continuous
      ((e j.val).coordChangeHomeomorph (e i) j.property b.property).isOpenMap
  have hne : (Finset.univ : Finset J).Nonempty :=
    ⟨⟨i, b.property⟩, Finset.mem_univ _⟩
  let K : TopologicalSpace.CompactOpens F := Finset.univ.inf' hne C
  have hcoe : (K : Set F) =
      Finset.univ.inf' hne (fun j : J ↦ (C j : Set F)) :=
    Finset.apply_inf'_eq_inf'_comp hne
      (fun U : TopologicalSpace.CompactOpens F ↦ (U : Set F))
      (fun U V ↦ TopologicalSpace.CompactOpens.coe_inf U V)
  have hmem (y : F) : y ∈ K ↔ ∀ j : J, y ∈ C j := by
    change y ∈ (K : Set F) ↔ _
    rw [hcoe]
    constructor
    · intro hy j
      exact (Finset.inf'_le (fun j : J ↦ (C j : Set F)) (Finset.mem_univ j)) hy
    · intro hy
      have hsub : ({y} : Set F) ≤
          Finset.univ.inf' hne (fun j : J ↦ (C j : Set F)) :=
        (Finset.le_inf'_iff hne _).2
          (fun j _ ↦ Set.singleton_subset_iff.mpr (hy j))
      exact hsub (Set.mem_singleton y)
  have heq : {y : F | (b, y) ∈ compactOpenConstraintGraph e i A} = (K : Set F) := by
    ext y
    change (b, y) ∈ compactOpenConstraintGraph e i A ↔ y ∈ K
    rw [mem_compactOpenConstraintGraph_iff, hmem]
    constructor
    · intro hy j
      exact (mem_map_coordChange_iff (e i) (e j.val) A b j.property y).2
        (hy j.val j.property)
    · intro hy j hj
      exact (mem_map_coordChange_iff (e i) (e j) A b hj y).1 (hy ⟨j, hj⟩)
  rw [heq]
  exact K.isCompact

/-- An old active constraint persists locally; no claim is made about inactive charts. -/
private theorem eventually_constraintChart (e e' : Trivialization F p)
    (A : TopologicalSpace.CompactOpens F) (b : e.baseSet) (hb : b.val ∈ e'.baseSet) :
    ∀ᶠ b' in 𝓝 b, b'.val ∈ e'.baseSet ∧ ∀ y : F,
      (e' (constraintChartInverse e (b', y))).2 ∈ A →
        (e' (constraintChartInverse e (b, y))).2 ∈ A := by
  let W := e'.baseSet ∩ e.baseSet
  let c (x : W) : F ≃ₜ F :=
    e'.coordChangeHomeomorph e x.property.1 x.property.2
  let C (x : W) : TopologicalSpace.CompactOpens F :=
    A.map (c x) (c x).continuous (c x).isOpenMap
  have hC : IsLocallyConstant C :=
    A.isLocallyConstant_map c (e'.continuous_coordChange_uncurry e)
      (e'.continuous_coordChangeHomeomorph_symm_uncurry e)
  let bW : W := ⟨b.val, hb, b.property⟩
  let V : Set W := {x | C x = C bW}
  have hV : IsOpen V := hC.isOpen_fiber (C bW)
  have hW : IsOpen W := e'.open_baseSet.inter e.open_baseSet
  have hN : IsOpen ((Subtype.val : e.baseSet → B) ⁻¹'
      ((Subtype.val : W → B) '' V)) :=
    (hW.isOpenMap_subtype_val V hV).preimage continuous_subtype_val
  have hbN : b ∈ (Subtype.val : e.baseSet → B) ⁻¹'
      ((Subtype.val : W → B) '' V) := ⟨bW, rfl, rfl⟩
  filter_upwards [hN.mem_nhds hbN] with b' hb'
  obtain ⟨x, hx, hxb⟩ := hb'
  have hb' : b'.val ∈ e'.baseSet := hxb ▸ x.property.1
  have hCb' : C (⟨b'.val, hb', b'.property⟩ : W) = C bW := by
    have heq : (⟨b'.val, hb', b'.property⟩ : W) = x := Subtype.ext hxb.symm
    rw [heq]
    exact hx
  refine ⟨hb', ?_⟩
  intro y hy
  have hy' := (mem_map_coordChange_iff e e' A b' hb' y).2 hy
  change y ∈ C (⟨b'.val, hb', b'.property⟩ : W) at hy'
  rw [hCb'] at hy'
  exact (mem_map_coordChange_iff e e' A b hb y).1 hy'

private theorem eventually_fiber_compactOpenConstraintGraph_subset [Finite I]
    (e : I → Trivialization F p) (i : I) (A : TopologicalSpace.CompactOpens F)
    (b : (e i).baseSet) :
    ∀ᶠ b' in 𝓝 b, {y : F | (b', y) ∈ compactOpenConstraintGraph e i A} ⊆
      {y : F | (b, y) ∈ compactOpenConstraintGraph e i A} := by
  classical
  have hj (j : I) : ∀ᶠ b' in 𝓝 b, b.val ∈ (e j).baseSet →
      b'.val ∈ (e j).baseSet ∧ ∀ y : F,
        (e j (constraintChartInverse (e i) (b', y))).2 ∈ A →
          (e j (constraintChartInverse (e i) (b, y))).2 ∈ A := by
    by_cases hb : b.val ∈ (e j).baseSet
    · exact (eventually_constraintChart (e i) (e j) A b hb).mono (fun _ h _ ↦ h)
    · exact Filter.Eventually.of_forall (fun _ h ↦ False.elim (hb h))
  filter_upwards [Filter.eventually_all.mpr hj] with b' hb'
  intro y hy
  apply (mem_compactOpenConstraintGraph_iff e i A (b, y)).2
  intro j hj
  have h := hb' j hj
  exact h.2 y ((mem_compactOpenConstraintGraph_iff e i A (b', y)).1 hy j h.1)

private theorem upperHemicontinuous_fiber_compactOpenConstraintGraph [Finite I]
    (e : I → Trivialization F p) (i : I) (A : TopologicalSpace.CompactOpens F) :
    UpperHemicontinuous
      (fun b : (e i).baseSet ↦ {y : F | (b, y) ∈ compactOpenConstraintGraph e i A}) := by
  apply upperHemicontinuous_iff_forall_isOpen.mpr
  intro b U _ hU
  exact (eventually_fiber_compactOpenConstraintGraph_subset e i A b).mono
    (fun _ h ↦ h.trans hU)

/-- The finite-chart constraint graph has proper first projection in reference coordinates. -/
private theorem isProperMap_fst_compactOpenConstraintGraph [Finite I]
    [QuasiSeparatedSpace F] (e : I → Trivialization F p) (i : I)
    (A : TopologicalSpace.CompactOpens F) :
    IsProperMap (fun q : compactOpenConstraintGraph e i A ↦ q.val.1) := by
  exact Set.isProperMap_fst_of_upperHemicontinuous
    (isCompact_fiber_compactOpenConstraintGraph e i A)
    (upperHemicontinuous_fiber_compactOpenConstraintGraph e i A)

/-- Compact-open constraints in finitely many charts cut out a compact set over a compact
base subset covered by those charts. The constraint set need not be ambient closed. -/
private theorem isCompact_preimage_of_compactOpen_constraints [Finite I]
    [QuasiSeparatedSpace F] (hp : Continuous p) (e : I → Trivialization F p)
    (A : TopologicalSpace.CompactOpens F) {s : Set B} (hs : IsCompact s)
    (hcover : s ⊆ ⋃ i, (e i).baseSet) :
    IsCompact {z : Z | p z ∈ s ∧ ∀ i, p z ∈ (e i).baseSet → (e i z).2 ∈ A} := by
  classical
  let U : Set B := ⋃ i, (e i).baseSet
  let T : Set Z := {z | p z ∈ U ∧ ∀ i, p z ∈ (e i).baseSet → (e i z).2 ∈ A}
  let r : T → U := fun z ↦ ⟨p z.val, z.property.1⟩
  have hr : Continuous r := (hp.comp continuous_subtype_val).subtype_mk _
  let V (i : I) : TopologicalSpace.Opens U :=
    ⟨(Subtype.val : U → B) ⁻¹' (e i).baseSet,
      (e i).open_baseSet.preimage continuous_subtype_val⟩
  have hV (b : U) : ∃ i, b ∈ V i := by
    obtain ⟨i, hi⟩ := (Set.mem_iUnion.mp b.property :
      ∃ i : I, (b : B) ∈ (e i).baseSet)
    exact ⟨i, hi⟩
  have hVcover : TopologicalSpace.IsOpenCover V := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro b _
    obtain ⟨i, hi⟩ := hV b
    exact (le_iSup V i) hi
  -- Each reference-chart graph maps to the global constraint set. Its image is
  -- precisely the part of that set above the reference chart's base set.
  let f (i : I) : compactOpenConstraintGraph e i A → T := fun q ↦
    ⟨constraintChartInverse (e i) q.val, by
      constructor
      · rw [constraintChartInverse_proj (e i) q.val]
        exact Set.mem_iUnion.mpr ⟨i, q.val.1.property⟩
      · intro j hj
        rw [constraintChartInverse_proj (e i) q.val] at hj
        exact (mem_compactOpenConstraintGraph_iff e i A q.val).1 q.property j hj⟩
  have hf (i : I) : Continuous (f i) :=
    ((continuous_constraintChartInverse (e i)).comp continuous_subtype_val).subtype_mk _
  have hfproj (i : I) (q : compactOpenConstraintGraph e i A) :
      p (f i q).val = q.val.1.val := constraintChartInverse_proj (e i) q.val
  have hfrecover (i : I) (x : T) (hi : p x.val ∈ (e i).baseSet) :
      ∃ q : compactOpenConstraintGraph e i A, f i q = x := by
    let q : (e i).baseSet × F := (⟨p x.val, hi⟩, (e i x.val).2)
    have hrec : constraintChartInverse (e i) q = x.val :=
      constraintChartInverse_apply (e i) x.val hi
    refine ⟨⟨q, ?_⟩, ?_⟩
    · apply (mem_compactOpenConstraintGraph_iff e i A q).2
      intro j hj
      rw [hrec]
      exact x.property.2 j hj
    · apply Subtype.ext
      exact hrec
  have hrclosed : IsClosedMap r := by
    intro C hC
    apply hVcover.isClosed_iff_coe_preimage.mpr
    intro i
    let k : V i → (e i).baseSet := fun b ↦ ⟨b.val.val, b.property⟩
    have hk : Continuous k :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let Q : Set (compactOpenConstraintGraph e i A) := (f i) ⁻¹' C
    have hQ : IsClosed Q := hC.preimage (hf i)
    have hfst : IsClosed ((fun q : compactOpenConstraintGraph e i A ↦ q.val.1) '' Q) :=
      (isProperMap_fst_compactOpenConstraintGraph e i A).isClosedMap Q hQ
    have heq : (Subtype.val : V i → U) ⁻¹' (r '' C) =
        k ⁻¹' ((fun q : compactOpenConstraintGraph e i A ↦ q.val.1) '' Q) := by
      ext b
      constructor
      · rintro ⟨x, hx, hxb⟩
        have hi : p x.val ∈ (e i).baseSet := by
          rw [show p x.val = b.val.val from congrArg Subtype.val hxb]
          exact b.property
        obtain ⟨q, hqx⟩ := hfrecover i x hi
        refine ⟨q, ?_, ?_⟩
        · change f i q ∈ C
          rw [hqx]
          exact hx
        · apply Subtype.ext
          rw [← hfproj i q, hqx]
          exact congrArg Subtype.val hxb
      · rintro ⟨q, hq, hqb⟩
        refine ⟨f i q, hq, ?_⟩
        apply Subtype.ext
        exact (hfproj i q).trans (congrArg Subtype.val hqb)
    rw [heq]
    exact hfst.preimage hk
  have hrfiber (b : U) : IsCompact (r ⁻¹' {b}) := by
    obtain ⟨i, hi⟩ := hV b
    let bi : (e i).baseSet := ⟨b.val, hi⟩
    let Q : Set (compactOpenConstraintGraph e i A) :=
      (fun q : compactOpenConstraintGraph e i A ↦ q.val.1) ⁻¹' {bi}
    have hQ : IsCompact Q :=
      (isProperMap_fst_compactOpenConstraintGraph e i A).isCompact_preimage
        isCompact_singleton
    have heq : r ⁻¹' {b} = f i '' Q := by
      ext x
      constructor
      · intro hx
        have hxb : r x = b := hx
        have hi' : p x.val ∈ (e i).baseSet := by
          rw [show p x.val = b.val from congrArg Subtype.val hxb]
          exact hi
        obtain ⟨q, hqx⟩ := hfrecover i x hi'
        refine ⟨q, ?_, hqx⟩
        change q.val.1 = bi
        apply Subtype.ext
        rw [← hfproj i q, hqx]
        exact congrArg Subtype.val hxb
      · rintro ⟨q, hq, rfl⟩
        have hqb : q.val.1 = bi := hq
        apply Subtype.ext
        exact (hfproj i q).trans (congrArg Subtype.val hqb)
    rw [heq]
    exact hQ.image (hf i)
  have hproper : IsProperMap r :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hr, hrclosed, hrfiber⟩
  -- Restrict by compactness in the original base, not by ambient closedness.
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let k : s → U := fun b ↦ ⟨b.val, hcover b.property⟩
  have hk : Continuous k := continuous_subtype_val.subtype_mk _
  let L : Set T := r ⁻¹' Set.range k
  have hL : IsCompact L := hproper.isCompact_preimage (isCompact_range hk)
  have heq : (Subtype.val : T → Z) '' L =
      {z : Z | p z ∈ s ∧ ∀ i, p z ∈ (e i).baseSet → (e i z).2 ∈ A} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, x.property.2⟩
      obtain ⟨b, hb⟩ := hx
      have hb' : (b : B) = p (x : Z) := congrArg Subtype.val hb
      exact hb' ▸ b.property
    · rintro ⟨hzs, hz⟩
      let x : T := ⟨z, hcover hzs, hz⟩
      refine ⟨x, ?_, rfl⟩
      exact ⟨⟨p z, hzs⟩, rfl⟩
  rw [← heq]
  exact hL.image continuous_subtype_val

end CompactOpenConstraints

private theorem isSigmaCompact_preimage_of_isCompact_of_monotone_compactOpen_cover
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [QuasiSeparatedSpace F]
    (K : ℕ → TopologicalSpace.CompactOpens F)
    (hmono : Monotone (fun n ↦ (K n : Set F)))
    (hcover : ∀ v, ∃ n, v ∈ K n) (s : Set B) (hs : IsCompact s) :
    IsSigmaCompact ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' s) := by
  classical
  let p : Bundle.TotalSpace F E → B := Bundle.TotalSpace.proj
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover
    (fun b ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ Set.mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F E b⟩)
  let I := {b : B // b ∈ t}
  let : Fintype I := inferInstance
  let e (i : I) := trivializationAt F E i.1
  have hcharts : s ⊆ ⋃ i : I, (e i).baseSet := by
    intro b hb
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hb)
    obtain ⟨hit, hbi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hbi⟩
  let C (n : ℕ) : Set (Bundle.TotalSpace F E) :=
    {z | p z ∈ s ∧ ∀ i : I, p z ∈ (e i).baseSet → (e i z).2 ∈ K n}
  have hCcompact (n : ℕ) : IsCompact (C n) :=
    isCompact_preimage_of_compactOpen_constraints (continuous_proj F E) e (K n) hs hcharts
  have heq : p ⁻¹' s = ⋃ n, C n := by
    ext z
    constructor
    · intro hz
      have hidx : ∀ i : I, ∃ n, p z ∈ (e i).baseSet → (e i z).2 ∈ K n := by
        intro i
        by_cases hi : p z ∈ (e i).baseSet
        · obtain ⟨n, hn⟩ := hcover ((e i z).2)
          exact ⟨n, fun _ ↦ hn⟩
        · exact ⟨0, fun h ↦ False.elim (hi h)⟩
      choose f hf using hidx
      refine Set.mem_iUnion.mpr ⟨Finset.univ.sup f, hz, ?_⟩
      intro i hi
      exact hmono (Finset.le_sup (Finset.mem_univ i)) (hf i hi)
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact hn.1
  change IsSigmaCompact (p ⁻¹' s)
  rw [heq]
  exact isSigmaCompact_iUnion_of_isCompact C hCcompact

/-- A fiber bundle over a sigma-compact base has sigma-compact total space if its model is
quasi-separated and has a countable cover by compact open sets. The cover already implies
sigma-compactness of the model. All given topologies and the coupled bundle structure are
retained, without separation or nonemptiness assumptions. -/
theorem sigmaCompactSpace_of_countable_open_compact_cover
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SigmaCompactSpace B] [QuasiSeparatedSpace F]
    (U : ℕ → TopologicalSpace.CompactOpens F)
    (hcover : (⋃ n, (U n : Set F)) = Set.univ) :
    SigmaCompactSpace (Bundle.TotalSpace F E) := by
  classical
  let K (n : ℕ) : TopologicalSpace.CompactOpens F := (Finset.range (n + 1)).sup U
  have hKmono : Monotone (fun n ↦ (K n : Set F)) := by
    intro m n hmn
    have hle : K m ≤ K n :=
      Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hmn 1))
    exact hle
  have hKcover (v : F) : ∃ n, v ∈ K n := by
    have hv : v ∈ ⋃ n, (U n : Set F) := by rw [hcover]; exact Set.mem_univ v
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    refine ⟨n, ?_⟩
    have hle : U n ≤ K n := Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact hle hn
  apply isSigmaCompact_univ_iff.mp
  have hpre (j : ℕ) : IsSigmaCompact
      ((Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹' compactCovering B j) :=
    isSigmaCompact_preimage_of_isCompact_of_monotone_compactOpen_cover F E
      K hKmono hKcover (compactCovering B j) (isCompact_compactCovering B j)
  have heq : (⋃ j, (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B) ⁻¹'
      compactCovering B j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_mem_compactCovering x.proj
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  rw [← heq]
  exact isSigmaCompact_iUnion _ hpre

private theorem exists_countable_open_compact_cover_of_open_nhdsKer_cover
    {F : Type uF} [TopologicalSpace F] [SigmaCompactSpace F]
    (hK : ∀ x : F, ∃ c : F,
      IsOpen (nhdsKer ({c} : Set F)) ∧ x ∈ nhdsKer ({c} : Set F)) :
    ∃ U : ℕ → TopologicalSpace.CompactOpens F, (⋃ n, (U n : Set F)) = Set.univ := by
  classical
  let c : F → F := fun x => Classical.choose (hK x)
  let V (x : F) : TopologicalSpace.CompactOpens F :=
    ⟨⟨nhdsKer ({c x} : Set F), isCompact_singleton.nhdsKer⟩,
      (Classical.choose_spec (hK x)).1⟩
  have hVcover (x : F) : x ∈ V x := (Classical.choose_spec (hK x)).2
  have hfinite (n : ℕ) : ∃ t : Finset F,
      compactCovering F n ⊆ ⋃ x ∈ t, (V x : Set F) :=
    (isCompact_compactCovering F n).elim_finite_subcover
      (fun x => (V x : Set F)) (fun x => (V x).isOpen)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hVcover x⟩)
  choose t ht using hfinite
  refine ⟨fun n => (t n).sup V, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_mem_compactCovering x
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  rw [TopologicalSpace.CompactOpens.coe_finsetSup]
  exact ht n hn

/-- A fiber bundle with sigma-compact base and quasi-separated sigma-compact model has
sigma-compact total space if the open neighborhood kernels of singletons cover the model.
Only the kernels used by the cover must be open; their family need not be countable.
All given topologies and the coupled bundle structure are retained, without separation
or nonemptiness assumptions. -/
theorem sigmaCompactSpace_of_open_nhdsKer_cover
    {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [SigmaCompactSpace B] [SigmaCompactSpace F] [QuasiSeparatedSpace F]
    (hK : ∀ x : F, ∃ c : F,
      IsOpen (nhdsKer ({c} : Set F)) ∧ x ∈ nhdsKer ({c} : Set F)) :
    SigmaCompactSpace (Bundle.TotalSpace F E) := by
  obtain ⟨U, hU⟩ := exists_countable_open_compact_cover_of_open_nhdsKer_cover hK
  exact sigmaCompactSpace_of_countable_open_compact_cover F E U hU

end FiberBundle
