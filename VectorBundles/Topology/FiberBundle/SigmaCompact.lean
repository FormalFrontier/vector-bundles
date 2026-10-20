/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.FiberBundle.Basic

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
