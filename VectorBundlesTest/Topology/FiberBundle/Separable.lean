/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.Separable.Basic
import VectorBundles.Topology.FiberBundle.Separable
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Separable real planes and trivial bundles

The noninjective first-coordinate projection on `ℝ × ℝ` has separable fibers:
each fiber is the range of a continuous map from `ℝ`. This proves separability of
the plane by the whole-codomain criterion and ambient separability of the strip
above `Set.Icc (0 : ℝ) 1` by the set-preimage criterion. For the latter, only the
target interval's ambient separability is taken from separability of `ℝ`; neither
fiber argument uses separability of the plane.

The usual trivial real-line bundle over `ℝ` has separable total space. The trivial
bundle with empty model over the same nonempty base also has separable total space.
Both statements retain the given trivial-bundle topologies.

For an injective open map into a separable space, singleton preimages are countable,
so the separable-fiber criterion recovers separability of the domain.

## References

* Mathlib's `TopologicalSpace.isSeparable_range`,
  `TopologicalSpace.IsSeparable.of_separableSpace` and `Bundle.Trivial` APIs.
* Mathlib's `IsOpenMap.separableSpace_of_injective`, `Set.Subsingleton.preimage`
  and `Set.Countable.isSeparable` APIs.
* `VectorBundlesTest.Topology.FiberBundle.Connected` for the real-fiber
  parametrization shared by the two projection examples here.
-/

@[expose] public section

universe u v

open Bundle TopologicalSpace

-- Each fiber is shown separable as a continuous range, not as a subset of a separable plane.
private theorem isSeparable_fst_fiber (y : ℝ) :
    TopologicalSpace.IsSeparable ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {y}) := by
  have hRange : Set.range (fun t : ℝ => (y, t)) =
      (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {y} := by
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      rfl
    · intro hp
      change p.1 = y at hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [← hRange]
  exact isSeparable_range (continuous_const.prodMk continuous_id)

example : SeparableSpace (ℝ × ℝ) := by
  exact IsOpenMap.separableSpace_of_isSeparable_fibers
    (f := (Prod.fst : ℝ × ℝ → ℝ)) isOpenMap_fst isSeparable_fst_fiber

-- Only the target interval is obtained from a global separability instance.
example : TopologicalSpace.IsSeparable
    ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) := by
  have hs : TopologicalSpace.IsSeparable (Set.Icc (0 : ℝ) 1) :=
    TopologicalSpace.IsSeparable.of_separableSpace (Set.Icc (0 : ℝ) 1)
  exact hs.preimage_of_isOpenMap_of_isSeparable_fibers isOpenMap_fst isSeparable_fst_fiber

-- The original trivial real-line bundle over the real line.
example : SeparableSpace (TotalSpace ℝ (Trivial ℝ ℝ)) := by
  exact FiberBundle.separableSpace_totalSpace ℝ (Trivial ℝ ℝ)

-- The same nonempty base, with empty model and the original trivial-bundle topology.
example : SeparableSpace (TotalSpace Empty (Trivial ℝ Empty)) := by
  exact FiberBundle.separableSpace_totalSpace Empty (Trivial ℝ Empty)

-- Exactly the hypotheses of Mathlib's separability theorem for injective open maps.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace Y] {f : X → Y} (h : IsOpenMap f) (h' : Function.Injective f) :
    SeparableSpace X := by
  exact h.separableSpace_of_isSeparable_fibers
    (fun _ => (Set.subsingleton_singleton.preimage h').countable.isSeparable)

section

universe uB uF uE

-- A specified point suffices for model reflection in a generic product.
example {B : Type uB} {F : Type uF} [TopologicalSpace B] [TopologicalSpace F]
    (b : B) [SeparableSpace (B × F)] : SeparableSpace F := by
  letI : SeparableSpace (TotalSpace F (Trivial B F)) :=
    (Trivial.homeomorphProd B F).symm.surjective.denseRange.separableSpace
      (Trivial.homeomorphProd B F).symm.continuous
  exact FiberBundle.separableSpace_model F (Trivial B F) b

-- An arbitrary ambient strip: the base and the subset need not be separable or open.
example {B : Type uB} {F : Type uF} [TopologicalSpace B] [TopologicalSpace F]
    [Nonempty F] [SeparableSpace F] (s : Set B) :
    IsSeparable (s ×ˢ (Set.univ : Set F)) ↔ IsSeparable s := by
  have hFib : ∀ b : B, IsSeparable ((Prod.fst : B × F → B) ⁻¹' {b}) := by
    intro b
    have hrange : Set.range (fun v : F => (b, v)) =
        (Prod.fst : B × F → B) ⁻¹' {b} := by
      ext p
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, rfl⟩
        rfl
      · intro hp
        exact ⟨p.2, Prod.ext hp.symm rfl⟩
    rw [← hrange]
    exact isSeparable_range (continuous_const.prodMk continuous_id)
  have hq : IsOpenQuotientMap (Prod.fst : B × F → B) :=
    ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩
  have hpre : (Prod.fst : B × F → B) ⁻¹' s = s ×ˢ (Set.univ : Set F) := by
    ext p
    simp
  simpa only [hpre] using hq.isSeparable_preimage_iff hFib s

-- The global characterization specializes to the canonical trivial bundle/product.
example {B : Type uB} {F : Type uF} [TopologicalSpace B] [TopologicalSpace F]
    [Nonempty B] [Nonempty F] :
    SeparableSpace (B × F) ↔ (SeparableSpace B ∧ SeparableSpace F) := by
  have h := FiberBundle.separableSpace_totalSpace_iff F (Trivial B F)
  constructor
  · intro hProd
    letI : SeparableSpace (B × F) := hProd
    letI : SeparableSpace (TotalSpace F (Trivial B F)) :=
      (Trivial.homeomorphProd B F).symm.surjective.denseRange.separableSpace
        (Trivial.homeomorphProd B F).symm.continuous
    exact h.mp inferInstance
  · rintro ⟨hB, hF⟩
    letI : SeparableSpace (TotalSpace F (Trivial B F)) := h.mpr ⟨hB, hF⟩
    exact (Trivial.homeomorphProd B F).surjective.denseRange.separableSpace
      (Trivial.homeomorphProd B F).continuous

-- Exact stock base reflection: no nonempty base or separable model assumption.
example {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [Nonempty F] [SeparableSpace (TotalSpace F E)] :
    SeparableSpace B := by
  exact (FiberBundle.isQuotientMap_proj F E).separableSpace

-- Ambient subset reflection for the original bundle projection.
example {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [fb : FiberBundle F E] [Nonempty F] [SeparableSpace F] (s : Set B) :
    IsSeparable (π F E ⁻¹' s) ↔ IsSeparable s := by
  have hq : IsOpenQuotientMap (π F E) :=
    ⟨FiberBundle.surjective_proj F E, FiberBundle.continuous_proj F E,
      FiberBundle.isOpenMap_proj F E⟩
  refine hq.isSeparable_preimage_iff (fun b => ?_) s
  letI : SeparableSpace (E b) :=
    (FiberBundle.homeomorphAt F E b).symm.surjective.denseRange.separableSpace
      (FiberBundle.homeomorphAt F E b).symm.continuous
  simpa only [TotalSpace.range_mk] using
    (isSeparable_range (FiberBundle.continuous_totalSpaceMk F E b))

-- A base point does not require a nonempty model or a nonempty total space.
example {B : Type uB} [TopologicalSpace B] (b : B) : SeparableSpace Empty := by
  letI : IsEmpty (TotalSpace Empty (Trivial B Empty)) := ⟨fun x => Empty.elim x.snd⟩
  letI : SeparableSpace (TotalSpace Empty (Trivial B Empty)) := inferInstance
  exact FiberBundle.separableSpace_model Empty (Trivial B Empty) b

-- An empty base gives separable total space for every model; no model conclusion
-- follows without a base point. Dually, an empty model gives empty total space
-- independently of base separability, explaining the nonempty-model hypothesis.
example (F : Type uF) [TopologicalSpace F] :
    SeparableSpace (TotalSpace F (Trivial Empty F)) := by
  letI : IsEmpty (TotalSpace F (Trivial Empty F)) := ⟨fun x => Empty.elim x.proj⟩
  infer_instance

end
