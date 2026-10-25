/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.CoordinateMap
public import VectorBundles.Topology.Algebra.Module.OpenMap
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Open maps of vector bundles

Fibrewise-surjective, fibrewise-linear continuous maps over a common base are open when the
finite-dimensional target model carries its given `IsModuleTopology`. The proof uses the given
bundle charts, restricted to the intersection of their base sets; all total-space maps retain
their original topologies. Both models are topological vector spaces, without an assumed norm.

For the vector-bundle setting, see Allen Hatcher,
[*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html),
version 2.2 (2017), Chapter 1. Here the scalar field may be any nontrivially normed field and
the source model need not be finite-dimensional; the target's module topology is an explicit
hypothesis, rather than a change to its given topology.
-/

@[expose] public section

universe uκ uB uF uG uE uE'

namespace Bundle

/-- A fibrewise-surjective, fibrewise-linear continuous map of bundles over the same base
is open when the finite-dimensional target model carries its given module topology.
The source and target models are topological vector spaces; no norm or finite-dimensionality
is required of the source model. -/
theorem isOpenMap_totalSpaceMap
    {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [AddCommGroup F] [Module κ F] [TopologicalSpace F]
    [ContinuousAdd F] [ContinuousSMul κ F]
    {G : Type uG} [AddCommGroup G] [Module κ G] [TopologicalSpace G]
    [ContinuousAdd G] [ContinuousSMul κ G]
    [FiniteDimensional κ G] [IsModuleTopology κ G]
    {E : B → Type uE} {E' : B → Type uE'}
    [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
    [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]
    [FiberBundle F E] [FiberBundle G E']
    (hF : ∀ b, (trivializationAt F E b).IsLinear κ)
    (hG : ∀ b, (trivializationAt G E' b).IsLinear κ)
    (φ : ∀ b, E b →ₗ[κ] E' b)
    (hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (φ p.proj p.snd)))
    (hSurj : ∀ b, Function.Surjective (φ b)) :
    IsOpenMap (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (φ p.proj p.snd)) := by
  let f : TotalSpace F E → TotalSpace G E' := fun p ↦
    TotalSpace.mk' G p.proj (φ p.proj p.snd)
  change IsOpenMap f
  intro S hS
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro y ⟨q, hq, rfl⟩
  let eF := trivializationAt F E q.proj
  let eG := trivializationAt G E' q.proj
  let : eF.IsLinear κ := hF q.proj
  let : eG.IsLinear κ := hG q.proj
  let U : Set B := eF.baseSet ∩ eG.baseSet
  have hU : IsOpen U := eF.open_baseSet.inter eG.open_baseSet
  have hb : q.proj ∈ U :=
    ⟨mem_baseSet_trivializationAt F E q.proj,
      mem_baseSet_trivializationAt G E' q.proj⟩
  let A : U → F →ₗ[κ] G := fun b ↦
    (eG.linearMapAt κ b).comp ((φ b).comp (eF.symmₗ κ b))
  have hiF : Continuous (fun p : U × F ↦ ((p.1 : B), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hA : Continuous (fun p : U × F ↦ A p.1 p.2) := by
    exact (eF.continuousOn_linearMapAt_comp_apply eG φ hφ).comp_continuous hiF
      (fun p ↦ ⟨p.1.property, Set.mem_univ _⟩)
  have hAsurj : ∀ b, Function.Surjective (A b) := by
    intro b w
    obtain ⟨v, hv⟩ := hSurj b (eG.symmₗ κ b w)
    refine ⟨eF.linearMapAt κ b v, ?_⟩
    change eG.linearMapAt κ b (φ b
      (eF.symmₗ κ b (eF.linearMapAt κ b v))) = w
    rw [eF.symmₗ_linearMapAt b.property.1, hv,
      eG.linearMapAt_symmₗ b.property.2]
  let H : U × F → U × G := fun p ↦ (p.1, A p.1 p.2)
  have hH : IsOpenMap H :=
    LinearMap.isOpenMap_prodMap A hA hAsurj
  let s : U × F → TotalSpace F E := fun p ↦
    TotalSpace.mk' F p.1 (eF.symmₗ κ p.1 p.2)
  let t : U × G → TotalSpace G E' := fun p ↦
    TotalSpace.mk' G p.1 (eG.symmₗ κ p.1 p.2)
  have hs : Continuous s := by
    have hs_eq : s = (fun p : U × F ↦
        TotalSpace.mk' F (p.1 : B) (eF.symm (p.1 : B) p.2)) := by
      funext p
      exact congrArg (TotalSpace.mk' F (p.1 : B))
        (eF.symmₗ_apply (R := κ) p.1.property.1 p.2)
    rw [hs_eq]
    exact eF.continuousOn_symm.comp_continuous hiF
      (fun p ↦ ⟨p.1.property.1, Set.mem_univ _⟩)
  have ht : IsOpenMap t := by
    let j : U × G → B × G := fun p ↦ ((p.1 : B), p.2)
    have hj : IsOpenMap j := hU.isOpenMap_subtype_val.prodMap .id
    have ht_eq : t = (fun p ↦ eG.toOpenPartialHomeomorph.symm (j p)) := by
      funext p
      change TotalSpace.mk' G (p.1 : B) (eG.symmₗ κ p.1 p.2) = _
      rw [eG.symmₗ_apply (R := κ) p.1.property.2 p.2]
      exact eG.mk_symm p.1.property.2 p.2
    rw [ht_eq]
    intro V hV
    have hVtarget : j '' V ⊆ eG.target := by
      rintro z ⟨p, hp, rfl⟩
      exact eG.mem_target.mpr p.1.property.2
    simpa only [Set.image_image] using
      eG.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target (hj V hV) hVtarget
  have hcomm : ∀ p, t (H p) = f (s p) := by
    intro p
    change TotalSpace.mk' G (p.1 : B)
      (eG.symmₗ κ p.1 (eG.linearMapAt κ p.1
        (φ p.1 (eF.symmₗ κ p.1 p.2)))) =
      TotalSpace.mk' G (p.1 : B) (φ p.1 (eF.symmₗ κ p.1 p.2))
    rw [eG.symmₗ_linearMapAt p.1.property.2]
  let a : U × F := (⟨q.proj, hb⟩, eF.linearMapAt κ q.proj q.snd)
  have ha : s a = q := by
    change TotalSpace.mk' F q.proj
      (eF.symmₗ κ q.proj (eF.linearMapAt κ q.proj q.snd)) = q
    rw [eF.symmₗ_linearMapAt hb.1]
  have hopen : IsOpen (t '' (H '' (s ⁻¹' S))) :=
    ht _ (hH _ (hS.preimage hs))
  have hmem : f q ∈ t '' (H '' (s ⁻¹' S)) := by
    refine ⟨H a, ⟨a, ?_, rfl⟩, ?_⟩
    · change s a ∈ S
      simpa only [ha] using hq
    · exact (hcomm a).trans (congrArg f ha)
  have hsubset : t '' (H '' (s ⁻¹' S)) ⊆ f '' S := by
    rintro z ⟨w, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨s p, hp, (hcomm p).symm⟩
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) hsubset

end Bundle
