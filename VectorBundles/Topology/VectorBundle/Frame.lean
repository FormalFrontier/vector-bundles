/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Isomorphism
import VectorBundles.Topology.VectorBundle.KernelProjection
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Global trivializations from continuous fiberwise bases

A finite family of continuous sections which is a basis in every fiber determines a global
linear trivialization of a vector bundle. The construction
`Bundle.Trivialization.ofBasisOfIsModuleTopology` preserves the model fiber: a basis `v` of the
model fiber and bases `b x` of the fibers specify the unique global linear trivialization taking
`b x i` to `v i`.

The coordinate functions in such a family of bases are continuous on the total space.
Consequently, a section is continuous if and only if all of its coefficients are continuous.
For a rank-`n` bundle, the basis hypothesis can equivalently be replaced by pointwise linear
independence of `n` continuous sections.

## Implementation notes

The index type is finite but need not be nonempty, and the base space need not be nonempty.
The model fiber is assumed to have its module topology. The complete-field versions derive
this topology from a model basis or at each point from a fiber basis. The coefficient and section
criteria also cover an empty base without imposing finite dimensionality on the model.
The resulting trivialization is fiberwise linear, but is not required to belong to the given
trivialization atlas. Fiber additive groups can be recovered from their module structures when
needed; only additive monoids are assumed publicly. No manifold structure is used.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, §1.1, pp. 8–9.
-/

@[expose] public section

open Bundle Module
open scoped BigOperators Bundle

universe u𝕜 uB uF uE uι

namespace VectorBundle

section FrameContinuity

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [hFB : FiberBundle F E] [hVB : VectorBundle 𝕜 F E]
  {ι : Type uι} [hι : Finite ι]

include hFB hVB hι

/-- Coordinates in a finite continuous frame are continuous at a point when the model has
its module topology. -/
private theorem continuousAt_basis_equivFun_of_isModuleTopology
    [IsModuleTopology 𝕜 F]
    (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))
    (p : TotalSpace F E) :
    ContinuousAt (fun z : TotalSpace F E ↦ (b z.proj).equivFun z.2) p := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := trivializationAt F E p.proj
  have hp : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p.proj
  let S := e.baseSet
  let x₀ : S := ⟨p.proj, hp⟩
  -- Only the fiber at the given point is needed to obtain a finite basis of the model.
  let v : Basis ι 𝕜 F := (b p.proj).map (e.linearEquivAt 𝕜 p.proj hp)
  let : FiniteDimensional 𝕜 F := v.finiteDimensional_of_finite
  let C := ι → 𝕜
  let a (x : S) : C ≃ₗ[𝕜] F :=
    (b x.1).equivFun.symm.trans (e.linearEquivAt 𝕜 x.1 x.2)
  let A : S → C →L[𝕜] F := fun x ↦
    ⟨(a x).toLinearMap, IsModuleTopology.continuous_of_linearMap (a x).toLinearMap⟩
  let w (x : S) (i : ι) : F := (e ⟨x.1, b x.1 i⟩).2
  have hw (i : ι) : Continuous (fun x : S ↦ w x i) :=
    (e.continuousOn.comp_continuous ((hb i).comp continuous_subtype_val)
      (fun x ↦ e.mem_source.mpr x.2)).snd
  -- Finite synthesis is continuous even as a family of operators: its columns are continuous.
  have hA_eq (x : S) :
      A x = ∑ i, (ContinuousLinearMap.proj i : C →L[𝕜] 𝕜).smulRight (w x i) := by
    ext c
    change (e.linearEquivAt 𝕜 x.1 x.2) ((b x.1).equivFun.symm c) = (∑ i,
      (ContinuousLinearMap.proj i : C →L[𝕜] 𝕜).smulRight (w x i)) c
    calc
      _ = (e.linearEquivAt 𝕜 x.1 x.2) (∑ i, c i • b x.1 i) :=
        congrArg (e.linearEquivAt 𝕜 x.1 x.2) (Basis.equivFun_symm_apply (b x.1) c)
      _ = ∑ i, c i • (e.linearEquivAt 𝕜 x.1 x.2) (b x.1 i) := by
        simp only [map_sum, map_smul]
      _ = _ := by
        simp only [Trivialization.linearEquivAt_apply, sum_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, w]
  have hA : Continuous A := by
    have hsum : Continuous (fun x : S ↦
        ∑ i, (ContinuousLinearMap.proj i : C →L[𝕜] 𝕜).smulRight (w x i)) := by
      apply continuous_finsetSum
      intro i _
      exact ((ContinuousLinearMap.smulRightL 𝕜 C F)
        (ContinuousLinearMap.proj i)).continuous.comp (hw i)
    exact hsum.congr fun x ↦ (hA_eq x).symm
  -- The inverse seed uses the given module topology on F, not completeness of the field.
  let j₀ : F →L[𝕜] C :=
    ⟨(a x₀).symm.toLinearMap,
      IsModuleTopology.continuous_of_linearMap (a x₀).symm.toLinearMap⟩
  have hj₀ : (A x₀).comp j₀ = ContinuousLinearMap.id 𝕜 F := by
    ext y
    exact (a x₀).apply_symm_apply y
  obtain ⟨U, hU, hx₀, K, hK, hright, _⟩ :=
    ContinuousLinearMap.exists_local_section_inverse A hA x₀ j₀ hj₀
  -- Work on open restrictions so the inverse action is evaluated only where it is defined.
  let Z : Set (TotalSpace F E) := {z | z.proj ∈ e.baseSet}
  let q : Z := ⟨p, hp⟩
  let r : Z → S := fun z ↦ ⟨z.1.proj, z.2⟩
  have hr : Continuous r :=
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk
      (fun z ↦ z.2)
  let V : Set Z := r ⁻¹' U
  have hq : q ∈ V := hx₀
  let rU : V → U := fun z ↦ ⟨r z.1, z.2⟩
  have hrU : Continuous rU :=
    (hr.comp continuous_subtype_val).subtype_mk (fun z ↦ z.2)
  have hcoord : Continuous (fun z : V ↦ (e z.1.1).2) :=
    (e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z ↦ e.mem_source.mpr z.1.2)).snd
  have hcoeff : Continuous (fun z : V ↦ (b z.1.1.proj).equivFun z.1.1.2) := by
    refine (j₀.continuous.comp (hK.comp (hrU.prodMk hcoord))).congr ?_
    intro z
    apply (a (r z.1)).injective
    change A (r z.1) (j₀ (K (rU z) (e z.1.1).2)) =
      a (r z.1) ((b z.1.1.proj).equivFun z.1.1.2)
    rw [hright (rU z)]
    change (e z.1.1).2 =
      (e.linearEquivAt 𝕜 z.1.1.proj z.1.2)
        ((b z.1.1.proj).equivFun.symm ((b z.1.1.proj).equivFun z.1.1.2))
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hcoeffZ : ContinuousAt (fun z : Z ↦ (b z.1.proj).equivFun z.1.2) q := by
    have hcoeffV : Continuous
        (V.domRestrict (fun z : Z ↦ (b z.1.proj).equivFun z.1.2)) := by
      apply hcoeff.congr
      intro z
      exact (Set.domRestrict_apply
        (fun z : Z ↦ (b z.1.proj).equivFun z.1.2) V z).symm
    have hwithin := (continuousWithinAt_iff_continuousAt_domRestrict
      (fun z : Z ↦ (b z.1.proj).equivFun z.1.2) hq).mpr
      (hcoeffV.continuousAt (x := ⟨q, hq⟩))
    exact hwithin.continuousAt ((hU.preimage hr).mem_nhds hq)
  have hwithin := (continuousWithinAt_iff_continuousAt_domRestrict
    (fun z : TotalSpace F E ↦ (b z.proj).equivFun z.2) (show p ∈ Z from hp)).mpr hcoeffZ
  exact hwithin.continuousAt
    ((e.open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds hp)

/-- Finite synthesis in a continuous frame is jointly continuous in the point and the
scalar coefficients. -/
theorem continuous_basis_synthesis
    (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    Continuous (fun p : B × (ι → 𝕜) ↦
      TotalSpace.mk' F p.1 ((b p.1).equivFun.symm p.2)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  simp_rw [Basis.equivFun_symm_apply]
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_fst.continuousAt, ?_⟩
  let e := trivializationAt F E p₀.1
  have hcoords (i : ι) :
      ContinuousAt (fun p : B × (ι → 𝕜) ↦ (e ⟨p.1, b p.1 i⟩).2) p₀ :=
    ((FiberBundle.continuousAt_totalSpace F
      (fun p : B × (ι → 𝕜) ↦ TotalSpace.mk' F p.1 (b p.1 i))).mp
        ((hb i).comp continuous_fst).continuousAt).2
  have hsum : ContinuousAt (fun p : B × (ι → 𝕜) ↦
      ∑ i, p.2 i • (e ⟨p.1, b p.1 i⟩).2) p₀ :=
    tendsto_finsetSum _ fun i _ ↦
      ((continuous_apply i).comp continuous_snd).continuousAt.smul (hcoords i)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.continuousAt (x := p₀)).preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F E p₀.1))]
    with p hp
  have hmap := map_sum (e.linearEquivAt 𝕜 p.1 hp)
    (fun i ↦ p.2 i • b p.1 i) Finset.univ
  simp only [map_smul] at hmap
  simpa only [Trivialization.linearEquivAt_apply] using hmap

/-- Continuity of frame coordinates and finite synthesis characterize continuous sections. -/
private theorem continuous_section_iff_basis_coeff_of_continuous
    (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))
    (hcoeff : Continuous (fun z : TotalSpace F E ↦ (b z.proj).equivFun z.2))
    (s : ∀ x, E x) :
    Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ↔
      ∀ i, Continuous (fun x ↦ (b x).repr (s x) i) := by
  constructor
  · intro hs i
    exact (continuous_apply i).comp (hcoeff.comp hs)
  · intro hs
    have hc : Continuous (fun x ↦ (b x).equivFun (s x)) := continuous_pi hs
    simpa only [Function.comp_def, id_eq, LinearEquiv.symm_apply_apply] using
      (continuous_basis_synthesis b hb).comp (continuous_id.prodMk hc)

/-- Coordinates in a continuous family of finite fiberwise bases are continuous on the total
space when the model has its module topology. No model basis or nonempty base is required.

This is the coordinate-map characterization of trivial bundles in Hatcher,
*Vector Bundles and K-Theory*, §1.1, pp. 8–9. -/
theorem continuous_basis_equivFun_of_isModuleTopology [IsModuleTopology 𝕜 F]
    (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    Continuous (fun z : TotalSpace F E ↦ (b z.proj).equivFun z.2) := by
  exact continuous_iff_continuousAt.2 fun p ↦
    continuousAt_basis_equivFun_of_isModuleTopology b hb p

/-- A section is continuous if and only if its coefficients in a continuous finite frame are
continuous, when the model has its module topology. -/
theorem continuous_section_iff_basis_coeff_of_isModuleTopology [IsModuleTopology 𝕜 F]
    (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))
    (s : ∀ x, E x) :
    Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ↔
      ∀ i, Continuous (fun x ↦ (b x).repr (s x) i) :=
  continuous_section_iff_basis_coeff_of_continuous b hb
    (continuous_basis_equivFun_of_isModuleTopology b hb) s

end FrameContinuity

end VectorBundle

namespace Bundle.Trivialization

/-- A global linear trivialization determined by a continuous family of finite fiberwise bases.
It sends the vector `b x i` over `x` to the model basis vector `v i`.

This is the finite-frame characterization of trivial bundles in Hatcher,
*Vector Bundles and K-Theory*, §1.1, p. 8. -/
noncomputable def ofBasisOfIsModuleTopology
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsModuleTopology 𝕜 F]
    {E : B → Type uE}
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {ι : Type uι} [Finite ι]
    (v : Basis ι 𝕜 F) (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    Trivialization F (π F E) := by
  have hv : Continuous v.equivFun :=
    IsModuleTopology.continuous_of_linearMap v.equivFun.toLinearMap
  have hv' : Continuous v.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap v.equivFun.symm.toLinearMap
  have hanalysis : Continuous (fun z : TotalSpace F E ↦
      (z.proj, v.equivFun.symm ((b z.proj).equivFun z.2))) :=
    (FiberBundle.continuous_proj F E).prodMk
      (hv'.comp (VectorBundle.continuous_basis_equivFun_of_isModuleTopology b hb))
  have hsynthesis : Continuous (fun p : B × F ↦
      (⟨p.1, (b p.1).equivFun.symm (v.equivFun p.2)⟩ : TotalSpace F E)) := by
    exact (VectorBundle.continuous_basis_synthesis b hb).comp
      (continuous_fst.prodMk (hv.comp continuous_snd))
  exact
    { toOpenPartialHomeomorph :=
        { toFun := fun z ↦ (z.proj, v.equivFun.symm ((b z.proj).equivFun z.2))
          invFun := fun p ↦ ⟨p.1, (b p.1).equivFun.symm (v.equivFun p.2)⟩
          source := Set.univ
          target := Set.univ
          map_source' := fun _ _ ↦ Set.mem_univ _
          map_target' := fun _ _ ↦ Set.mem_univ _
          left_inv' := by
            intro z _
            simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, TotalSpace.eta]
          right_inv' := by
            intro p _
            simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
          open_source := isOpen_univ
          open_target := isOpen_univ
          continuousOn_toFun := hanalysis.continuousOn
          continuousOn_invFun := hsynthesis.continuousOn }
      baseSet := Set.univ
      open_baseSet := isOpen_univ
      source_eq := by simp
      target_eq := by simp
      proj_toFun := fun _ _ ↦ rfl }

/-- A global linear trivialization determined by a continuous family of finite fiberwise bases.
It sends the vector `b x i` over `x` to the model basis vector `v i`.

This is the finite-frame characterization of trivial bundles in Hatcher,
*Vector Bundles and K-Theory*, §1.1, p. 8. -/
noncomputable def ofBasis
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type uE}
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {ι : Type uι} [Finite ι]
    (v : Basis ι 𝕜 F) (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    Trivialization F (π F E) := by
  letI : FiniteDimensional 𝕜 F := v.finiteDimensional_of_finite
  letI : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  exact ofBasisOfIsModuleTopology v b hb

section OfBasisOfIsModuleTopology

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsModuleTopology 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {ι : Type uι} [Finite ι]
  (v : Basis ι 𝕜 F) (b : ∀ x, Basis ι 𝕜 (E x))
  (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))

instance ofBasisOfIsModuleTopology.isLinear : (ofBasisOfIsModuleTopology v b hb).IsLinear 𝕜 where
  linear x _ := ((b x).equivFun.trans v.equivFun.symm).toLinearMap.isLinear

@[simp]
theorem ofBasisOfIsModuleTopology_baseSet :
    (ofBasisOfIsModuleTopology v b hb).baseSet = Set.univ := by
  rfl

@[simp]
theorem ofBasisOfIsModuleTopology_source :
    (ofBasisOfIsModuleTopology v b hb).source = Set.univ := by
  rfl

@[simp]
theorem ofBasisOfIsModuleTopology_target :
    (ofBasisOfIsModuleTopology v b hb).target = Set.univ := by
  rfl

theorem ofBasisOfIsModuleTopology_apply (z : TotalSpace F E) :
    ofBasisOfIsModuleTopology v b hb z = (z.proj, v.equivFun.symm ((b z.proj).equivFun z.2)) := by
  rfl

theorem ofBasisOfIsModuleTopology_symm_apply (x : B) (w : F) :
    (ofBasisOfIsModuleTopology v b hb).symm x w = (b x).equivFun.symm (v.equivFun w) := by
  have h := (ofBasisOfIsModuleTopology v b hb).mk_symm (b := x) (by simp) w
  exact TotalSpace.mk_injective x h

@[simp]
theorem ofBasisOfIsModuleTopology_toOpenPartialHomeomorph_symm_apply (p : B × F) :
    (ofBasisOfIsModuleTopology v b hb).toOpenPartialHomeomorph.symm p =
      ⟨p.1, (b p.1).equivFun.symm (v.equivFun p.2)⟩ := by
  rfl

/-- The inverse trivialization is finite linear combination of the frame sections. -/
theorem ofBasisOfIsModuleTopology_symm_apply_eq_sum [Fintype ι] (x : B) (w : F) :
    (ofBasisOfIsModuleTopology v b hb).symm x w = ∑ i, v.repr w i • b x i := by
  rw [ofBasisOfIsModuleTopology_symm_apply, Basis.equivFun_symm_apply]
  rfl

@[simp]
theorem ofBasisOfIsModuleTopology_apply_basis (x : B) (i : ι) :
    ofBasisOfIsModuleTopology v b hb ⟨x, b x i⟩ = (x, v i) := by
  classical
  simp only [ofBasisOfIsModuleTopology_apply, Basis.equivFun_apply, Basis.repr_self]
  congr 1
  apply v.equivFun.injective
  simp [Basis.equivFun_apply]

@[simp]
theorem ofBasisOfIsModuleTopology_symm_basis (x : B) (i : ι) :
    (ofBasisOfIsModuleTopology v b hb).symm x (v i) = b x i := by
  classical
  rw [ofBasisOfIsModuleTopology_symm_apply]
  apply (b x).equivFun.injective
  simp [Basis.equivFun_apply]

theorem ofBasisOfIsModuleTopology_linearEquivAt (x : B)
    (hx : x ∈ (ofBasisOfIsModuleTopology v b hb).baseSet) :
    (ofBasisOfIsModuleTopology v b hb).linearEquivAt 𝕜 x hx =
      (b x).equivFun.trans v.equivFun.symm := by
  ext w
  rfl

end OfBasisOfIsModuleTopology

section OfBasis

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {ι : Type uι} [Finite ι]
  (v : Basis ι 𝕜 F) (b : ∀ x, Basis ι 𝕜 (E x))
  (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))

instance ofBasis.isLinear : (ofBasis v b hb).IsLinear 𝕜 where
  linear x _ := ((b x).equivFun.trans v.equivFun.symm).toLinearMap.isLinear

@[simp]
theorem ofBasis_baseSet : (ofBasis v b hb).baseSet = Set.univ := by
  rfl

@[simp]
theorem ofBasis_source : (ofBasis v b hb).source = Set.univ := by
  rfl

@[simp]
theorem ofBasis_target : (ofBasis v b hb).target = Set.univ := by
  rfl

theorem ofBasis_apply (z : TotalSpace F E) :
    ofBasis v b hb z = (z.proj, v.equivFun.symm ((b z.proj).equivFun z.2)) := by
  rfl

theorem ofBasis_symm_apply (x : B) (w : F) :
    (ofBasis v b hb).symm x w = (b x).equivFun.symm (v.equivFun w) := by
  have h := (ofBasis v b hb).mk_symm (b := x) (by simp) w
  exact TotalSpace.mk_injective x h

@[simp]
theorem ofBasis_toOpenPartialHomeomorph_symm_apply (p : B × F) :
    (ofBasis v b hb).toOpenPartialHomeomorph.symm p =
      ⟨p.1, (b p.1).equivFun.symm (v.equivFun p.2)⟩ := by
  rfl

/-- The inverse trivialization is finite linear combination of the frame sections. -/
theorem ofBasis_symm_apply_eq_sum [Fintype ι] (x : B) (w : F) :
    (ofBasis v b hb).symm x w = ∑ i, v.repr w i • b x i := by
  rw [ofBasis_symm_apply, Basis.equivFun_symm_apply]
  rfl

@[simp]
theorem ofBasis_apply_basis (x : B) (i : ι) :
    ofBasis v b hb ⟨x, b x i⟩ = (x, v i) := by
  classical
  simp only [ofBasis_apply, Basis.equivFun_apply, Basis.repr_self]
  congr 1
  apply v.equivFun.injective
  simp [Basis.equivFun_apply]

@[simp]
theorem ofBasis_symm_basis (x : B) (i : ι) :
    (ofBasis v b hb).symm x (v i) = b x i := by
  classical
  rw [ofBasis_symm_apply]
  apply (b x).equivFun.injective
  simp [Basis.equivFun_apply]

theorem ofBasis_linearEquivAt (x : B) (hx : x ∈ (ofBasis v b hb).baseSet) :
    (ofBasis v b hb).linearEquivAt 𝕜 x hx =
      (b x).equivFun.trans v.equivFun.symm := by
  ext w
  rfl

end OfBasis

section Compatibility

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsModuleTopology 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {ι : Type uι} [Finite ι]

/-- The complete-field construction agrees as a trivialization with the construction using
the model's module topology. -/
theorem ofBasis_eq_ofBasisOfIsModuleTopology
    (v : Basis ι 𝕜 F) (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    ofBasis v b hb = ofBasisOfIsModuleTopology v b hb := by
  rfl

end Compatibility

section Ext

variable {R : Type u𝕜} [Semiring R]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [TopologicalSpace (TotalSpace F E)] {ι : Type uι}

/-- Two all-base linear trivializations agree if they agree on a basis in every fiber. -/
theorem ext_of_eq_on_basis
    {e e' : Trivialization F (π F E)} [e.IsLinear R] [e'.IsLinear R]
    (he : e.baseSet = Set.univ) (he' : e'.baseSet = Set.univ)
    (b : ∀ x, Basis ι R (E x))
    (h : ∀ x i, (e ⟨x, b x i⟩).2 = (e' ⟨x, b x i⟩).2) : e = e' := by
  have hlin (x : B) :
      (e.linearEquivAt R x (by rw [he]; trivial)).toLinearMap =
        (e'.linearEquivAt R x (by rw [he']; trivial)).toLinearMap :=
    (b x).ext (h x)
  have hforward (z : TotalSpace F E) : e z = e' z := by
    apply Prod.ext
    · exact (e.coe_fst' (by rw [he]; trivial)).trans
        (e'.coe_fst' (by rw [he']; trivial)).symm
    · exact DFunLike.congr_fun (hlin z.proj) z.2
  apply Trivialization.ext' _ _ _ (he.trans he'.symm)
  apply OpenPartialHomeomorph.ext _ _ hforward
  · intro p
    apply e.toOpenPartialHomeomorph.injOn
    · exact e.mem_source.mpr (by rw [he]; trivial)
    · exact e.mem_source.mpr (by rw [he]; trivial)
    · change e (e.toOpenPartialHomeomorph.symm p) =
        e (e'.toOpenPartialHomeomorph.symm p)
      calc
        _ = p := e.apply_symm_apply (e.mem_target.mpr (by rw [he]; trivial))
        _ = e' (e'.toOpenPartialHomeomorph.symm p) :=
          (e'.apply_symm_apply (e'.mem_target.mpr (by rw [he']; trivial))).symm
        _ = _ := (hforward _).symm
  · rw [e.source_eq, e'.source_eq, he, he']

end Ext

section TrivialOfIsModuleTopology

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsModuleTopology 𝕜 F]
  {ι : Type uι} [Finite ι]

/-- A constant frame on a trivial bundle gives its standard trivialization. -/
@[simp]
theorem ofBasisOfIsModuleTopology_trivial (v : Basis ι 𝕜 F)
    (hv : ∀ i, Continuous
      (fun x : B ↦ TotalSpace.mk' F (E := Bundle.Trivial B F) x (v i))) :
    ofBasisOfIsModuleTopology v (fun _ : B ↦ v) hv = Bundle.Trivial.trivialization B F := by
  apply ext_of_eq_on_basis (R := 𝕜) (by simp) rfl (fun _ ↦ v)
  intro x i
  rw [ofBasisOfIsModuleTopology_apply_basis]
  rfl

end TrivialOfIsModuleTopology

section Trivial

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type uι} [Finite ι]

/-- A constant frame on a trivial bundle gives its standard trivialization. -/
@[simp]
theorem ofBasis_trivial (v : Basis ι 𝕜 F)
    (hv : ∀ i, Continuous
      (fun x : B ↦ TotalSpace.mk' F (E := Bundle.Trivial B F) x (v i))) :
    ofBasis v (fun _ : B ↦ v) hv = Bundle.Trivial.trivialization B F := by
  apply ext_of_eq_on_basis (R := 𝕜) (by simp) rfl (fun _ ↦ v)
  intro x i
  rw [ofBasis_apply_basis]
  rfl

end Trivial

end Bundle.Trivialization

namespace VectorBundle

section BasisOfIsModuleTopology

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [hIMT : IsModuleTopology 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [hFB : FiberBundle F E] [hVB : VectorBundle 𝕜 F E]
  {ι : Type uι} [hι : Finite ι]

include hIMT hFB hVB hι

/-- A vector bundle is globally linearly trivial if and only if it has a continuous finite
frame indexed by a basis of the model fiber.

This is the finite-frame characterization in Hatcher,
*Vector Bundles and K-Theory*, §1.1, p. 8. -/
theorem exists_global_trivialization_iff_basis_of_isModuleTopology (v : Basis ι 𝕜 F) :
    (∃ e : Trivialization F (π F E), e.baseSet = Set.univ ∧ e.IsLinear 𝕜) ↔
      ∃ b : ∀ x, Basis ι 𝕜 (E x),
        ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)) := by
  constructor
  · rintro ⟨e, he, hlinear⟩
    let : e.IsLinear 𝕜 := hlinear
    let b : ∀ x, Basis ι 𝕜 (E x) := fun x ↦
      v.map (e.linearEquivAt 𝕜 x (he ▸ Set.mem_univ x)).symm
    refine ⟨b, fun i ↦ ?_⟩
    have hc : Continuous (fun p : B × F ↦ TotalSpace.mk' F p.1 (e.symm p.1 p.2)) :=
      continuousOn_univ.mp (by simpa [he] using e.continuousOn_symm)
    simpa [Function.comp_def, b, Trivialization.linearEquivAt_symm_apply] using
      hc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : B ↦ v i)))
  · rintro ⟨b, hb⟩
    exact ⟨Trivialization.ofBasisOfIsModuleTopology v b hb,
      Trivialization.ofBasisOfIsModuleTopology_baseSet v b hb, inferInstance⟩

end BasisOfIsModuleTopology

section Basis

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [h𝕜 : CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [hFB : FiberBundle F E] [hVB : VectorBundle 𝕜 F E]
  {ι : Type uι} [hι : Finite ι]

include h𝕜 hFB hVB hι

/-- Coordinates in a continuous family of finite fiberwise bases are continuous on the total
space. No choice of model basis or nonempty base is part of the statement.

This is the coordinate-map characterization of trivial bundles in Hatcher,
*Vector Bundles and K-Theory*, §1.1, pp. 8–9. -/
theorem continuous_basis_equivFun (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i))) :
    Continuous (fun z : TotalSpace F E ↦ (b z.proj).equivFun z.2) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  let v : Basis ι 𝕜 F :=
    (b p.proj).map (VectorBundle.continuousLinearEquivAt 𝕜 F E p.proj).toLinearEquiv
  let : FiniteDimensional 𝕜 F := v.finiteDimensional_of_finite
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  exact continuousAt_basis_equivFun_of_isModuleTopology b hb p

/-- A section is continuous if and only if all of its coefficients in a continuous finite
frame are continuous. -/
theorem continuous_section_iff_basis_coeff (b : ∀ x, Basis ι 𝕜 (E x))
    (hb : ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)))
    (s : ∀ x, E x) :
    Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ↔
      ∀ i, Continuous (fun x ↦ (b x).repr (s x) i) :=
  continuous_section_iff_basis_coeff_of_continuous b hb
    (continuous_basis_equivFun b hb) s

/-- A vector bundle is globally linearly trivial if and only if it has a continuous finite
frame indexed by a basis of the model fiber.

This is the finite-frame characterization in Hatcher,
*Vector Bundles and K-Theory*, §1.1, p. 8. -/
theorem exists_global_trivialization_iff_basis (v : Basis ι 𝕜 F) :
    (∃ e : Trivialization F (π F E), e.baseSet = Set.univ ∧ e.IsLinear 𝕜) ↔
      ∃ b : ∀ x, Basis ι 𝕜 (E x),
        ∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (b x i)) := by
  let : FiniteDimensional 𝕜 F := v.finiteDimensional_of_finite
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  exact exists_global_trivialization_iff_basis_of_isModuleTopology v

end Basis

section LinearIndependentOfIsModuleTopology

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [hIMT : IsModuleTopology 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [hFB : FiberBundle F E] [hVB : VectorBundle 𝕜 F E]
  [hF : FiniteDimensional 𝕜 F] {ι : Type uι} [Fintype ι]

include hIMT hFB hVB hF

/-- A finite-rank bundle is globally linearly trivial if and only if it has a pointwise linearly
independent family of continuous sections whose cardinality is the rank.

The statement includes rank zero: fiberwise basis construction uses
`basisOfLinearIndependentOfCardEqFinrank'`, which has no nonempty-index hypothesis.
See Hatcher, *Vector Bundles and K-Theory*, §1.1, p. 8. -/
theorem exists_global_trivialization_iff_linearIndependent_of_isModuleTopology
    (hι : Fintype.card ι = Module.finrank 𝕜 F) :
    (∃ e : Trivialization F (π F E), e.baseSet = Set.univ ∧ e.IsLinear 𝕜) ↔
      ∃ s : ι → (x : B) → E x,
        (∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (s i x))) ∧
          ∀ x, LinearIndependent 𝕜 (fun i ↦ s i x) := by
  classical
  let (x : B) : AddCommGroup (E x) := Module.addCommMonoidToAddCommGroup 𝕜
  let v : Basis ι 𝕜 F :=
    (Module.finBasis 𝕜 F).reindex (Fintype.equivFinOfCardEq hι).symm
  rw [exists_global_trivialization_iff_basis_of_isModuleTopology v]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun i x ↦ b x i, hb, fun x ↦ (b x).linearIndependent⟩
  · rintro ⟨s, hs, hli⟩
    let (x : B) : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
    let b : ∀ x, Basis ι 𝕜 (E x) := fun x ↦
      basisOfLinearIndependentOfCardEqFinrank' (fun i ↦ s i x) (hli x)
        (hι.trans (VectorBundle.finrank_eq 𝕜 F E x).symm)
    refine ⟨b, fun i ↦ ?_⟩
    simpa [b] using hs i

end LinearIndependentOfIsModuleTopology

section LinearIndependent

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [h𝕜 : CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [hFB : FiberBundle F E] [hVB : VectorBundle 𝕜 F E]
  [hF : FiniteDimensional 𝕜 F] {ι : Type uι} [Fintype ι]

include h𝕜 hFB hVB hF

/-- A finite-rank bundle is globally linearly trivial if and only if it has a pointwise linearly
independent family of continuous sections whose cardinality is the rank.

The statement includes rank zero: fiberwise basis construction uses
`basisOfLinearIndependentOfCardEqFinrank'`, which has no nonempty-index hypothesis.
See Hatcher, *Vector Bundles and K-Theory*, §1.1, p. 8. -/
theorem exists_global_trivialization_iff_linearIndependent
    (hι : Fintype.card ι = Module.finrank 𝕜 F) :
    (∃ e : Trivialization F (π F E), e.baseSet = Set.univ ∧ e.IsLinear 𝕜) ↔
      ∃ s : ι → (x : B) → E x,
        (∀ i, Continuous (fun x ↦ TotalSpace.mk' F x (s i x))) ∧
          ∀ x, LinearIndependent 𝕜 (fun i ↦ s i x) := by
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  exact exists_global_trivialization_iff_linearIndependent_of_isModuleTopology hι

end LinearIndependent

end VectorBundle
