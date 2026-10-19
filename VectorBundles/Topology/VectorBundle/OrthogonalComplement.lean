/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Orthogonal families of submodules in vector bundles

For a Hermitian metric `g`, the orthogonal family of a submodule family `S` is
`fun b ↦ (S b).orthogonalBilin (g.inner b).toLinearMap₁₂`. This uses Mathlib's
sesquilinear orthogonal complement without choosing new norms on the fibers.
Its fibers retain their subtype topologies, and its total topology is induced
by inclusion in the original ambient total space.

The submodule family is assumed to be an intrinsic vector bundle whose total
inclusion is an embedding. Neither adapted ambient charts nor a continuously
varying projection is part of this input. The finite-dimensional ambient model
may have an arbitrary norm. The subbundle model is finite-dimensional whenever
the base has a point; no such restriction is needed on an empty base.

Projection continuity and the addition/decomposition homeomorphism are separate
assertions, not input assumptions of the bundle construction below.

## Implementation notes

An intrinsic subbundle chart gives a finite family of continuous ambient sections.
Pairing against these sections describes the orthogonal family as kernels of a
continuous family of surjections between fixed model spaces. A right inverse at
one base point identifies nearby kernels as graphs over that fixed kernel. The
resulting linear charts are homeomorphisms for the ambient-induced total topology.
Finite-dimensionality of the subbundle model is obtained separately at each chart's
base point, so the construction also applies to an empty base with an infinite-dimensional
subbundle model. No metric-induced replacement of a fiber topology is used.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Proposition 1.3,
  pp. 12–13. The given-metric assertion separates the part after metric choice
  from the paracompact-base existence statement, and uses `RCLike` scalars.
* Mathlib's sesquilinear orthogonal complements, by Moritz Doll, Christopher
  Hoskin and Martin Winter, and inner-product orthogonal complements, by
  Zhouhang Zhou, Sébastien Gouëzel and Frédéric Dupuis.
-/

@[expose] public section

open Bundle

/-- The sesquilinear orthogonal complement for the continuous inner product
agrees with the inner-product-space orthogonal complement, over either scalar field. -/
theorem Submodule.orthogonalBilin_innerSL {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (S : Submodule 𝕜 V) :
    S.orthogonalBilin (innerSL 𝕜).toLinearMap₁₂ = S.orthogonal := by
  ext v
  rfl

namespace VectorBundle

section SubmoduleModel

variable {𝕜 B F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type*} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]

include F E S

/-- A model for an intrinsic bundle of submodules of a finite-rank vector bundle
is finite-dimensional if a base point is available. -/
theorem finiteDimensional_of_submodule (b : B) : FiniteDimensional 𝕜 G := by
  let := VectorBundle.finiteDimensional 𝕜 F E b
  exact (VectorBundle.continuousLinearEquivAt 𝕜 G (fun b ↦ S b) b).toLinearEquiv.finiteDimensional

/-- At any base point, the rank of a submodule-bundle model is at most the
ambient model rank. No global nonemptiness assumption on the base is needed. -/
theorem finrank_model_le_of_submodule (b : B) : Module.finrank 𝕜 G ≤ Module.finrank 𝕜 F := by
  let := VectorBundle.finiteDimensional 𝕜 F E b
  rw [← VectorBundle.finrank_eq 𝕜 G (fun b ↦ S b) b,
    ← VectorBundle.finrank_eq 𝕜 F E b]
  exact (S b).finrank_le

end SubmoduleModel

end VectorBundle

namespace Bundle.ContinuousHermitianMetric

section KernelGraph

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Kernels near a split surjection are graphs over its fixed kernel. -/
private noncomputable def kernelGraphEquiv
    (D₀ D : X →L[𝕜] Y) (R : Y →L[𝕜] X)
    (h₀ : D₀.comp R = ContinuousLinearMap.id 𝕜 Y)
    (a : Y ≃L[𝕜] Y) (ha : D.comp R = (a : Y →L[𝕜] Y)) :
    D₀.ker ≃L[𝕜] D.ker where
  toFun x := ⟨x - R (a.symm (D x)), by
    change D ((x : X) - R (a.symm (D x))) = 0
    have h (y : Y) : D (R y) = a y := DFunLike.congr_fun ha y
    simp only [map_sub, h, a.apply_symm_apply, sub_self]⟩
  invFun y := ⟨y - R (D₀ y), by
    change D₀ ((y : X) - R (D₀ y)) = 0
    have h (z : Y) : D₀ (R z) = z := DFunLike.congr_fun h₀ z
    simp only [map_sub, h, sub_self]⟩
  left_inv x := by
    apply Subtype.ext
    have h (y : Y) : D₀ (R y) = y := DFunLike.congr_fun h₀ y
    change (x : X) - R (a.symm (D x)) -
      R (D₀ ((x : X) - R (a.symm (D x)))) = x
    have hx : D₀ x = 0 := x.property
    simp only [map_sub, h, hx, zero_sub, map_neg, sub_neg_eq_add]
    abel
  right_inv y := by
    apply Subtype.ext
    have h (z : Y) : D (R z) = a z := DFunLike.congr_fun ha z
    change (y : X) - R (D₀ y) -
      R (a.symm (D ((y : X) - R (D₀ y)))) = y
    have hy : D y = 0 := y.property
    simp only [map_sub, h, hy, zero_sub, map_neg,
      a.symm_apply_apply, sub_neg_eq_add]
    abel
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, smul_sub]
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (R.continuous.comp (a.symm.continuous.comp (D.continuous.comp continuous_subtype_val)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (R.continuous.comp (D₀.continuous.comp continuous_subtype_val))

private noncomputable def fixedKernelProjection
    (D₀ : X →L[𝕜] Y) (R : Y →L[𝕜] X)
    (h₀ : D₀.comp R = ContinuousLinearMap.id 𝕜 Y) : X →L[𝕜] D₀.ker :=
  D₀.projKerOfRightInverse R (fun y ↦ DFunLike.congr_fun h₀ y)

private noncomputable def kernelGraphMap {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (D₀ D : X →L[𝕜] Y) (R : Y →L[𝕜] X) (k : D₀.ker ≃L[𝕜] Z) : Z →L[𝕜] X :=
  (ContinuousLinearMap.id 𝕜 X - R.comp ((D.comp R).inverse.comp D)).comp
    (D₀.ker.subtypeL.comp (k.symm : Z →L[𝕜] D₀.ker))

private theorem kernelGraphMap_properties {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (D₀ D : X →L[𝕜] Y) (R : Y →L[𝕜] X)
    (h₀ : D₀.comp R = ContinuousLinearMap.id 𝕜 Y) (k : D₀.ker ≃L[𝕜] Z)
    (h : (D.comp R).IsInvertible) :
    (∀ z, D (kernelGraphMap D₀ D R k z) = 0) ∧
    (∀ z, k (fixedKernelProjection D₀ R h₀ (kernelGraphMap D₀ D R k z)) = z) ∧
    (∀ y : D.ker, kernelGraphMap D₀ D R k (k (fixedKernelProjection D₀ R h₀ y)) = y) := by
  let a := ContinuousLinearEquiv.equivOfInverse' (D.comp R) (D.comp R).inverse
    h.self_comp_inverse h.inverse_comp_self
  let q := kernelGraphEquiv D₀ D R h₀ a rfl
  have huv (z : Z) : kernelGraphMap D₀ D R k z = (q (k.symm z) : X) := rfl
  have hpv (y : D.ker) : fixedKernelProjection D₀ R h₀ y = q.symm y := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [huv]
    exact (q (k.symm z)).property
  · intro z
    rw [huv, hpv, q.symm_apply_apply, k.apply_symm_apply]
  · intro y
    rw [huv, hpv, k.symm_apply_apply, q.apply_symm_apply]

private theorem continuousOn_operatorInverse {T : Type*} [TopologicalSpace T]
    [CompleteSpace Y] {A : T → Y →L[𝕜] Y} {U : Set T}
    (hA : ContinuousOn A U) (hU : ∀ b ∈ U, (A b).IsInvertible) :
    ContinuousOn (fun b ↦ (A b).inverse) U := by
  intro b hb
  have hi : ContinuousAt ContinuousLinearMap.inverse (A b) := by
    rw [← ContinuousLinearMap.ringInverse_eq_inverse]
    obtain ⟨a, ha⟩ := hU b hb
    rw [← ha]
    exact NormedRing.inverse_continuousAt a.toUnit
  exact hi.comp_continuousWithinAt (hA b hb)

private theorem finrank_kernel_of_rightInverse [FiniteDimensional 𝕜 X]
    (D : X →L[𝕜] Y) (R : Y →L[𝕜] X)
    (hR : D.comp R = ContinuousLinearMap.id 𝕜 Y) :
    Module.finrank 𝕜 D.ker = Module.finrank 𝕜 X - Module.finrank 𝕜 Y := by
  have hd := D.toLinearMap.finrank_range_add_finrank_ker
  have hs : Function.Surjective D := fun z ↦ ⟨R z, DFunLike.congr_fun hR z⟩
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hd
  omega

end KernelGraph

section OrthogonalBundle

variable {𝕜 B F G : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type*} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]

local notation "C" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g b)) (S b))
local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))
local notation "tC" => TopologicalSpace.induced
  (fun p : TotalSpace H C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance

omit [VectorBundle 𝕜 F E] in
private theorem continuousOn_chartVector
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (v : F) :
    ContinuousOn (fun b ↦ TotalSpace.mk' F b (e.symmL 𝕜 b v)) e.baseSet := by
  have hc : ContinuousOn (fun b ↦ TotalSpace.mk' F b (e.symm b v)) e.baseSet :=
    e.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hb ↦ ⟨hb, Set.mem_univ _⟩)
  exact hc.congr (fun b hb ↦ by rw [e.symmL_apply hb])

private noncomputable def localAnnihilator {ι : Type*} [Fintype ι]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : Trivialization G (π G (fun b ↦ S b))) [f.IsLinear 𝕜]
    (w : ι → G) (b : B) : F →L[𝕜] (ι → 𝕜) :=
  ContinuousLinearMap.pi fun i ↦
    (g.inner b (f.symmL 𝕜 b (w i))).comp (e.symmL 𝕜 b)

private theorem continuousOn_localAnnihilator [FiniteDimensional 𝕜 F]
    {ι : Type*} [Fintype ι]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (hS : Topology.IsEmbedding
      (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : Trivialization G (π G (fun b ↦ S b))) [f.IsLinear 𝕜]
    (w : ι → G) :
    ContinuousOn (localAnnihilator g S e f w) (e.baseSet ∩ f.baseSet) := by
  rw [continuousOn_clm_apply]
  intro v
  apply continuousOn_pi.mpr
  intro i
  exact g.continuousOn_inner
    ((hS.continuous.comp_continuousOn
      (continuousOn_chartVector (E := fun b ↦ S b) f (w i))).mono
        Set.inter_subset_right)
    ((continuousOn_chartVector e v).mono Set.inter_subset_left)

private theorem localAnnihilator_eq_zero_iff {ι : Type*} [Fintype ι]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : Trivialization G (π G (fun b ↦ S b))) [f.IsLinear 𝕜]
    (w : Module.Basis ι 𝕜 G) {b : B} (he : b ∈ e.baseSet) (hf : b ∈ f.baseSet) (v : E b) :
    localAnnihilator g S e f w b (e.continuousLinearMapAt 𝕜 b v) = 0 ↔ v ∈ C b := by
  have happ (i : ι) :
      localAnnihilator g S e f w b (e.continuousLinearMapAt 𝕜 b v) i =
        g.inner b (f.symmL 𝕜 b (w i)) v := by
    change g.inner b (f.symmL 𝕜 b (w i))
      (e.symmL 𝕜 b (e.continuousLinearMapAt 𝕜 b v)) = _
    rw [e.symmL_continuousLinearMapAt he]
  constructor
  · intro h
    let l : G →ₛₗ[starRingEnd 𝕜] 𝕜 :=
      ((g.inner b).toLinearMap₁₂.flip v).comp ((S b).subtype.comp (f.symmₗ 𝕜 b))
    have hl : l = 0 := w.ext fun i ↦ by
      have hi := congrFun h i
      rw [happ] at hi
      simpa [l, Trivialization.symmL] using hi
    intro s hs
    have hz := DFunLike.congr_fun hl (f.continuousLinearMapAt 𝕜 b ⟨s, hs⟩)
    simpa [l, Trivialization.continuousLinearMapAt,
      f.symmₗ_linearMapAt hf] using hz
  · intro h
    ext i
    rw [happ]
    exact h _ (f.symmL 𝕜 b (w i)).property

private theorem localAnnihilator_hasRightInverse {ι : Type*} [Fintype ι]
    [FiniteDimensional 𝕜 G]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : Trivialization G (π G (fun b ↦ S b))) [f.IsLinear 𝕜]
    (w : Module.Basis ι 𝕜 G) {b : B} (he : b ∈ e.baseSet) (hf : b ∈ f.baseSet) :
    ∃ R : (ι → 𝕜) →L[𝕜] F,
      (localAnnihilator g S e f w b).comp R = ContinuousLinearMap.id 𝕜 (ι → 𝕜) := by
  let ew := w.equivFun.toContinuousLinearEquiv
  let es := f.continuousLinearEquivAt 𝕜 b hf
  let ea := e.continuousLinearEquivAt 𝕜 b he
  let L : (ι → 𝕜) →L[𝕜] F :=
    (ea : E b →L[𝕜] F).comp ((S b).subtypeL.comp
      ((es.symm : G →L[𝕜] S b).comp (ew.symm : (ι → 𝕜) →L[𝕜] G)))
  let A := (localAnnihilator g S e f w b).comp L
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    let s : S b := es.symm (ew.symm u)
    change localAnnihilator g S e f w b (ea s) = 0 at hu
    have hu' : localAnnihilator g S e f w b
        (e.continuousLinearMapAt 𝕜 b s) = 0 := by
      rw [← e.coe_continuousLinearEquivAt_eq' he]
      exact hu
    have hs : (s : E b) ∈ C b :=
      (localAnnihilator_eq_zero_iff g S e f w he hf s).mp hu'
    have hs0 : s = 0 := Subtype.ext
      ((g.toHermitianMetric.inner_self_eq_zero_iff b s).mp (hs s s.property))
    have hu0 : ew.symm u = 0 := es.symm.injective (by simpa [s] using hs0)
    exact ew.symm.injective (by simpa using hu0)
  let a : (ι → 𝕜) ≃L[𝕜] (ι → 𝕜) :=
    (LinearEquiv.ofBijective A.toLinearMap
      ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
  refine ⟨L.comp (a.symm : (ι → 𝕜) →L[𝕜] (ι → 𝕜)), ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  exact a.apply_symm_apply u

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

local notation "tK" => TopologicalSpace.induced
  (fun p : TotalSpace K C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance

private noncomputable def orthogonalChart
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (U : Set B) (hUo : IsOpen U) (hU : U ⊆ e.baseSet)
    (u : B → K →L[𝕜] F) (p : F →L[𝕜] K)
    (hu : ContinuousOn u U)
    (hmem : ∀ b ∈ U, ∀ z, e.symmL 𝕜 b (u b z) ∈ C b)
    (hpu : ∀ b ∈ U, ∀ z, p (u b z) = z)
    (hup : ∀ b ∈ U, ∀ v : C b,
      u b (p (e.continuousLinearMapAt 𝕜 b v)) = e.continuousLinearMapAt 𝕜 b v) :
    @Trivialization B K _ _ _ tK (π K C) := by
  classical
  letI : TopologicalSpace (TotalSpace K C) := tK
  let j : TotalSpace K C → TotalSpace F E := fun x ↦ ⟨x.proj, x.2⟩
  have hj : Topology.IsInducing j := ⟨rfl⟩
  have hp : Continuous (π K C) := (FiberBundle.continuous_proj F E).comp hj.continuous
  let inv : B × K → TotalSpace K C := fun q ↦
    ⟨q.1, if h : q.1 ∈ U then ⟨e.symmL 𝕜 q.1 (u q.1 q.2), hmem q.1 h q.2⟩ else 0⟩
  refine
    { toFun := fun x ↦ (x.proj, p (e.continuousLinearMapAt 𝕜 x.proj x.2))
      invFun := inv
      source := (π K C) ⁻¹' U
      target := U ×ˢ Set.univ
      map_source' := fun _ hx ↦ ⟨hx, Set.mem_univ _⟩
      map_target' := fun _ hq ↦ hq.1
      left_inv' := ?_
      right_inv' := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      open_source := hUo.preimage hp
      open_target := hUo.prod isOpen_univ
      baseSet := U
      open_baseSet := hUo
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  · rintro ⟨b, v⟩ hb
    change b ∈ U at hb
    dsimp only [inv]
    simp only [dite_eq_left hb]
    apply congrArg (fun z : C b ↦ (⟨b, z⟩ : TotalSpace K C))
    apply Subtype.ext
    change e.symmL 𝕜 b (u b (p (e.continuousLinearMapAt 𝕜 b v))) = v
    rw [hup b hb v, e.symmL_continuousLinearMapAt (hU hb)]
  · rintro ⟨b, z⟩ hb
    dsimp only [inv]
    rw [dite_eq_left hb.1]
    apply Prod.ext
    · rfl
    change p (e.continuousLinearMapAt 𝕜 b (e.symmL 𝕜 b (u b z))) = z
    rw [e.continuousLinearMapAt_symmL (hU hb.1), hpu b hb.1 z]
  · have hc : ContinuousOn (fun x : TotalSpace K C ↦ e (j x)) ((π K C) ⁻¹' U) :=
      e.continuousOn.comp hj.continuous.continuousOn (fun _ hx ↦ e.mem_source.mpr (hU hx))
    refine hp.continuousOn.prodMk ?_
    apply (p.continuous.comp_continuousOn hc.snd).congr
    intro x hx
    dsimp only [Function.comp_def]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e (hU hx)]
  · apply hj.continuousOn_iff.mpr
    have hpair : ContinuousOn (fun q : B × K ↦ (q.1, u q.1 q.2)) (U ×ˢ Set.univ) :=
      continuousOn_fst.prodMk
        ((hu.comp continuousOn_fst (fun _ hq ↦ hq.1)).clm_apply continuousOn_snd)
    have hc := e.continuousOn_symm.comp hpair (fun _ hq ↦ ⟨hU hq.1, Set.mem_univ _⟩)
    apply hc.congr
    rintro ⟨b, z⟩ hb
    dsimp [Function.comp_def, j, inv]
    rw [dite_eq_left hb.1]
    simp only [e.symmL_apply (hU hb.1)]

omit [TopologicalSpace (TotalSpace G (fun b ↦ S b))] in
private theorem orthogonalChart_isLinear
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (U : Set B) (hUo : IsOpen U) (hU : U ⊆ e.baseSet)
    (u : B → K →L[𝕜] F) (p : F →L[𝕜] K)
    (hu : ContinuousOn u U)
    (hmem : ∀ b ∈ U, ∀ z, e.symmL 𝕜 b (u b z) ∈ C b)
    (hpu : ∀ b ∈ U, ∀ z, p (u b z) = z)
    (hup : ∀ b ∈ U, ∀ v : C b,
      u b (p (e.continuousLinearMapAt 𝕜 b v)) = e.continuousLinearMapAt 𝕜 b v) :
    @Trivialization.IsLinear 𝕜 B K C _ _ _ tK _ _ _ _
      (orthogonalChart g S e U hUo hU u p hu hmem hpu hup) := by
  let : TopologicalSpace (TotalSpace K C) := tK
  constructor
  intro b hb
  change IsLinearMap 𝕜 (fun v : C b ↦ p (e.continuousLinearMapAt 𝕜 b v))
  constructor
  · intro x y
    simp only [Submodule.coe_add, map_add]
  · intro c x
    simp only [Submodule.coe_smul, map_smul]

set_option maxHeartbeats 300000 in
-- Transporting the two bundle charts and the finite-dimensional kernel coordinates requires
-- a larger elaboration budget, even with the operator and graph calculations separated above.
private theorem exists_orthogonalChart [FiniteDimensional 𝕜 F]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (hS : Topology.IsEmbedding
      (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))
    (b₀ : B) :
    ∃ c : @Trivialization B H _ _ _ tC (π H C),
      b₀ ∈ @Trivialization.baseSet B H (TotalSpace H C) _ _ tC _ c ∧
      @Trivialization.IsLinear 𝕜 B H C _ _ _ tC _ _ _ _ c := by
  let : TopologicalSpace (TotalSpace H C) := tC
  let : FiniteDimensional 𝕜 G :=
    VectorBundle.finiteDimensional_of_submodule (F := F) S b₀
  let e := trivializationAt F E b₀
  let f := trivializationAt G (fun b ↦ S b) b₀
  let w := Module.finBasis 𝕜 G
  let J := Fin (Module.finrank 𝕜 G) → 𝕜
  let D : B → F →L[𝕜] J := localAnnihilator g S e f w
  have hD : ContinuousOn D (e.baseSet ∩ f.baseSet) :=
    continuousOn_localAnnihilator g S hS e f w
  have he₀ : b₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E b₀
  have hf₀ : b₀ ∈ f.baseSet := mem_baseSet_trivializationAt G (fun b ↦ S b) b₀
  obtain ⟨R, hR⟩ := localAnnihilator_hasRightInverse g S e f w he₀ hf₀
  let D₀ := D b₀
  let A : B → J →L[𝕜] J := fun b ↦ (D b).comp R
  have hA : ContinuousOn A (e.baseSet ∩ f.baseSet) := hD.clm_comp continuousOn_const
  let U := (e.baseSet ∩ f.baseSet) ∩ {b | (A b).IsInvertible}
  have hUo : IsOpen U := hA.isOpen_inter_preimage
    (e.open_baseSet.inter f.open_baseSet) ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have h₀ : (A b₀).IsInvertible := by
    change (D₀.comp R).IsInvertible
    rw [hR]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 J, rfl⟩
  have hb₀ : b₀ ∈ U := ⟨⟨he₀, hf₀⟩, h₀⟩
  have hInv : ContinuousOn (fun b ↦ (A b).inverse) U :=
    continuousOn_operatorInverse (hA.mono Set.inter_subset_left) (fun _ hb ↦ hb.2)
  have hdim : Module.finrank 𝕜 D₀.ker = Module.finrank 𝕜 F - Module.finrank 𝕜 G := by
    simpa only [J, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      finrank_kernel_of_rightInverse D₀ R hR
  let k : D₀.ker ≃L[𝕜] H := ContinuousLinearEquiv.ofFinrankEq (by
    rw [hdim, finrank_euclideanSpace, Fintype.card_fin])
  let p : F →L[𝕜] H := (k : D₀.ker →L[𝕜] H).comp (fixedKernelProjection D₀ R hR)
  let u : B → H →L[𝕜] F := fun b ↦ kernelGraphMap D₀ (D b) R k
  have hu : ContinuousOn u U :=
    (continuousOn_const.sub
      (continuousOn_const.clm_comp (hInv.clm_comp (hD.mono Set.inter_subset_left)))).clm_comp
        continuousOn_const
  have hg (b : B) (hb : b ∈ U) := kernelGraphMap_properties D₀ (D b) R hR k hb.2
  have hmem (b : B) (hb : b ∈ U) (z : H) : e.symmL 𝕜 b (u b z) ∈ C b := by
    apply (localAnnihilator_eq_zero_iff g S e f w hb.1.1 hb.1.2 _).mp
    rw [e.continuousLinearMapAt_symmL hb.1.1]
    exact (hg b hb).1 z
  have hup (b : B) (hb : b ∈ U) (v : C b) :
      u b (p (e.continuousLinearMapAt 𝕜 b v)) = e.continuousLinearMapAt 𝕜 b v :=
    (hg b hb).2.2 ⟨e.continuousLinearMapAt 𝕜 b v,
      (localAnnihilator_eq_zero_iff g S e f w hb.1.1 hb.1.2 v).mpr v.property⟩
  let c := orthogonalChart g S e U hUo (fun _ hb ↦ hb.1.1) u p hu
    hmem (fun b hb ↦ (hg b hb).2.1) hup
  exact ⟨c, hb₀, orthogonalChart_isLinear g S e U hUo (fun _ hb ↦ hb.1.1) u p hu
    hmem (fun b hb ↦ (hg b hb).2.1) hup⟩

/-- The orthogonal family of an embedded intrinsic submodule bundle, with its
original fiber subtype topologies and induced ambient total-space topology, has
fiber-bundle data and a vector-bundle structure. The model has dimension equal
to the ambient rank minus the subbundle rank.

This is the given-metric part of Hatcher's Proposition 1.3 over `RCLike` scalars;
no separation or paracompactness assumption on the base is required. -/
@[no_expose] noncomputable def orthogonalBundle [FiniteDimensional 𝕜 F]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (hS : Topology.IsEmbedding
      (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj))) :
    Σ' fb : @FiberBundle B H _ _ C tC _,
      @VectorBundle 𝕜 B H C _ _ _ _ _ _ tC _ fb := by
  classical
  letI : TopologicalSpace (TotalSpace H C) := tC
  let j : TotalSpace H C → TotalSpace F E := fun x ↦ ⟨x.proj, x.2⟩
  have hj : Topology.IsInducing j := ⟨rfl⟩
  choose c hc hlin using exists_orthogonalChart g S hS
  let fb : FiberBundle H C :=
    { totalSpaceMk_isInducing' := fun b ↦ hj.of_comp_iff.mp
        ((FiberBundle.totalSpaceMk_isInducing F E b).comp Topology.IsInducing.subtypeVal)
      trivializationAtlas' := Set.range c
      trivializationAt' := c
      mem_baseSet_trivializationAt' := hc
      trivialization_mem_atlas' := fun b ↦ ⟨b, rfl⟩ }
  letI := fb
  refine ⟨fb, { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }⟩
  · intro e he
    obtain ⟨b, rfl⟩ := he.out
    exact hlin b
  · intro e e' he he'
    let : e.IsLinear 𝕜 := by
      obtain ⟨b, rfl⟩ := he.out
      exact hlin b
    let : e'.IsLinear 𝕜 := by
      obtain ⟨b, rfl⟩ := he'.out
      exact hlin b
    rw [continuousOn_clm_apply]
    intro v
    have hs : ContinuousOn (fun b ↦ TotalSpace.mk' H b (e.symm b v)) e.baseSet :=
      e.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
        (fun _ hb ↦ ⟨hb, Set.mem_univ _⟩)
    have ht := e'.continuousOn.comp (hs.mono Set.inter_subset_left)
      (fun b hb ↦ e'.mem_source.mpr hb.2)
    exact ht.snd.congr (fun b hb ↦ e.coordChangeL_apply e' hb v)

end OrthogonalBundle

end Bundle.ContinuousHermitianMetric
