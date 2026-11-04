/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Data.Bundle
public import VectorBundles.Topology.Maps.FiberwiseProjection
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas.FiniteAmbient
public import VectorBundles.Topology.VectorBundle.FiniteRank.ConstantRank
public import StableRange.Module.SplitSurjectiveRank

/-!
# Complementary range bundles of split families

For a family of algebraic split embeddings into a finite-dimensional normed space, the ranges
of the complementary projectors carry their inherited fibre topologies and a finite-rank atlas
for the range-graph total-space topology, without a common model for the original fibres.
When the original fibres have a common model, the complementary rank is the ambient dimension
minus that model dimension.

The complementary range atlas gives fixed-model fibre-bundle data and a vector-bundle mixin
for those exact data. Changing the total-space model tag preserves the base point and ambient
vector in both directions, and uses the topology transported from the range total space.
-/

@[expose] public section

universe uK uB uA uP uF uE

namespace VectorBundle

attribute [local instance] VectorBundle.rangeTotalSpaceTopology

/-- A finite-rank atlas on the complementary ranges of an algebraic split family, with
inherited fibre topologies and the range-graph total-space topology. The original fibres need
not admit a common model or have constant rank. -/
noncomputable def complementaryRangeFiniteRankAtlas
    (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
    (B : Type uB) [TopologicalSpace B]
    (A : Type uA) [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
    (P : Type uP)
    (E : B → Type uE) [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
    (β : ∀ b, E b →ₗ[K] A)
    (ρ : ∀ b, A →ₗ[K] E b)
    (hρβ : ∀ b (v : E b), ρ b (β b v) = v)
    [tTotal : TopologicalSpace (Bundle.TotalSpace P E)]
    (hβTotal : Continuous (fun z : Bundle.TotalSpace P E => (z.proj, β z.proj z.snd)))
    (hρTotal : Continuous (fun y : B × A =>
      (Bundle.TotalSpace.mk y.1 (ρ y.1 y.2) : Bundle.TotalSpace P E))) :
    @Bundle.FiniteRankAtlas.{_, _, _, _, uB} K _ _ B _ P
      (fun b => LinearMap.range (LinearMap.id - (β b).comp (ρ b))) _ _ _
      (VectorBundle.rangeTotalSpaceTopology (F := P)
        (fun b => LinearMap.id - (β b).comp (ρ b))) := by
  let Q : B → A →ₗ[K] A := fun b => LinearMap.id - (β b).comp (ρ b)
  classical
  letI := Bundle.TotalSpace.fiberAddCommMonoid (E := E) P
  letI := Bundle.TotalSpace.fiberModule (E := E) K P
  let p : Bundle.TotalSpace P E → B := fun z => z.proj
  let ePack (b : B) : E b ≃ₗ[K] {z : Bundle.TotalSpace P E // p z = b} :=
    Bundle.TotalSpace.fiberLinearEquiv (E := E) K P b
  let βraw (b : B) : {z : Bundle.TotalSpace P E // p z = b} →ₗ[K] A :=
    (β b).comp (ePack b).symm.toLinearMap
  let ρraw (b : B) : A →ₗ[K] {z : Bundle.TotalSpace P E // p z = b} :=
    (ePack b).toLinearMap.comp (ρ b)
  have hρβraw : ∀ b, Function.RightInverse (βraw b) (ρraw b) := by
    intro b u
    calc
      ρraw b (βraw b u) = ePack b ((ePack b).symm u) :=
        congrArg (ePack b) (hρβ b ((ePack b).symm u))
      _ = u := (ePack b).apply_symm_apply u
  have hβrawValue (z : Bundle.TotalSpace P E) :
      βraw (p z) ⟨z, rfl⟩ = β z.proj z.snd :=
    Bundle.TotalSpace.comp_fiberLinearEquiv_symm_apply_self (E := E) K P β z
  have hρrawValue (b : B) (a : A) :
      (ρraw b a).val = (Bundle.TotalSpace.mk b (ρ b a) : Bundle.TotalSpace P E) :=
    Bundle.TotalSpace.fiberLinearEquiv_comp_apply_val (E := E) K P b (ρ b) a
  have hβrawTotal : Continuous (fun z : Bundle.TotalSpace P E =>
      (p z, βraw (p z) ⟨z, rfl⟩)) :=
    hβTotal.congr (fun z =>
      (congrArg (fun a : A => (z.proj, a)) (hβrawValue z)).symm)
  have hρrawTotal : Continuous (fun y : B × A => (ρraw y.1 y.2).val) :=
    hρTotal.congr (fun y => (hρrawValue y.1 y.2).symm)
  let projectionFamily : C(B, {R : A →L[K] A // IsIdempotentElem R}) :=
    ContinuousMap.fiberwiseProjection p βraw ρraw hρβraw hβrawTotal hρrawTotal
  have hProjection (b : B) (a : A) : (projectionFamily b).val a = β b (ρ b a) := by
    calc
      (projectionFamily b).val a = βraw b (ρraw b a) :=
        ContinuousMap.fiberwiseProjection_apply p βraw ρraw
          hρβraw hβrawTotal hρrawTotal b a
      _ = β b (ρ b a) :=
        congrArg (β b) ((ePack b).symm_apply_apply (ρ b a))
  have hresidualContinuous (b : B) :
      Continuous (fun a : A => a - β b (ρ b a)) :=
    (ContinuousLinearMap.id K A - (projectionFamily b).val).continuous.congr
      (fun a => congrArg (fun v : A => a - v) (hProjection b a))
  let Qop (b : B) : A →L[K] A :=
    { toLinearMap := Q b
      cont := hresidualContinuous b }
  have hQop (b : B) : Qop b = ContinuousLinearMap.id K A - (projectionFamily b).val := by
    ext a
    exact congrArg (fun v : A => a - v) (hProjection b a).symm
  have hProjectionContinuous : Continuous (fun b => (projectionFamily b).val) :=
    continuous_subtype_val.comp projectionFamily.continuous
  have hcomplementContinuous :
      Continuous (fun b => ContinuousLinearMap.id K A - (projectionFamily b).val) :=
    continuous_const.sub hProjectionContinuous
  let Qc : C(B, A →L[K] A) :=
    ⟨Qop, hcomplementContinuous.congr (fun b => (hQop b).symm)⟩
  let R (b : B) : A →ₗ[K] A := (β b).comp (ρ b)
  have hR (b : B) : R b * R b = R b := by
    ext a
    exact congrArg (β b) (hρβ b (ρ b a))
  have hQ (b : B) : Q b * Q b = Q b := by
    change (1 - R b) * (1 - R b) = 1 - R b
    simp only [sub_mul, mul_sub, one_mul, mul_one, hR b, sub_self, sub_zero]
  have hid (b : B) : IsIdempotentElem (Qc b) := by
    change Qc b * Qc b = Qc b
    ext a
    change Q b (Q b a) = Q b a
    exact congrArg (fun L : A →ₗ[K] A => L a) (hQ b)
  letI : IsModuleTopology K A :=
    isModuleTopologyOfFiniteDimensional (𝕜 := K) (E := A)
  -- Normalize the inherited family and the already chosen total-space topology.
  change
    letI : TopologicalSpace
        (Bundle.TotalSpace P (fun b => LinearMap.range (Qc b).toLinearMap)) :=
      VectorBundle.rangeTotalSpaceTopology (F := P) (fun b => (Qc b).toLinearMap)
    Bundle.FiniteRankAtlas.{_, _, _, _, uB} K P
      (fun b => LinearMap.range (Qc b).toLinearMap)
  exact ContinuousLinearMap.finiteRankRangeAtlasOfFiniteDimensional
    (K := K) (A := A) P (fun b => Qc b) Qc.continuous hid

/-- The complementary ranges of a split family, with their finite-rank atlas, common rank,
named fixed-model bundle data, and canonical base- and ambient-vector-preserving change of tag.
The original fibres are algebraic modules; only their original total space is topologized. -/
noncomputable def complementaryRangeBundle
    (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
    (B : Type uB) [TopologicalSpace B]
    (A : Type uA) [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
    (P : Type uP)
    (F : Type uF) [AddCommMonoid F] [Module K F]
    (E : B → Type uE) [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
    (e : ∀ b, E b ≃ₗ[K] F)
    (β : ∀ b, E b →ₗ[K] A)
    (ρ : ∀ b, A →ₗ[K] E b)
    (hρβ : ∀ b (v : E b), ρ b (β b v) = v)
    [tTotal : TopologicalSpace (Bundle.TotalSpace P E)]
    (hβTotal : Continuous (fun z : Bundle.TotalSpace P E => (z.proj, β z.proj z.snd)))
    (hρTotal : Continuous (fun y : B × A =>
      (Bundle.TotalSpace.mk y.1 (ρ y.1 y.2) : Bundle.TotalSpace P E))) :
    let Q : B → A →ₗ[K] A := fun b => LinearMap.id - (β b).comp (ρ b)
    let S : B → Type uA := fun b => LinearMap.range (Q b)
    let n := Module.finrank K A - Module.finrank K F
    let tP : TopologicalSpace (Bundle.TotalSpace P S) := inferInstance
    letI : TopologicalSpace (Bundle.TotalSpace P S) := tP
    let W := Fin n → K
    let tW : TopologicalSpace (Bundle.TotalSpace W S) :=
      Bundle.TotalSpace.changeModelTopology P W S tP
    letI : TopologicalSpace (Bundle.TotalSpace W S) := tW
    Σ' (a : Bundle.FiniteRankAtlas.{_, _, _, _, uB} K P S),
    Σ' (h : ∀ b : B, Module.finrank K (S b) = n),
    Σ' (fb : @FiberBundle B W inferInstance inferInstance S tW inferInstance),
    Σ' (_hfb : fb = a.fiberBundleOfFinrank n h),
    letI : FiberBundle W S := fb
    letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
    letI : IsModuleTopology K W := IsModuleTopology.instPi
    Σ' (_vb : VectorBundle K W S),
    Σ' (hTag :
      @Homeomorph (Bundle.TotalSpace P S) (Bundle.TotalSpace W S) tP tW),
      hTag = @Homeomorph.symm _ _ tW tP
        (Bundle.TotalSpace.changeModelHomeomorph P W S tP) ∧
      (∀ z : Bundle.TotalSpace P S, (hTag z).proj = z.proj) ∧
      (∀ z : Bundle.TotalSpace P S, ((hTag z).snd : A) = (z.snd : A)) ∧
      (∀ z : Bundle.TotalSpace W S, (hTag.symm z).proj = z.proj) ∧
      (∀ z : Bundle.TotalSpace W S, ((hTag.symm z).snd : A) = (z.snd : A)) ∧
      (∀ z : Bundle.TotalSpace P S, hTag.symm (hTag z) = z) ∧
      (∀ z : Bundle.TotalSpace W S, hTag (hTag.symm z) = z) := by
  let Q : B → A →ₗ[K] A := fun b => LinearMap.id - (β b).comp (ρ b)
  let S : B → Type uA := fun b => LinearMap.range (Q b)
  let n := Module.finrank K A - Module.finrank K F
  let tP : TopologicalSpace (Bundle.TotalSpace P S) := inferInstance
  letI : TopologicalSpace (Bundle.TotalSpace P S) := tP
  let calA : Bundle.FiniteRankAtlas.{_, _, _, _, uB} K P S :=
    complementaryRangeFiniteRankAtlas K B A P E β ρ hρβ hβTotal hρTotal
  let hρβLM : ∀ b : B, (ρ b).comp (β b) = LinearMap.id := by
    intro b
    apply LinearMap.ext
    intro v
    exact hρβ b v
  let hn : ∀ b : B, Module.finrank K (S b) = n := by
    intro b
    exact LinearMap.finrank_range_id_sub_comp_of_rightInverse_family
      ρ β hρβLM e b
  let W := Fin n → K
  let tW : TopologicalSpace (Bundle.TotalSpace W S) :=
    Bundle.TotalSpace.changeModelTopology P W S tP
  letI : TopologicalSpace (Bundle.TotalSpace W S) := tW
  let fixedFB :
      @FiberBundle B W inferInstance inferInstance S tW inferInstance :=
    calA.fiberBundleOfFinrank n hn
  letI : FiberBundle W S := fixedFB
  letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
  letI : IsModuleTopology K W := IsModuleTopology.instPi
  let fixedVB : VectorBundle K W S :=
    calA.vectorBundleOfFinrank n hn
  let H0 :
      @Homeomorph (Bundle.TotalSpace W S) (Bundle.TotalSpace P S) tW tP :=
    Bundle.TotalSpace.changeModelHomeomorph P W S tP
  let H :
      @Homeomorph (Bundle.TotalSpace P S) (Bundle.TotalSpace W S) tP tW :=
    @Homeomorph.symm _ _ tW tP H0
  let tail :
      Σ' (a : Bundle.FiniteRankAtlas.{_, _, _, _, uB} K P S),
      Σ' (h : ∀ b : B, Module.finrank K (S b) = n),
      Σ' (fb : @FiberBundle B W inferInstance inferInstance S tW inferInstance),
      Σ' (_hfb : fb = a.fiberBundleOfFinrank n h),
      letI : FiberBundle W S := fb
      letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
      letI : IsModuleTopology K W := IsModuleTopology.instPi
      Σ' (_vb : VectorBundle K W S),
      Σ' (hTag :
        @Homeomorph (Bundle.TotalSpace P S) (Bundle.TotalSpace W S) tP tW),
        hTag = @Homeomorph.symm _ _ tW tP
          (Bundle.TotalSpace.changeModelHomeomorph P W S tP) ∧
        (∀ z : Bundle.TotalSpace P S, (hTag z).proj = z.proj) ∧
        (∀ z : Bundle.TotalSpace P S, ((hTag z).snd : A) = (z.snd : A)) ∧
        (∀ z : Bundle.TotalSpace W S, (hTag.symm z).proj = z.proj) ∧
        (∀ z : Bundle.TotalSpace W S, ((hTag.symm z).snd : A) = (z.snd : A)) ∧
        (∀ z : Bundle.TotalSpace P S, hTag.symm (hTag z) = z) ∧
        (∀ z : Bundle.TotalSpace W S, hTag (hTag.symm z) = z) := by
    refine ⟨calA, hn, fixedFB, rfl, fixedVB, H, ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      rfl
    · intro z
      rfl
    · intro z
      rfl
    · intro z
      rfl
    · intro z
      exact (@Homeomorph.toEquiv _ _ tP tW H).left_inv z
    · intro z
      exact (@Homeomorph.toEquiv _ _ tP tW H).right_inv z
  exact tail

section Characteristic

variable (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
  (B : Type uB) [TopologicalSpace B]
  (A : Type uA) [NormedAddCommGroup A] [NormedSpace K A] [FiniteDimensional K A]
  (P : Type uP)
  (F : Type uF) [AddCommMonoid F] [Module K F]
  (E : B → Type uE) [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
  (e : ∀ b, E b ≃ₗ[K] F)
  (β : ∀ b, E b →ₗ[K] A) (ρ : ∀ b, A →ₗ[K] E b)
  (hρβ : ∀ b (v : E b), ρ b (β b v) = v)
  [tTotal : TopologicalSpace (Bundle.TotalSpace P E)]
  (hβTotal : Continuous (fun z : Bundle.TotalSpace P E => (z.proj, β z.proj z.snd)))
  (hρTotal : Continuous (fun y : B × A =>
    (Bundle.TotalSpace.mk y.1 (ρ y.1 y.2) : Bundle.TotalSpace P E)))

local notation "Q" => (fun b : B => (LinearMap.id : A →ₗ[K] A) - LinearMap.comp (β b) (ρ b))
local notation "S" => (fun b : B => LinearMap.range (Q b))
local notation "n" => (Module.finrank K A - Module.finrank K F)
local notation "W" => (Fin n → K)
local notation "tP" => (VectorBundle.rangeTotalSpaceTopology (F := P) Q)
local notation "tW" => (Bundle.TotalSpace.changeModelTopology P W S tP)
local notation "r" =>
  (complementaryRangeBundle K B A P F E e β ρ hρβ hβTotal hρTotal)

include e hρβ hβTotal hρTotal

/-- The finite-rank atlas on the complementary ranges selected by `complementaryRangeBundle`
for the given family and common model. -/
noncomputable def complementaryRangeAtlas :
    Bundle.FiniteRankAtlas.{_, _, _, _, uB} K P S :=
  (r).1

/-- The named fixed-model fibre-bundle data selected by `complementaryRangeBundle`, on exactly
the topology transported from its original range total space. This is not a global instance. -/
@[instance_reducible] noncomputable def complementaryRangeFiberBundle :
    @FiberBundle B W inferInstance inferInstance S tW inferInstance :=
  (r).2.2.1

/-- The selected fibre-bundle data are those of the selected atlas and its common rank. -/
theorem complementaryRangeFiberBundle_eq :
    complementaryRangeFiberBundle K B A P F E e β ρ hρβ hβTotal hρTotal =
      (complementaryRangeAtlas K B A P F E e β ρ hρβ hβTotal hρTotal).fiberBundleOfFinrank n
        (LinearMap.finrank_range_id_sub_comp_of_rightInverse_family
          ρ β (fun b => LinearMap.ext (hρβ b)) e) :=
  (r).2.2.2.1

/-- The vector-bundle mixin for exactly `complementaryRangeFiberBundle` and its transported
total-space topology, using the scalar-self and finite-product module topologies. -/
theorem complementaryRangeVectorBundle :
    letI : TopologicalSpace (Bundle.TotalSpace W S) := tW
    letI : FiberBundle W S :=
      complementaryRangeFiberBundle K B A P F E e β ρ hρβ hβTotal hρTotal
    letI : IsModuleTopology K K := IsTopologicalSemiring.toIsModuleTopology K
    letI : IsModuleTopology K W := IsModuleTopology.instPi
    VectorBundle K W S :=
  (r).2.2.2.2.1

/-- The canonical change of tag from the original range total space to the fixed-model one.
Its domain has the original range topology and its codomain has exactly `changeModelTopology`. -/
noncomputable def complementaryRangeHomeomorph :
    @Homeomorph (Bundle.TotalSpace P S) (Bundle.TotalSpace W S) tP tW :=
  (r).2.2.2.2.2.1

-- The total-space model tags are phantom: fix both topologies before symmetry or application.
/-- The selected homeomorphism is the inverse of the canonical new-to-original change of tag. -/
theorem complementaryRangeHomeomorph_eq :
    complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal =
      @Homeomorph.symm _ _ tW tP (Bundle.TotalSpace.changeModelHomeomorph P W S tP) :=
  (r).2.2.2.2.2.2.1

/-- Changing the range model tag preserves a specified base point and fibre vector. -/
@[simp] theorem complementaryRangeHomeomorph_mk (b : B) (v : S b) :
    (@Homeomorph.toEquiv _ _ tP tW
      (complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal))
        (Bundle.TotalSpace.mk b v) =
      (Bundle.TotalSpace.mk b v : Bundle.TotalSpace W S) := by
  rw [complementaryRangeHomeomorph_eq K B A P F E e β ρ hρβ hβTotal hρTotal]
  rfl

/-- The inverse change of range model tag preserves a specified base point and fibre vector. -/
@[simp] theorem complementaryRangeHomeomorph_symm_mk (b : B) (v : S b) :
    (@Homeomorph.toEquiv _ _ tP tW
      (complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal)).symm
        (Bundle.TotalSpace.mk b v) =
      (Bundle.TotalSpace.mk b v : Bundle.TotalSpace P S) := by
  rw [complementaryRangeHomeomorph_eq K B A P F E e β ρ hρβ hβTotal hρTotal]
  rfl

/-- The forward change of range model tag preserves the base point. -/
@[simp] theorem complementaryRangeHomeomorph_proj (z : Bundle.TotalSpace P S) :
    ((complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal :
      @Homeomorph _ _ tP tW) z).proj = z.proj :=
  (r).2.2.2.2.2.2.2.1 z

/-- The forward change of range model tag preserves the ambient vector in `A`. -/
@[simp] theorem complementaryRangeHomeomorph_snd (z : Bundle.TotalSpace P S) :
    (((complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal :
      @Homeomorph _ _ tP tW) z).snd : A) =
      (z.snd : A) :=
  (r).2.2.2.2.2.2.2.2.1 z

/-- The inverse change of range model tag preserves the base point. -/
@[simp] theorem complementaryRangeHomeomorph_symm_proj (z : Bundle.TotalSpace W S) :
    (@DFunLike.coe (@Homeomorph _ _ tW tP) _ _ _
      (@Homeomorph.symm _ _ tP tW
        (complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal :
          @Homeomorph _ _ tP tW)) z).proj =
      z.proj :=
  (r).2.2.2.2.2.2.2.2.2.1 z

/-- The inverse change of range model tag preserves the ambient vector in `A`. -/
@[simp] theorem complementaryRangeHomeomorph_symm_snd (z : Bundle.TotalSpace W S) :
    ((@DFunLike.coe (@Homeomorph _ _ tW tP) _ _ _
      (@Homeomorph.symm _ _ tP tW
        (complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal :
          @Homeomorph _ _ tP tW)) z).snd : A) =
      (z.snd : A) :=
  (r).2.2.2.2.2.2.2.2.2.2.1 z

end Characteristic

end VectorBundle
