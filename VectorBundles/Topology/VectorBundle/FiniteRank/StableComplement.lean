/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import VectorBundles.Topology.VectorBundle.FiniteRank.Embedding
public import VectorBundles.Topology.VectorBundle.FiniteRank.LinearEquiv
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas.SplitFamily
public import VectorBundles.Topology.FiberBundle.SumRangeTrivialization

/-!
# Stable complements of finite-rank atlases

The finite trivial embedding of a finite-rank atlas over a compact normal base has a
specified retraction. The range of the complementary projector is a finite-rank family,
with its range-graph topology. The direct sum with the original family has a full-base
trivialization, with model the same finite coordinate space as the embedding.

The topology on the original total space is unchanged. The sum total space carries the
fiberwise product topology of that total space and the range-graph total space. Ranks of
both summands may vary with the base point.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, §1, the stable-complement argument.
* The finite trivial embedding and complementary range constructions in this library;
  the sum chart uses `Bundle.TotalSpace.sumRangeTrivialization`.
-/

@[expose] public section

universe uK uB uE uP uI

namespace Bundle.FiniteRankAtlas

variable {K : Type uK} [RCLike K]
variable {B : Type uB} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [tTotal : TopologicalSpace (TotalSpace P E)]
variable (a : FiniteRankAtlas.{_, _, _, _, uI} K P E)

noncomputable section

local notation "A" => (Fin a.embeddingDimension → K)
local notation "β" => a.finiteTrivialEmbeddingLinearMap
local notation "ρ" => a.finiteTrivialRetractionLinearMap

/-- The atlas-selected finite trivial retraction is a left inverse to the embedding. -/
private theorem retraction_embedding (b : B) (v : E b) : ρ b (β b v) = v :=
  congrArg (fun f : E b →ₗ[K] E b => f v)
    (a.finiteTrivialRetractionLinearMap_comp_finiteTrivialEmbeddingLinearMap b)

/-- The selected embedding is continuous for the original atlas total-space topology. -/
private theorem embedding_total_continuous :
    Continuous (fun z : TotalSpace P E => (z.proj, β z.proj z.snd)) := by
  apply a.continuous_finiteTrivialEmbedding.congr
  rintro ⟨b, v⟩
  exact a.finiteTrivialEmbedding_mk b v

/-- The selected retraction is continuous into the original atlas total space. -/
private theorem retraction_total_continuous :
    Continuous (fun y : B × A => (TotalSpace.mk y.1 (ρ y.1 y.2) : TotalSpace P E)) :=
  a.continuous_finiteTrivialRetraction.congr a.finiteTrivialRetraction_apply

/-- The projector complementary to the specified finite trivial embedding and retraction. -/
def stableComplementProjector (b : B) : A →ₗ[K] A :=
  LinearMap.id - (β b).comp (ρ b)

/-- The complementary projector subtracts the embedded retraction. -/
theorem stableComplementProjector_apply (b : B) (x : A) :
    a.stableComplementProjector b x = x - β b (ρ b x) := rfl

/-- The stable complement, as a family of submodules of the finite coordinate space. -/
def stableComplement (b : B) : Submodule K A :=
  (a.stableComplementProjector b).range

/-- Membership in the stable complement means being the image of the complementary projector. -/
theorem mem_stableComplement_iff (b : B) (x : A) :
    x ∈ a.stableComplement b ↔ ∃ y, a.stableComplementProjector b y = x :=
  Iff.rfl

/-- The complementary component of an ambient vector, regarded as a complement vector. -/
def stableComplementComponent (b : B) (x : A) : a.stableComplement b :=
  ⟨a.stableComplementProjector b x, ⟨x, rfl⟩⟩

/-- The ambient value of the complementary component. -/
@[simp] theorem coe_stableComplementComponent (b : B) (x : A) :
    (a.stableComplementComponent b x : A) = a.stableComplementProjector b x := rfl

/-- The complementary component is additive. -/
@[simp] theorem stableComplementComponent_add (b : B) (x y : A) :
    a.stableComplementComponent b (x + y) =
      a.stableComplementComponent b x + a.stableComplementComponent b y :=
  Subtype.ext ((a.stableComplementProjector b).map_add x y)

/-- The complementary component commutes with scalar multiplication. -/
@[simp] theorem stableComplementComponent_smul (b : B) (r : K) (x : A) :
    a.stableComplementComponent b (r • x) = r • a.stableComplementComponent b x :=
  Subtype.ext ((a.stableComplementProjector b).map_smul r x)

/-- The stable complement is the kernel of the specified retraction. -/
theorem stableComplement_eq_ker_retraction (b : B) :
    a.stableComplement b = (ρ b).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change ρ b (y - β b (ρ b y)) = 0
    rw [map_sub, retraction_embedding, sub_self]
  · intro hx
    have hx' : ρ b x = 0 := hx
    refine ⟨x, ?_⟩
    simp only [stableComplementProjector_apply, hx', map_zero, sub_zero]

/-- The stable complement is also the kernel of the projection onto the embedded family. -/
theorem stableComplement_eq_ker_projection (b : B) :
    a.stableComplement b = ((β b).comp (ρ b)).ker := by
  rw [stableComplement_eq_ker_retraction]
  ext x
  constructor
  · intro hx
    change β b (ρ b x) = 0
    rw [show ρ b x = 0 from hx, map_zero]
  · intro hx
    have h : β b (ρ b x) = 0 := hx
    have h' := congrArg (ρ b) h
    change ρ b x = 0
    simpa only [retraction_embedding, map_zero] using h'

/-- The retraction vanishes on a complement vector. -/
@[simp] theorem retraction_coe_stableComplement (b : B) (c : a.stableComplement b) :
    ρ b (c : A) = 0 := by
  have hc : (c : A) ∈ (ρ b).ker := by
    rw [← stableComplement_eq_ker_retraction]
    exact c.property
  exact hc

/-- The complementary projector fixes each complement vector. -/
@[simp] theorem stableComplementProjector_coe (b : B) (c : a.stableComplement b) :
    a.stableComplementProjector b (c : A) = (c : A) := by
  rw [stableComplementProjector_apply, retraction_coe_stableComplement, map_zero, sub_zero]

/-- The complementary projector is idempotent on the ambient coordinate space. -/
@[simp] theorem stableComplementProjector_apply_self (b : B) (x : A) :
    a.stableComplementProjector b (a.stableComplementProjector b x) =
      a.stableComplementProjector b x :=
  a.stableComplementProjector_coe b (a.stableComplementComponent b x)

/-- The complement rank is the ambient dimension minus the original fibre rank. -/
theorem finrank_stableComplement (b : B) :
    Module.finrank K (a.stableComplement b) =
      a.embeddingDimension - Module.finrank K (E b) := by
  change Module.finrank K
      ((LinearMap.id - (β b).comp (ρ b) : A →ₗ[K] A).range) =
    a.embeddingDimension - Module.finrank K (E b)
  have h : Module.finrank K
        ((LinearMap.id - (β b).comp (ρ b) : A →ₗ[K] A).range) =
      Module.finrank K A - Module.finrank K (E b) :=
    LinearMap.finrank_range_id_sub_comp_of_rightInverse_family
      (fun _ : Unit => ρ b) (fun _ : Unit => β b)
      (fun _ : Unit =>
        a.finiteTrivialRetractionLinearMap_comp_finiteTrivialEmbeddingLinearMap b)
      (fun _ : Unit => LinearEquiv.refl K (E b)) ()
  simpa only [Module.finrank_fin_fun] using h

/-- The original fibre rank and its stable-complement rank add to the specified ambient
dimension, even when the ranks vary over the base. -/
theorem finrank_stableComplement_add (b : B) :
    Module.finrank K (a.stableComplement b) + Module.finrank K (E b) =
      a.embeddingDimension := by
  have : Module.Finite K (E b) := a.moduleFinite_fiber b
  have hβinj : Function.Injective (β b) := by
    intro x y h
    calc
      x = ρ b (β b x) := (retraction_embedding a b x).symm
      _ = ρ b (β b y) := congrArg (ρ b) h
      _ = y := retraction_embedding a b y
  have hdim : Module.finrank K (E b) ≤ a.embeddingDimension := by
    simpa only [Module.finrank_fin_fun] using
      LinearMap.finrank_le_finrank_of_injective hβinj
  rw [finrank_stableComplement]
  exact Nat.sub_add_cancel hdim

/-- The canonical range-graph topology on the atlas stable complement. -/
abbrev complementTotalTopology :
    TopologicalSpace (TotalSpace P (fun b => a.stableComplement b)) :=
  VectorBundle.rangeTotalSpaceTopology (F := P) a.stableComplementProjector

attribute [local instance] complementTotalTopology

/-- The product topology of the original atlas total space and its stable complement. -/
abbrev complementSumTopology :
    TopologicalSpace (TotalSpace (P × P) (fun b => E b × a.stableComplement b)) :=
  @FiberBundle.Prod.topologicalSpace B P E P (fun b => a.stableComplement b)
    tTotal (complementTotalTopology a)

attribute [local instance] complementSumTopology

/-- The finite-rank atlas on the stable complement with its canonical range-graph topology. -/
def stableComplementAtlas :
    FiniteRankAtlas.{_, _, _, _, uB} K P (fun b => a.stableComplement b) :=
  VectorBundle.complementaryRangeFiniteRankAtlas K B A P E β ρ
    (by exact retraction_embedding a)
    (by exact embedding_total_continuous a)
    (by exact retraction_total_continuous a)

/-- The full-base sum trivialization associated to the specified finite trivial embedding.
This is the stable-complement construction of Hatcher, *Vector Bundles and K-Theory*, §1. -/
def stableComplementTrivialization :
    Trivialization A
      (TotalSpace.proj : TotalSpace (P × P) (fun b => E b × a.stableComplement b) → B) :=
  TotalSpace.sumRangeTrivialization (F := P) (G := P) (tE := tTotal) β ρ
    (by exact retraction_embedding a)
    (by exact embedding_total_continuous a)
    (by exact retraction_total_continuous a)

/-- Every base point belongs to the stable-complement chart. -/
@[simp] theorem stableComplementTrivialization_baseSet :
    a.stableComplementTrivialization.baseSet = Set.univ :=
  TotalSpace.sumRangeTrivialization_baseSet (F := P) (G := P) (tE := tTotal) β ρ
    (retraction_embedding a) (embedding_total_continuous a) (retraction_total_continuous a)

/-- The stable-complement chart is defined on the entire original sum total space. -/
@[simp] theorem stableComplementTrivialization_source :
    a.stableComplementTrivialization.source = Set.univ := by
  rw [Trivialization.source_eq, stableComplementTrivialization_baseSet]
  rfl

/-- The stable-complement chart has the whole trivial bundle as target. -/
@[simp] theorem stableComplementTrivialization_target :
    a.stableComplementTrivialization.target = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact (a.stableComplementTrivialization.mem_target (x := y)).mpr (by simp)

/-- The sum chart adds the embedded original vector and the complement vector. -/
@[simp] theorem stableComplementTrivialization_apply
    (z : TotalSpace (P × P) (fun b => E b × a.stableComplement b)) :
    a.stableComplementTrivialization z = (z.proj, β z.proj z.snd.1 + (z.snd.2 : A)) :=
  TotalSpace.sumRangeTrivialization_apply (F := P) (G := P) (tE := tTotal) β ρ
    (retraction_embedding a) (embedding_total_continuous a) (retraction_total_continuous a) z

/-- The forward chart preserves the original base point. -/
theorem stableComplementTrivialization_fst
    (z : TotalSpace (P × P) (fun b => E b × a.stableComplement b)) :
    (a.stableComplementTrivialization z).1 = z.proj := by
  rw [stableComplementTrivialization_apply]

/-- The underlying partial-homeomorphism inverse recovers a specified original fibre vector
and its complementary component. No zero extension of a fibre inverse is used. -/
@[simp] theorem stableComplementTrivialization_symm_apply (b : B) (x : A) :
    a.stableComplementTrivialization.toOpenPartialHomeomorph.symm (b, x) =
      TotalSpace.mk b (ρ b x, a.stableComplementComponent b x) := by
  have h : a.stableComplementTrivialization
      (TotalSpace.mk b (ρ b x, a.stableComplementComponent b x)) = (b, x) := by
    simp only [stableComplementTrivialization_apply, coe_stableComplementComponent,
      stableComplementProjector_apply]
    congr 1
    simp [sub_eq_add_neg, add_left_comm]
  rw [← h]
  exact a.stableComplementTrivialization.toOpenPartialHomeomorph.left_inv (by simp)

/-- The inverse recovers the entire original total-space point, as well as the ambient
complementary vector. -/
theorem stableComplementTrivialization_symm_apply_val (y : B × A) :
    let z := a.stableComplementTrivialization.toOpenPartialHomeomorph.symm y
    ((TotalSpace.mk z.proj z.snd.1 : TotalSpace P E), (z.snd.2 : A)) =
      ((TotalSpace.mk y.1 (ρ y.1 y.2) : TotalSpace P E),
        a.stableComplementProjector y.1 y.2) := by
  rcases y with ⟨b, x⟩
  exact congrArg
    (fun z : TotalSpace (P × P) (fun b => E b × a.stableComplement b) =>
      ((TotalSpace.mk z.proj z.snd.1 : TotalSpace P E), (z.snd.2 : A)))
    (a.stableComplementTrivialization_symm_apply b x)

/-- The inverse chart preserves the base point. -/
@[simp] theorem stableComplementTrivialization_symm_proj (y : B × A) :
    (a.stableComplementTrivialization.toOpenPartialHomeomorph.symm y).proj = y.1 := by
  rcases y with ⟨b, x⟩
  rw [stableComplementTrivialization_symm_apply]

/-- Forward then inverse returns every original sum point. -/
theorem stableComplementTrivialization_symm_apply_apply
    (z : TotalSpace (P × P) (fun b => E b × a.stableComplement b)) :
    a.stableComplementTrivialization.toOpenPartialHomeomorph.symm
      (a.stableComplementTrivialization z) = z :=
  a.stableComplementTrivialization.toOpenPartialHomeomorph.left_inv (by simp)

/-- Inverse then forward returns every point of the trivial bundle. -/
theorem stableComplementTrivialization_apply_symm_apply (y : B × A) :
    a.stableComplementTrivialization
      (a.stableComplementTrivialization.toOpenPartialHomeomorph.symm y) = y :=
  a.stableComplementTrivialization.toOpenPartialHomeomorph.right_inv (by simp)

/-- On an original fibre, the sum-chart function is the coproduct of the chosen embedding
and complement inclusion. -/
theorem stableComplementTrivialization_fiber_eq_coprod (b : B) :
    (fun w : E b × a.stableComplement b =>
      (a.stableComplementTrivialization (TotalSpace.mk b w)).2) =
      (LinearMap.coprod (β b) (a.stableComplement b).subtype :
        E b × a.stableComplement b → A) := by
  funext w
  rw [stableComplementTrivialization_apply]
  rfl

/-- The sum chart is fibrewise linear for the original module structures. -/
theorem stableComplementTrivialization_isFiberwiseLinear :
    a.stableComplementTrivialization.IsFiberwiseLinear (K := K) :=
  TotalSpace.sumRangeTrivialization_isFiberwiseLinear (F := P) (G := P) (tE := tTotal) β ρ
    (retraction_embedding a) (embedding_total_continuous a) (retraction_total_continuous a)

/-- The fibre linear map of the sum chart is the coproduct of the specified embedding and
submodule inclusion. -/
theorem stableComplementTrivialization_linearMap (b : B)
    (hb : b ∈ a.stableComplementTrivialization.baseSet) :
    a.stableComplementTrivialization_isFiberwiseLinear.linearMap hb =
      LinearMap.coprod (β b) (a.stableComplement b).subtype :=
  TotalSpace.sumRangeTrivialization_linearMap (F := P) (G := P) (tE := tTotal) β ρ
    (retraction_embedding a) (embedding_total_continuous a) (retraction_total_continuous a) b hb

end

end Bundle.FiniteRankAtlas
