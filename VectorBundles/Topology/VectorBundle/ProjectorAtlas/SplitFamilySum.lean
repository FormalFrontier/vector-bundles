/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas.SplitFamily
public import VectorBundles.Topology.FiberBundle.SumRangeTrivialization
public import VectorBundles.Topology.FiberBundle.Prod
public import VectorBundles.Topology.FiberBundle.Trivialization.CompHomeomorph

/-!
# Sum charts with a fixed complementary model

Over a complete nontrivially normed field, an algebraic split family in a finite-dimensional
normed space, with continuous original-total embedding and retraction, has a complementary
range bundle with a fixed model of the dimension difference. Its sum with the original
family admits a full-base chart into the ambient space. Only the given original total
space is topologized; no topology on the original fibres or their common algebraic model
is required.

The chart changes the right total-space model tag by the canonical homeomorphism from
`complementaryRangeBundle`. The entire first original total-space point is fixed. Both
ambient-value laws of that homeomorphism identify the forward and inverse coordinates.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, §1, the stable-complement argument.
* The complementary range bundle, sum–range chart, and right-factor product
  homeomorphism formalizations in this library.
-/

@[expose] public section

universe uK uB uA uP uF uE

namespace VectorBundle

section Sum

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
local notation "W" => (Fin (Module.finrank K A - Module.finrank K F) → K)
local notation "tP" => (VectorBundle.rangeTotalSpaceTopology (F := P) Q)
local notation "tW" => (Bundle.TotalSpace.changeModelTopology P W S tP)
local notation "hTag" =>
  (complementaryRangeHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal)
local notation "q" =>
  (fun (b : B) (x : A) => (Subtype.mk (Q b x) (Exists.intro x rfl) : S b))

/-- Product topology of the given original total space and the complementary range graph,
with both total-space model tags equal to `P`. -/
abbrev rangeSumTopology :
    TopologicalSpace (Bundle.TotalSpace (P × P) (fun b => E b × S b)) :=
  @FiberBundle.Prod.topologicalSpace B P E P S tTotal tP

/-- Product topology after changing only the complementary model tag to the fixed model. -/
abbrev modelSumTopology :
    TopologicalSpace (Bundle.TotalSpace (P × W) (fun b => E b × S b)) :=
  @FiberBundle.Prod.topologicalSpace B P E W S tTotal tW

attribute [local instance] rangeSumTopology modelSumTopology

/-- Change the complementary model tag while preserving the complete original first point. -/
noncomputable def rangeSumHomeomorph :
    @Homeomorph
      (Bundle.TotalSpace (P × W) (fun b => E b × S b))
      (Bundle.TotalSpace (P × P) (fun b => E b × S b))
      (modelSumTopology K B A P F E β ρ) (rangeSumTopology K B A P E β ρ) :=
  @FiberBundle.Prod.homeomorphCongrRight B P E W S P S tTotal tW tP
    (@Homeomorph.symm _ _ tP tW hTag)
    (complementaryRangeHomeomorph_symm_proj K B A P F E e β ρ hρβ hβTotal hρTotal)

local notation "H" => (rangeSumHomeomorph K B A P F E e β ρ hρβ hβTotal hρTotal)
local notation "T" => (Bundle.TotalSpace.sumRangeTrivialization
  (F := P) (G := P) (tE := tTotal) β ρ hρβ hβTotal hρTotal)

private theorem rangeSumHomeomorph_fst
    (z : Bundle.TotalSpace (P × W) (fun b => E b × S b)) :
    Bundle.TotalSpace.mk (H z).proj (H z).snd.1 =
      (Bundle.TotalSpace.mk z.proj z.snd.1 : Bundle.TotalSpace P E) :=
  @FiberBundle.Prod.totalSpaceFst_homeomorphCongrRight B P E W S P S tTotal tW tP
    (@Homeomorph.symm _ _ tP tW hTag)
    (complementaryRangeHomeomorph_symm_proj K B A P F E e β ρ hρβ hβTotal hρTotal) z

private theorem rangeSumHomeomorph_snd
    (z : Bundle.TotalSpace (P × W) (fun b => E b × S b)) :
    (Bundle.TotalSpace.mk (H z).proj (H z).snd.2 : Bundle.TotalSpace P S) =
      (@Homeomorph.symm _ _ tP tW hTag)
        (Bundle.TotalSpace.mk z.proj z.snd.2 : Bundle.TotalSpace W S) :=
  @FiberBundle.Prod.totalSpaceSnd_homeomorphCongrRight B P E W S P S tTotal tW tP
    (@Homeomorph.symm _ _ tP tW hTag)
    (complementaryRangeHomeomorph_symm_proj K B A P F E e β ρ hρβ hβTotal hρTotal) z

private theorem rangeSumHomeomorph_symm_fst
    (z : Bundle.TotalSpace (P × P) (fun b => E b × S b)) :
    Bundle.TotalSpace.mk ((H).symm z).proj ((H).symm z).snd.1 =
      (Bundle.TotalSpace.mk z.proj z.snd.1 : Bundle.TotalSpace P E) :=
  @FiberBundle.Prod.totalSpaceFst_homeomorphCongrRight_symm B P E W S P S tTotal tW tP
    (@Homeomorph.symm _ _ tP tW hTag)
    (complementaryRangeHomeomorph_symm_proj K B A P F E e β ρ hρβ hβTotal hρTotal) z

private theorem rangeSumHomeomorph_symm_snd
    (z : Bundle.TotalSpace (P × P) (fun b => E b × S b)) :
    (Bundle.TotalSpace.mk ((H).symm z).proj ((H).symm z).snd.2 : Bundle.TotalSpace W S) =
      hTag (Bundle.TotalSpace.mk z.proj z.snd.2 : Bundle.TotalSpace P S) :=
  @FiberBundle.Prod.totalSpaceSnd_homeomorphCongrRight_symm B P E W S P S tTotal tW tP
    (@Homeomorph.symm _ _ tP tW hTag)
    (complementaryRangeHomeomorph_symm_proj K B A P F E e β ρ hρβ hβTotal hρTotal) z

private theorem rangeSumHomeomorph_proj :
    (Bundle.TotalSpace.proj : Bundle.TotalSpace (P × P) (fun b => E b × S b) → B) ∘ H =
      (Bundle.TotalSpace.proj : Bundle.TotalSpace (P × W) (fun b => E b × S b) → B) := by
  funext z
  exact congrArg (fun u : Bundle.TotalSpace P E => u.proj)
    (rangeSumHomeomorph_fst K B A P F E e β ρ hρβ hβTotal hρTotal z)

private theorem castTrivialization_toOpenPartialHomeomorph
    {Z : Type*} [TopologicalSpace Z] {f g : Z → B}
    (h : f = g) (t : Bundle.Trivialization A f) :
    (Eq.mp (congrArg (Bundle.Trivialization A) h) t).toOpenPartialHomeomorph =
      (t).toOpenPartialHomeomorph := by
  cases h
  rfl

private theorem castTrivialization_baseSet
    {Z : Type*} [TopologicalSpace Z] {f g : Z → B}
    (h : f = g) (t : Bundle.Trivialization A f) :
    (Eq.mp (congrArg (Bundle.Trivialization A) h) t).baseSet = (t).baseSet := by
  cases h
  rfl

/-- The full sum chart with the fixed complementary model. Its domain has the canonical
product topology of the given original total space and the transported range-graph topology.
The construction follows the stable-complement argument of Hatcher, *Vector Bundles and
K-Theory*, §1, without imposing a topology on the original algebraic fibres. -/
noncomputable def complementaryRangeSumTrivialization :
    Bundle.Trivialization A
      (Bundle.TotalSpace.proj : Bundle.TotalSpace (P × W) (fun b => E b × S b) → B) :=
  Eq.mp (congrArg (Bundle.Trivialization A)
    (by exact rangeSumHomeomorph_proj K B A P F E e β ρ hρβ hβTotal hρTotal))
    ((T).compHomeomorph H)

local notation "t" =>
  (complementaryRangeSumTrivialization K B A P F E e β ρ hρβ hβTotal hρTotal)

private theorem sumTrivialization_toOpenPartialHomeomorph :
    (t).toOpenPartialHomeomorph = ((T).compHomeomorph H).toOpenPartialHomeomorph := by
  exact castTrivialization_toOpenPartialHomeomorph B A
    (rangeSumHomeomorph_proj K B A P F E e β ρ hρβ hβTotal hρTotal) ((T).compHomeomorph H)

/-- Every base point belongs to the fixed-model sum chart. -/
@[simp] theorem complementaryRangeSumTrivialization_baseSet : (t).baseSet = Set.univ := by
  rw [complementaryRangeSumTrivialization,
    castTrivialization_baseSet B A
      (rangeSumHomeomorph_proj K B A P F E e β ρ hρβ hβTotal hρTotal)
      ((T).compHomeomorph H),
    Bundle.Trivialization.compHomeomorph_baseSet]
  exact Bundle.TotalSpace.sumRangeTrivialization_baseSet
    (F := P) (G := P) (tE := tTotal) β ρ hρβ hβTotal hρTotal

/-- The fixed-model sum chart is defined on the whole original product total space. -/
@[simp] theorem complementaryRangeSumTrivialization_source : (t).source = Set.univ := by
  rw [Bundle.Trivialization.source_eq, complementaryRangeSumTrivialization_baseSet]
  rfl

/-- The target of the fixed-model sum chart is the whole ambient trivial bundle. -/
@[simp] theorem complementaryRangeSumTrivialization_target : (t).target = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact ((t).mem_target (x := y)).mpr (by simp)

/-- The fixed-model chart adds the original embedded vector and the ambient range vector. -/
@[simp] theorem complementaryRangeSumTrivialization_apply
    (z : Bundle.TotalSpace (P × W) (fun b => E b × S b)) :
    t z = (z.proj, β z.proj z.snd.1 + (z.snd.2 : A)) := by
  change (t).toOpenPartialHomeomorph z = _
  rw [sumTrivialization_toOpenPartialHomeomorph]
  change ((T).compHomeomorph H) z = _
  rw [Bundle.Trivialization.compHomeomorph_apply, Bundle.TotalSpace.sumRangeTrivialization_apply]
  have hf := rangeSumHomeomorph_fst K B A P F E e β ρ hρβ hβTotal hρTotal z
  have hs := rangeSumHomeomorph_snd K B A P F E e β ρ hρβ hβTotal hρTotal z
  have hβ := congrArg (fun u : Bundle.TotalSpace P E => β u.proj u.snd) hf
  have hval : ((H z).snd.2 : A) = (z.snd.2 : A) := by
    calc
      ((H z).snd.2 : A) =
          (((@Homeomorph.symm _ _ tP tW hTag)
            (Bundle.TotalSpace.mk z.proj z.snd.2 : Bundle.TotalSpace W S)).snd : A) :=
        congrArg (fun u : Bundle.TotalSpace P S => (u.snd : A)) hs
      _ = (z.snd.2 : A) :=
        complementaryRangeHomeomorph_symm_snd K B A P F E e β ρ hρβ hβTotal hρTotal _
  exact Prod.ext (congrArg (fun u : Bundle.TotalSpace P E => u.proj) hf)
    (congrArg₂ (fun x y : A => x + y) hβ hval)

/-- The forward fixed-model chart preserves the original base point. -/
theorem complementaryRangeSumTrivialization_fst
    (z : Bundle.TotalSpace (P × W) (fun b => E b × S b)) :
    (t z).1 = z.proj := by
  rw [complementaryRangeSumTrivialization_apply]

private theorem sumTrivialization_symm (y : B × A) :
    (t).toOpenPartialHomeomorph.symm y = (H).symm ((T).toOpenPartialHomeomorph.symm y) := by
  rw [sumTrivialization_toOpenPartialHomeomorph,
    Bundle.Trivialization.toOpenPartialHomeomorph_compHomeomorph_symm_apply]

/-- The full underlying inverse preserves the complete original total-space retraction
point and returns the complementary ambient vector. -/
theorem complementaryRangeSumTrivialization_symm_apply_val (y : B × A) :
    let z := (t).toOpenPartialHomeomorph.symm y
    ((Bundle.TotalSpace.mk z.proj z.snd.1 : Bundle.TotalSpace P E), (z.snd.2 : A)) =
      ((Bundle.TotalSpace.mk y.1 (ρ y.1 y.2) : Bundle.TotalSpace P E), Q y.1 y.2) := by
  rw [sumTrivialization_symm]
  let c := (T).toOpenPartialHomeomorph.symm y
  have hf := rangeSumHomeomorph_symm_fst K B A P F E e β ρ hρβ hβTotal hρTotal c
  have hs := rangeSumHomeomorph_symm_snd K B A P F E e β ρ hρβ hβTotal hρTotal c
  have hc := Bundle.TotalSpace.toOpenPartialHomeomorph_sumRangeTrivialization_symm_apply_val
    (F := P) (G := P) (tE := tTotal) β ρ hρβ hβTotal hρTotal y
  apply Prod.ext
  · exact hf.trans (congrArg Prod.fst hc)
  · calc
      (((H).symm c).snd.2 : A) =
          ((hTag (Bundle.TotalSpace.mk c.proj c.snd.2 : Bundle.TotalSpace P S)).snd : A) :=
        congrArg (fun u : Bundle.TotalSpace W S => (u.snd : A)) hs
      _ = (c.snd.2 : A) :=
        complementaryRangeHomeomorph_snd K B A P F E e β ρ hρβ hβTotal hρTotal _
      _ = Q y.1 y.2 := congrArg Prod.snd hc

/-- The underlying inverse at a specified base point is the retraction paired with the
range-valued complementary projector. -/
@[simp] theorem complementaryRangeSumTrivialization_symm_apply (b : B) (x : A) :
    (t).toOpenPartialHomeomorph.symm (b, x) = Bundle.TotalSpace.mk b (ρ b x, q b x) := by
  have h : t (Bundle.TotalSpace.mk b (ρ b x, q b x)) = (b, x) := by
    rw [complementaryRangeSumTrivialization_apply]
    change (b, β b (ρ b x) + (x - β b (ρ b x))) = (b, x)
    congr 1
    simp [sub_eq_add_neg, add_left_comm]
  rw [← h]
  exact (t).toOpenPartialHomeomorph.left_inv (by simp)

/-- The inverse fixed-model chart preserves the base point. -/
@[simp] theorem complementaryRangeSumTrivialization_symm_proj (y : B × A) :
    ((t).toOpenPartialHomeomorph.symm y).proj = y.1 := by
  rcases y with ⟨b, x⟩
  rw [complementaryRangeSumTrivialization_symm_apply]

/-- Every original product total-space point survives the forward–inverse round trip. -/
theorem complementaryRangeSumTrivialization_symm_apply_apply
    (z : Bundle.TotalSpace (P × W) (fun b => E b × S b)) :
    (t).toOpenPartialHomeomorph.symm (t z) = z :=
  (t).toOpenPartialHomeomorph.left_inv (by simp)

/-- Every ambient trivial-bundle point survives the inverse–forward round trip. -/
theorem complementaryRangeSumTrivialization_apply_symm_apply (y : B × A) :
    t ((t).toOpenPartialHomeomorph.symm y) = y :=
  (t).toOpenPartialHomeomorph.right_inv (by simp)

/-- The inverse fibre coordinates preserve addition for the original module operations. -/
theorem complementaryRangeSumTrivialization_symm_apply_add (b : B) (x y : A) :
    (t).toOpenPartialHomeomorph.symm (b, x + y) =
      Bundle.TotalSpace.mk b ((ρ b x, q b x) + (ρ b y, q b y)) := by
  rw [complementaryRangeSumTrivialization_symm_apply]
  apply congrArg (Bundle.TotalSpace.mk b)
  apply Prod.ext
  · exact (ρ b).map_add x y
  · exact Subtype.ext ((Q b).map_add x y)

/-- The inverse fibre coordinates preserve scalar multiplication for the original operations. -/
theorem complementaryRangeSumTrivialization_symm_apply_smul (b : B) (r : K) (x : A) :
    (t).toOpenPartialHomeomorph.symm (b, r • x) =
      Bundle.TotalSpace.mk b (r • (ρ b x, q b x)) := by
  rw [complementaryRangeSumTrivialization_symm_apply]
  apply congrArg (Bundle.TotalSpace.mk b)
  apply Prod.ext
  · exact (ρ b).map_smul r x
  · exact Subtype.ext ((Q b).map_smul r x)

/-- On each original fibre, the chart function is the coproduct of the embedding and
range inclusion. -/
theorem complementaryRangeSumTrivialization_fiber_eq_coprod (b : B) :
    (fun w : E b × S b => (t (Bundle.TotalSpace.mk b w)).2) =
      (LinearMap.coprod (β b) (Q b).range.subtype : E b × S b → A) := by
  funext w
  rw [complementaryRangeSumTrivialization_apply]
  rfl

/-- The fixed-model sum chart is fibrewise linear for the given algebraic actions. -/
theorem complementaryRangeSumTrivialization_isFiberwiseLinear :
    (t).IsFiberwiseLinear (K := K) := by
  have hcoord (b : B) (w : E b × S b) :
      (t (Bundle.TotalSpace.mk b w)).2 = LinearMap.coprod (β b) (Q b).range.subtype w :=
    congrFun (complementaryRangeSumTrivialization_fiber_eq_coprod
      K B A P F E e β ρ hρβ hβTotal hρTotal b) w
  constructor
  · intro b _ v w
    rw [hcoord, hcoord, hcoord]
    exact (LinearMap.coprod (β b) (Q b).range.subtype).map_add v w
  · intro b _ r v
    rw [hcoord, hcoord]
    exact (LinearMap.coprod (β b) (Q b).range.subtype).map_smul r v

/-- The fibre linear map of the fixed-model sum chart is the coproduct of the original
embedding and the complementary submodule inclusion. -/
theorem complementaryRangeSumTrivialization_linearMap (b : B) (hb : b ∈ (t).baseSet) :
    (complementaryRangeSumTrivialization_isFiberwiseLinear
      K B A P F E e β ρ hρβ hβTotal hρTotal).linearMap hb =
      LinearMap.coprod (β b) (Q b).range.subtype := by
  apply LinearMap.ext
  intro w
  rw [Bundle.Trivialization.IsFiberwiseLinear.linearMap_apply,
    complementaryRangeSumTrivialization_apply]
  rfl

end Sum

end VectorBundle
