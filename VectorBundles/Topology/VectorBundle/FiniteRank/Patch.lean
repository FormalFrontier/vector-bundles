/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Fixed-model bundles on chart domains

A chart of a finite-rank atlas gives a fixed-model trivialization over its base set.
The fibres are the original fibres, and the patch total-space topology is induced
from the original chart source. The resulting trivialization is linear for the
original module structures and supplies named `FiberBundle` data on this patch.

These constructions require only the hypotheses of `FiniteRankAtlas`. They do not
assert the normed coordinate-change conditions of the stock `VectorBundle` class,
and they do not introduce a fixed model for the original bundle over its whole base.
-/

@[expose] public section

open Bundle Topology

universe uK uB uE uP

namespace Bundle.FiniteRankAtlas

variable {K : Type uK} [Field K] [TopologicalSpace K]
variable {B : Type uB} [TopologicalSpace B]
variable {P : Type uP} {E : B → Type uE}
variable [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
variable [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace P E)]
variable (A : FiniteRankAtlas K P E)

/-- The projection-defined patch subspace is the original chart source, with the
same underlying points and the same inherited topology. -/
def patchSourceHomeomorph (i : A.Index) :
    {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet} ≃ₜ (A.chart i).source where
  toFun p := ⟨p.1, (A.mem_source_iff i p.1).mpr p.2⟩
  invFun p := ⟨p.1, (A.mem_source_iff i p.1).mp p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk
    (fun p => (A.mem_source_iff i p.1).mpr p.2)
  continuous_invFun := continuous_subtype_val.subtype_mk
    (fun p => (A.mem_source_iff i p.1).mp p.2)

/-- The fixed-model patch total space is homeomorphic to the product of the original
chart base set and its standard coordinate model. -/
def patchProductHomeomorph (i : A.Index) :
    @Homeomorph
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      ((A.chart i).baseSet × (Fin (A.rank i) → K))
      (A.patchTopology i) inferInstance :=
  @Homeomorph.trans
    (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
    {p : TotalSpace P E // p.proj ∈ (A.chart i).baseSet}
    ((A.chart i).baseSet × (Fin (A.rank i) → K))
    (A.patchTopology i) inferInstance inferInstance
    (A.patchTotalSpaceHomeomorph i)
    ((A.patchSourceHomeomorph i).trans (A.sourceHomeomorph i))

/-- The product homeomorphism preserves the original base point in the patch. -/
@[simp] theorem patchProductHomeomorph_fst (i : A.Index)
    (p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :
    (A.patchProductHomeomorph i p).1 = p.proj := by
  apply Subtype.ext
  exact A.sourceHomeomorph_fst_coe i _

/-- The product homeomorphism gives exactly the original coordinates of a fibre vector. -/
@[simp] theorem patchProductHomeomorph_mk (i : A.Index)
    (b : (A.chart i).baseSet) (v : E b.1) :
    A.patchProductHomeomorph i (TotalSpace.mk b v) = (b, A.coord i b.1 v) := by
  apply Prod.ext
  · exact A.patchProductHomeomorph_fst i (TotalSpace.mk b v)
  · rfl

/-- The global chart on a patch is the original chart expressed on the restricted
original fibres, with the named topology induced from the original total space. -/
def patchTrivialization (i : A.Index) :
    @Trivialization (A.chart i).baseSet (Fin (A.rank i) → K)
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      inferInstance inferInstance (A.patchTopology i) TotalSpace.proj := by
  letI : TopologicalSpace
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :=
    A.patchTopology i
  exact
    let e := @Homeomorph.toEquiv
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      ((A.chart i).baseSet × (Fin (A.rank i) → K))
      (A.patchTopology i) inferInstance (A.patchProductHomeomorph i)
    @Trivialization.mk (A.chart i).baseSet (Fin (A.rank i) → K)
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
      (@OpenPartialHomeomorph.mk
        (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
        ((A.chart i).baseSet × (Fin (A.rank i) → K))
        (A.patchTopology i) inferInstance
        (@PartialHomeomorph.mk
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K))
          (A.patchTopology i) inferInstance
          (@PartialEquiv.mk
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            ((A.chart i).baseSet × (Fin (A.rank i) → K))
            e e.symm Set.univ Set.univ
            (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
            (fun p _ => e.symm_apply_apply p)
            (fun p _ => e.apply_symm_apply p))
          ((@Homeomorph.continuous_toFun
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            ((A.chart i).baseSet × (Fin (A.rank i) → K))
            (A.patchTopology i) inferInstance (A.patchProductHomeomorph i)).continuousOn)
          ((@Homeomorph.continuous_invFun
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            ((A.chart i).baseSet × (Fin (A.rank i) → K))
            (A.patchTopology i) inferInstance (A.patchProductHomeomorph i)).continuousOn))
        isOpen_univ isOpen_univ)
      Set.univ isOpen_univ (by ext p; rfl) (by ext p; simp)
      (fun p _ => A.patchProductHomeomorph_fst i p)

/-- The patched chart has the whole patch as base set. -/
@[simp] theorem patchTrivialization_baseSet (i : A.Index) :
    @Trivialization.baseSet (A.chart i).baseSet (Fin (A.rank i) → K)
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
      (A.patchTrivialization i) = Set.univ := rfl

/-- The patched chart is defined on the whole patch total space. -/
@[simp] theorem patchTrivialization_source (i : A.Index) :
    @PartialEquiv.source
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      ((A.chart i).baseSet × (Fin (A.rank i) → K))
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
        ((A.chart i).baseSet × (Fin (A.rank i) → K))
        (A.patchTopology i) inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K))
          (A.patchTopology i) inferInstance
          (@Trivialization.toOpenPartialHomeomorph
            (A.chart i).baseSet (Fin (A.rank i) → K)
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
            (A.patchTrivialization i)))) = Set.univ := rfl

/-- The patched chart covers the whole product with its standard model. -/
@[simp] theorem patchTrivialization_target (i : A.Index) :
    @PartialEquiv.target
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
      ((A.chart i).baseSet × (Fin (A.rank i) → K))
      (@PartialHomeomorph.toPartialEquiv
        (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
        ((A.chart i).baseSet × (Fin (A.rank i) → K))
        (A.patchTopology i) inferInstance
        (@OpenPartialHomeomorph.toPartialHomeomorph
          (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
          ((A.chart i).baseSet × (Fin (A.rank i) → K))
          (A.patchTopology i) inferInstance
          (@Trivialization.toOpenPartialHomeomorph
            (A.chart i).baseSet (Fin (A.rank i) → K)
            (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1))
            inferInstance inferInstance (A.patchTopology i) TotalSpace.proj
            (A.patchTrivialization i)))) = Set.univ := rfl

/-- A vector in an original fibre has the same coordinates in the patched chart. -/
@[simp] theorem patchTrivialization_mk (i : A.Index)
    (b : (A.chart i).baseSet) (v : E b.1) :
    A.patchTrivialization i (TotalSpace.mk b v) = (b, A.coord i b.1 v) :=
  A.patchProductHomeomorph_mk i b v

/-- The patched chart evaluates by retaining the patch base point and using the
original fibre coordinate function. -/
theorem patchTrivialization_apply (i : A.Index)
    (p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :
    A.patchTrivialization i p = (p.proj, A.coord i p.proj.1 p.2) := by
  cases p with
  | mk b v => exact A.patchTrivialization_mk i b v

/-- The patched chart preserves the projection everywhere on the patch. -/
@[simp] theorem patchTrivialization_proj (i : A.Index)
    (p : TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :
    (A.patchTrivialization i p).1 = p.proj :=
  A.patchProductHomeomorph_fst i p

/-- The second coordinate of the patched chart is the original coordinate function. -/
@[simp] theorem patchTrivialization_mk_snd (i : A.Index)
    (b : (A.chart i).baseSet) (v : E b.1) :
    (A.patchTrivialization i (TotalSpace.mk b v)).2 = A.coord i b.1 v := by
  rw [A.patchTrivialization_mk]

/-- The patched chart is fibrewise linear for the unchanged original module structures. -/
theorem patchTrivialization_isFiberwiseLinear (i : A.Index) :
    @Trivialization.IsFiberwiseLinear K inferInstance
      (A.chart i).baseSet inferInstance
      (fun b : (A.chart i).baseSet => E b.1) (Fin (A.rank i) → K)
      inferInstance inferInstance (A.patchTopology i)
      (Fin (A.rank i) → K) inferInstance inferInstance inferInstance
      (A.patchTrivialization i) := by
  let : TopologicalSpace
      (TotalSpace (Fin (A.rank i) → K) (fun b : (A.chart i).baseSet => E b.1)) :=
    A.patchTopology i
  constructor
  · intro b _ v w
    simpa only [patchTrivialization_mk_snd] using A.coord_add i b.2 v w
  · intro b _ c v
    simpa only [patchTrivialization_mk_snd] using A.coord_smul i b.2 c v

/-- The patched chart satisfies the stock fixed-model trivialization linearity class. -/
theorem patchTrivialization_isLinear (i : A.Index) :
    @Trivialization.IsLinear K (A.chart i).baseSet (Fin (A.rank i) → K)
      (fun b : (A.chart i).baseSet => E b.1)
      inferInstance inferInstance inferInstance (A.patchTopology i)
      inferInstance inferInstance inferInstance inferInstance (A.patchTrivialization i) :=
  (@Trivialization.isFiberwiseLinear_iff_isLinear K inferInstance
    (A.chart i).baseSet inferInstance (fun b : (A.chart i).baseSet => E b.1)
    inferInstance inferInstance (Fin (A.rank i) → K)
    inferInstance inferInstance inferInstance (A.patchTopology i)
    (A.patchTrivialization i)).mp (A.patchTrivialization_isFiberwiseLinear i)

/-- The given topology on an original fibre is also its induced topology in the patch.
The only total-space topology used here is the named topology induced from the original
chart subspace. -/
theorem patchTotalSpaceMk_isInducing (i : A.Index) (b : (A.chart i).baseSet) :
    @IsInducing (E b.1)
      (TotalSpace (Fin (A.rank i) → K) (fun c : (A.chart i).baseSet => E c.1))
      inferInstance (A.patchTopology i)
      (fun v : E b.1 =>
        @TotalSpace.mk (A.chart i).baseSet (Fin (A.rank i) → K)
          (fun c : (A.chart i).baseSet => E c.1) b v) := by
  let : TopologicalSpace
      (TotalSpace (Fin (A.rank i) → K) (fun c : (A.chart i).baseSet => E c.1)) :=
    A.patchTopology i
  have htop :
      TopologicalSpace.induced
          (fun v : E b.1 =>
            @TotalSpace.mk (A.chart i).baseSet (Fin (A.rank i) → K)
              (fun c : (A.chart i).baseSet => E c.1) b v)
          (A.patchTopology i) =
        TopologicalSpace.induced
          (TotalSpace.mk b.1 : E b.1 → TotalSpace P E) inferInstance := by
    apply TopologicalSpace.ext
    funext s
    apply propext
    constructor
    · rintro ⟨t, ⟨u, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(A.patchTotalSpaceEquiv i) ⁻¹' (Subtype.val ⁻¹' u), ?_, rfl⟩
      exact ⟨Subtype.val ⁻¹' u, ⟨u, hu, rfl⟩, rfl⟩
  rcases A.inducing b.1 with ⟨h⟩
  have horiginal :
      TopologicalSpace.induced
          (TotalSpace.mk b.1 : E b.1 → TotalSpace P E) inferInstance =
        (inferInstance : TopologicalSpace (E b.1)) := by
    first
    | exact h
    | exact h.symm
  have hind := htop.trans horiginal
  first
  | exact ⟨hind⟩
  | exact ⟨hind.symm⟩

/-- Named stock fibre-bundle data on a chart domain. Its atlas consists of the single
global patched chart, chosen at every point. This declaration is not an instance and
does not replace any topology or fibre structure on the original bundle. -/
@[instance_reducible] def patchFiberBundle (i : A.Index) :
    @FiberBundle (A.chart i).baseSet (Fin (A.rank i) → K)
      inferInstance inferInstance (fun b : (A.chart i).baseSet => E b.1)
      (A.patchTopology i) inferInstance :=
  @FiberBundle.mk (A.chart i).baseSet (Fin (A.rank i) → K)
    inferInstance inferInstance (fun b : (A.chart i).baseSet => E b.1)
    (A.patchTopology i) inferInstance
    (A.patchTotalSpaceMk_isInducing i)
    {A.patchTrivialization i} (fun _ => A.patchTrivialization i)
    (fun _ => Set.mem_univ _) (fun _ => rfl)

/-- The named patch atlas has just its canonical global chart. -/
@[simp] theorem patchFiberBundle_trivializationAtlas (i : A.Index) :
    @FiberBundle.trivializationAtlas' (A.chart i).baseSet (Fin (A.rank i) → K)
      inferInstance inferInstance (fun b : (A.chart i).baseSet => E b.1)
      (A.patchTopology i) inferInstance (A.patchFiberBundle i) =
        {A.patchTrivialization i} := rfl

/-- At every patch base point the named bundle data use the canonical patched chart. -/
@[simp] theorem patchFiberBundle_trivializationAt (i : A.Index)
    (b : (A.chart i).baseSet) :
    @FiberBundle.trivializationAt' (A.chart i).baseSet (Fin (A.rank i) → K)
      inferInstance inferInstance (fun b : (A.chart i).baseSet => E b.1)
      (A.patchTopology i) inferInstance (A.patchFiberBundle i) b =
        A.patchTrivialization i := rfl

end Bundle.FiniteRankAtlas
