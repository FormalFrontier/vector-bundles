/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas

/-!
# Finite-rank atlases for projector kernels

The complementary projector identifies its range with the original kernel submodule.
The range atlas supplies coordinates on the original kernel graph, using one fixed
coordinate equivalence at each anchor. Its forward transport includes the inverse
fixed-range compression. Its ambient inverse formula is global, while chart inverse
laws hold on the full strict unit-gap neighborhood.
-/

@[expose] public section

universe uK uA uX uF

namespace ContinuousLinearMap

variable {K : Type uK} [NontriviallyNormedField K]
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]

variable {X : Type uX} [TopologicalSpace X]

/-- Chart families on the kernel graph, with the finite-coordinate model of each anchor.
The graph topology is induced by the inclusion into `X × A`. -/
def KernelAtlasCharts (F : Type uF) (P : X → A →L[K] A) : Type _ := by
  let E : X → Type uA := fun x => ↥(LinearMap.ker (P x).toLinearMap)
  letI : TopologicalSpace (Bundle.TotalSpace F E) :=
    TopologicalSpace.induced
      (fun p : Bundle.TotalSpace F E => (p.proj, (p.2 : A))) inferInstance
  exact (c : X) → Bundle.Trivialization (Fin (Module.finrank K (E c)) → K)
    (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → X)

/-- A kernel chart family is fibrewise linear, covers the base, and induces the given
fibre topologies. Its domains are the full strict unit-gap neighborhoods; complementary
projection preserves anchor coordinates there and gives the ambient inverse everywhere. -/
def IsKernelAtlasChartFamily (F : Type uF) (P : X → A →L[K] A)
    (C : KernelAtlasCharts F P) : Prop := by
  let E : X → Type uA := fun x => ↥(LinearMap.ker (P x).toLinearMap)
  letI : TopologicalSpace (Bundle.TotalSpace F E) :=
    TopologicalSpace.induced
      (fun p : Bundle.TotalSpace F E => (p.proj, (p.2 : A))) inferInstance
  exact
    (∀ c : X, (C c).IsFiberwiseLinear (K := K)) ∧
      (∀ x : X, ∃ c : X, x ∈ (C c).baseSet) ∧
      (∀ x : X, Topology.IsInducing
        (fun v : E x => (⟨x, v⟩ : Bundle.TotalSpace F E))) ∧
      (∀ c : X, (C c).baseSet = {x | ‖P x - P c‖ < 1}) ∧
      (∀ (c x : X), ‖P x - P c‖ < 1 →
        ∀ (v : E c) (w : E x), (w : A) = (1 - P x) (v : A) →
          (C c ⟨x, w⟩).2 = (C c ⟨c, v⟩).2) ∧
      (∀ (c x : X) (v : Fin (Module.finrank K (E c)) → K),
        (((C c).invFun (x, v)).2 : A) =
          (1 - P x) (((C c).invFun (c, v)).2 : A))

namespace KernelAtlasCharts

/-- The base set of a chart on the kernel graph. -/
def baseSet {F : Type uF} {P : X → A →L[K] A}
    (C : KernelAtlasCharts F P) (c : X) : Set X := by
  let E : X → Type uA := fun x => ↥(LinearMap.ker (P x).toLinearMap)
  letI : TopologicalSpace (Bundle.TotalSpace F E) :=
    TopologicalSpace.induced
      (fun e : Bundle.TotalSpace F E => (e.proj, (e.2 : A))) inferInstance
  exact (C c).baseSet

/-- Two kernel chart families agree when they agree at every anchor. -/
@[ext] theorem ext {F : Type uF} {P : X → A →L[K] A}
    {C D : KernelAtlasCharts F P} (h : ∀ c, C c = D c) : C = D :=
  funext h

end KernelAtlasCharts

namespace IsKernelAtlasChartFamily

variable {F : Type uF} {P : X → A →L[K] A} {C : KernelAtlasCharts F P}

/-- The six geometric laws construct a kernel chart family predicate. -/
theorem mk
    (linear : ∀ c : X,
      @Bundle.Trivialization.IsFiberwiseLinear K _ X _
        (fun x => ↥(LinearMap.ker (P x).toLinearMap)) F _ _
        (TopologicalSpace.induced
          (fun e : Bundle.TotalSpace F
              (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
            (e.proj, (e.2 : A))) inferInstance)
        (Fin (Module.finrank K (LinearMap.ker (P c).toLinearMap)) → K) _ _ _ (C c))
    (cover : ∀ x : X, ∃ c : X, x ∈ C.baseSet c)
    (inducing : ∀ x : X, @Topology.IsInducing _ _ inferInstance
      (TopologicalSpace.induced
        (fun p : Bundle.TotalSpace F (fun y => ↥(LinearMap.ker (P y).toLinearMap)) =>
          (p.proj, (p.2 : A))) inferInstance)
      (fun v : LinearMap.ker (P x).toLinearMap =>
        (⟨x, v⟩ : Bundle.TotalSpace F (fun y => ↥(LinearMap.ker (P y).toLinearMap)))))
    (baseSet : ∀ c : X, C.baseSet c = {x | ‖P x - P c‖ < 1})
    (anchor_transport : ∀ (c x : X), ‖P x - P c‖ < 1 →
      ∀ (v : LinearMap.ker (P c).toLinearMap) (w : LinearMap.ker (P x).toLinearMap),
        (w : A) = (1 - P x) (v : A) → (C c ⟨x, w⟩).2 = (C c ⟨c, v⟩).2)
    (inverse_ambient : ∀ (c x : X)
      (v : Fin (Module.finrank K (LinearMap.ker (P c).toLinearMap)) → K),
      (((C c).invFun (x, v)).2 : A) =
        (1 - P x) (((C c).invFun (c, v)).2 : A)) :
    IsKernelAtlasChartFamily F P C :=
  ⟨linear, cover, inducing, baseSet, anchor_transport, inverse_ambient⟩

/-- Each chart of a kernel chart family is fibrewise linear. -/
theorem linear (hC : IsKernelAtlasChartFamily F P C) (c : X) :
    @Bundle.Trivialization.IsFiberwiseLinear K _ X _
      (fun x => ↥(LinearMap.ker (P x).toLinearMap)) F _ _
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F
            (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (Fin (Module.finrank K (LinearMap.ker (P c).toLinearMap)) → K) _ _ _ (C c) :=
  hC.1 c

/-- The domains of a kernel chart family cover the base. -/
theorem cover (hC : IsKernelAtlasChartFamily F P C) (x : X) :
    ∃ c : X, x ∈ C.baseSet c :=
  hC.2.1 x

/-- Each kernel fibre has its given topology inside the kernel graph. -/
theorem inducing (hC : IsKernelAtlasChartFamily F P C) (x : X) :
    @Topology.IsInducing _ _ inferInstance
      (TopologicalSpace.induced
        (fun p : Bundle.TotalSpace F (fun y => ↥(LinearMap.ker (P y).toLinearMap)) =>
          (p.proj, (p.2 : A))) inferInstance)
      (fun v : LinearMap.ker (P x).toLinearMap =>
        (⟨x, v⟩ : Bundle.TotalSpace F (fun y => ↥(LinearMap.ker (P y).toLinearMap)))) :=
  hC.2.2.1 x

/-- A kernel chart domain is the full strict unit-gap neighborhood of its anchor. -/
theorem baseSet (hC : IsKernelAtlasChartFamily F P C) (c : X) :
    C.baseSet c = {x | ‖P x - P c‖ < 1} :=
  hC.2.2.2.1 c

/-- Complementary projection preserves anchor coordinates on the unit-gap neighborhood. -/
theorem anchor_transport (hC : IsKernelAtlasChartFamily F P C)
    (c x : X) (hx : ‖P x - P c‖ < 1)
    (v : LinearMap.ker (P c).toLinearMap) (w : LinearMap.ker (P x).toLinearMap)
    (hw : (w : A) = (1 - P x) (v : A)) :
    (C c ⟨x, w⟩).2 = (C c ⟨c, v⟩).2 :=
  hC.2.2.2.2.1 c x hx v w hw

/-- The ambient inverse formula holds at every base point, without a unit-gap hypothesis. -/
theorem inverse_ambient (hC : IsKernelAtlasChartFamily F P C) (c x : X)
    (v : Fin (Module.finrank K (LinearMap.ker (P c).toLinearMap)) → K) :
    (((C c).invFun (x, v)).2 : A) =
      (1 - P x) (((C c).invFun (c, v)).2 : A) :=
  hC.2.2.2.2.2 c x v

end IsKernelAtlasChartFamily

/-- Kernel chart families together with their six geometric laws. -/
abbrev KernelAtlasChartData (F : Type uF) (P : X → A →L[K] A) :=
  {C : KernelAtlasCharts F P // IsKernelAtlasChartFamily F P C}

/-- Kernel chart data agree when their chart families agree at every anchor. -/
@[ext] theorem KernelAtlasChartData.ext {F : Type uF} {P : X → A →L[K] A}
    {D1 D2 : KernelAtlasChartData F P} (h : ∀ c, D1.val c = D2.val c) : D1 = D2 := by
  apply Subtype.ext
  exact KernelAtlasCharts.ext h

/-- The complementary-range construction gives kernel chart data for a continuous family
of idempotents with finite-dimensional kernels carrying their module topologies.
The charts and all six laws are transported together along equality of the range of the
complementary projector with the original kernel submodule. -/
noncomputable def kernelAtlasChartData (F : Type uF)
    (P : X → A →L[K] A) (hP : Continuous P)
    (hid : ∀ x, IsIdempotentElem (P x))
    (hfd : ∀ x, FiniteDimensional K (LinearMap.ker (P x).toLinearMap))
    (hmt : ∀ x, IsModuleTopology K (LinearMap.ker (P x).toLinearMap)) :
    KernelAtlasChartData F P := by
  classical
  let Q : X → A →L[K] A := fun x => 1 - P x
  have hQ : Continuous Q := continuous_const.sub hP
  have hQid (x : X) : IsIdempotentElem (Q x) := by
    change IsIdempotentElem (1 - P x)
    exact (hid x).one_sub
  let S : X → Submodule K A := fun x => LinearMap.range (Q x).toLinearMap
  let E : X → Submodule K A := fun x => LinearMap.ker (P x).toLinearMap
  have hS (x : X) : S x = E x := by
    change LinearMap.range (1 - P x).toLinearMap = LinearMap.ker (P x).toLinearMap
    have hp : IsIdempotentElem (P x).toLinearMap :=
      congrArg (fun T : A →L[K] A => T.toLinearMap) (hid x)
    exact (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp).symm
  have hSE : S = E := funext hS
  have hfdQ (x : X) : FiniteDimensional K (S x) := by
    rw [hS x]
    exact hfd x
  have hmtQ (x : X) : IsModuleTopology K (S x) := by
    rw [hS x]
    exact hmt x
  let a := finiteRankRangeAtlas F Q hQ hQid hfdQ hmtQ
  let τ (R : X → Submodule K A) :
      TopologicalSpace (Bundle.TotalSpace F (fun x => ↥(R x))) :=
    TopologicalSpace.induced
      (fun p : Bundle.TotalSpace F (fun x => ↥(R x)) =>
        (p.proj, (p.2 : A))) inferInstance
  let Charts (R : X → Submodule K A) : Type _ :=
    letI : TopologicalSpace (Bundle.TotalSpace F (fun x => ↥(R x))) := τ R
    (c : X) → Bundle.Trivialization (Fin (Module.finrank K (R c)) → K)
      (Bundle.TotalSpace.proj : Bundle.TotalSpace F (fun x => ↥(R x)) → X)
  let cS : Charts S := by
    change
      letI : TopologicalSpace (Bundle.TotalSpace F (fun x => ↥(S x))) :=
        VectorBundle.rangeTotalSpaceTopology (fun x => (Q x).toLinearMap)
      (c : X) → Bundle.Trivialization (Fin (Module.finrank K (S c)) → K)
        (Bundle.TotalSpace.proj :
          Bundle.TotalSpace F (fun x => ↥(S x)) → X)
    exact a.chart
  have hgap (c x : X) : ‖Q x - Q c‖ = ‖P x - P c‖ := by
    change ‖(1 - P x) - (1 - P c)‖ = ‖P x - P c‖
    have h : (1 - P x) - (1 - P c) = -(P x - P c) := by abel
    rw [h, norm_neg]
  let Specs (R : X → Submodule K A) (D : Charts R) : Prop :=
    letI : TopologicalSpace (Bundle.TotalSpace F (fun x => ↥(R x))) := τ R
    (∀ c : X, (D c).IsFiberwiseLinear (K := K)) ∧
      (∀ x : X, ∃ c : X, x ∈ (D c).baseSet) ∧
      (∀ x : X, Topology.IsInducing
        (fun v : R x =>
          (⟨x, v⟩ : Bundle.TotalSpace F (fun y => ↥(R y))))) ∧
      (∀ c : X, (D c).baseSet = {x | ‖P x - P c‖ < 1}) ∧
      (∀ (c x : X), ‖P x - P c‖ < 1 →
        ∀ (v : R c) (w : R x), (w : A) = Q x (v : A) →
          (D c ⟨x, w⟩).2 = (D c ⟨c, v⟩).2) ∧
      (∀ (c x : X) (v : Fin (Module.finrank K (R c)) → K),
        (((D c).invFun (x, v)).2 : A) =
          Q x (((D c).invFun (c, v)).2 : A))
  have hcS : Specs S cS := by
    refine ⟨a.linear, a.cover, a.inducing, ?_, ?_, ?_⟩
    · intro c
      change ((finiteRankRangeAtlas F Q hQ hQid hfdQ hmtQ).chart c).baseSet =
        {x | ‖P x - P c‖ < 1}
      simpa only [hgap] using
        (finiteRankRangeAtlas_baseSet (hfd := hfdQ) (hmt := hmtQ)
          F Q hQ hQid c)
    · intro c x hx v w hw
      let : FiniteDimensional K (S c) := hfdQ c
      have hxQ : ‖Q x - Q c‖ < 1 := by
        rw [hgap c x]
        exact hx
      let e := nearbyRangeEquiv (Q c) (Q x) (hQid c) (hQid x) hxQ
      have he : e v = w := by
        apply Subtype.ext
        simp only [e, nearbyRangeEquiv_apply]
        exact hw.symm
      have hes : e.symm w = v := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact he.symm
      have hs := finiteRankRangeAtlas_anchor_transport
        (hfd := hfdQ) (hmt := hmtQ) F Q hQ hQid c x hxQ w
      change (cS c ⟨x, w⟩).2 = (cS c ⟨c, e.symm w⟩).2 at hs
      rw [hes] at hs
      exact hs
    · intro c x v
      exact finiteRankRangeAtlas_inverse_ambient (hfd := hfdQ) (hmt := hmtQ)
        F Q hQ hQid c x v
  -- Transport each chart together with its laws along equality of the fibre submodules.
  let Data (R : X → Submodule K A) := {D : Charts R // Specs R D}
  let dS : Data S := ⟨cS, hcS⟩
  let dE : Data E := Eq.mp (congrArg Data hSE) dS
  change Data E
  exact dE

/-- A continuous family of idempotents with finite-dimensional kernels carrying their
module topologies has a finite-coordinate atlas on its original kernel graph.
The total-space topology is induced by the original inclusion into `X × A`.
Its chart indices are base points, with rank given by the dimension of the anchor kernel. -/
@[reducible]
noncomputable def finiteRankKernelAtlas (F : Type uF)
    (P : X → A →L[K] A) (hP : Continuous P)
    (hid : ∀ x, IsIdempotentElem (P x))
    (hfd : ∀ x, FiniteDimensional K (LinearMap.ker (P x).toLinearMap))
    (hmt : ∀ x, IsModuleTopology K (LinearMap.ker (P x).toLinearMap)) :
    @Bundle.FiniteRankAtlas K _ _ X _ F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance) := by
  letI : TopologicalSpace
      (Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap))) :=
    TopologicalSpace.induced
      (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
        (e.proj, (e.2 : A))) inferInstance
  let D := kernelAtlasChartData F P hP hid hfd hmt
  exact {
    Index := X
    rank := fun c => Module.finrank K (LinearMap.ker (P c).toLinearMap)
    chart := D.val
    linear := D.property.linear
    cover := D.property.cover
    inducing := D.property.inducing }

section

variable (F : Type uF) (P : X → A →L[K] A) (hP : Continuous P)
variable (hid : ∀ x, IsIdempotentElem (P x))
variable (hfd : ∀ x, FiniteDimensional K (LinearMap.ker (P x).toLinearMap))
variable (hmt : ∀ x, IsModuleTopology K (LinearMap.ker (P x).toLinearMap))

/-- The canonical kernel chart domain is the full strict unit-gap neighborhood. -/
theorem kernelAtlasChartData_baseSet (c : X) :
    (kernelAtlasChartData F P hP hid hfd hmt).val.baseSet c =
      {x | ‖P x - P c‖ < 1} :=
  (kernelAtlasChartData F P hP hid hfd hmt).property.baseSet c

/-- Membership in a canonical kernel chart domain is the strict unit-gap condition. -/
@[simp] theorem kernelAtlasChartData_mem_baseSet (c x : X) :
    x ∈ (kernelAtlasChartData F P hP hid hfd hmt).val.baseSet c ↔
      ‖P x - P c‖ < 1 := by
  rw [kernelAtlasChartData_baseSet F P hP hid hfd hmt c]
  rfl

/-- The kernel atlas uses the charts of the complementary-range construction. -/
@[simp] theorem finiteRankKernelAtlas_chart (c : X) :
    (@Bundle.FiniteRankAtlas.chart K inferInstance inferInstance X inferInstance F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
        A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
        X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c) =
      (kernelAtlasChartData F P hP hid hfd hmt).val c := by
  rfl

/-- The model dimension is the dimension of the original anchor kernel. -/
theorem finiteRankKernelAtlas_rank (c : X) :
    (@Bundle.FiniteRankAtlas.rank K inferInstance inferInstance X inferInstance F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
        A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
        X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c) =
      Module.finrank K (LinearMap.ker (P c).toLinearMap) := rfl

/-- The chart domain is the full strict unit-gap neighborhood of its anchor. -/
theorem finiteRankKernelAtlas_baseSet (c : X) :
    (@Bundle.FiniteRankAtlas.baseSet K inferInstance inferInstance X inferInstance F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
        A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
        X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c) =
      {x | ‖P x - P c‖ < 1} := by
  change (kernelAtlasChartData F P hP hid hfd hmt).val.baseSet c =
    {x | ‖P x - P c‖ < 1}
  exact kernelAtlasChartData_baseSet F P hP hid hfd hmt c

/-- Applying the complementary projector transports anchor vectors without changing
their coordinates on the strict unit-gap neighborhood. -/
theorem finiteRankKernelAtlas_anchor_transport (c x : X) (hx : ‖P x - P c‖ < 1)
    (v : LinearMap.ker (P c).toLinearMap) (w : LinearMap.ker (P x).toLinearMap)
    (hw : (w : A) = (1 - P x) (v : A)) :
    ((@Bundle.FiniteRankAtlas.chart K inferInstance inferInstance X inferInstance F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
        A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
        X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c) ⟨x, w⟩).2 =
      ((@Bundle.FiniteRankAtlas.chart K inferInstance inferInstance X inferInstance F
        (fun x => ↥(LinearMap.ker (P x).toLinearMap))
        inferInstance inferInstance inferInstance
        (TopologicalSpace.induced
          (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
            (e.proj, (e.2 : A))) inferInstance)
        (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
          A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
          X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c) ⟨c, v⟩).2 := by
  rw [finiteRankKernelAtlas_chart F P hP hid hfd hmt c]
  exact (kernelAtlasChartData F P hP hid hfd hmt).property.anchor_transport c x hx v w hw

/-- At every base point, the ambient inverse vector is the complementary projector
applied to the anchor inverse vector; no chart-domain hypothesis is required. -/
theorem finiteRankKernelAtlas_inverse_ambient (c x : X)
    (v : Fin (Module.finrank K (LinearMap.ker (P c).toLinearMap)) → K) :
    (((@Bundle.FiniteRankAtlas.chart K inferInstance inferInstance X inferInstance F
      (fun x => ↥(LinearMap.ker (P x).toLinearMap))
      inferInstance inferInstance inferInstance
      (TopologicalSpace.induced
        (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
          (e.proj, (e.2 : A))) inferInstance)
      (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
        A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
        X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c).invFun (x, v)).2 : A) =
      (1 - P x)
        (((@Bundle.FiniteRankAtlas.chart K inferInstance inferInstance X inferInstance F
          (fun x => ↥(LinearMap.ker (P x).toLinearMap))
          inferInstance inferInstance inferInstance
          (TopologicalSpace.induced
            (fun e : Bundle.TotalSpace F (fun x => ↥(LinearMap.ker (P x).toLinearMap)) =>
              (e.proj, (e.2 : A))) inferInstance)
          (@finiteRankKernelAtlas K (inferInstance : NontriviallyNormedField K)
            A (inferInstance : NormedAddCommGroup A) (inferInstance : NormedSpace K A)
            X (inferInstance : TopologicalSpace X) F P hP hid hfd hmt) c).invFun
              (c, v)).2 : A) := by
  rw [finiteRankKernelAtlas_chart F P hP hid hfd hmt c]
  exact (kernelAtlasChartData F P hP hid hfd hmt).property.inverse_ambient c x v

/-- The original kernel-graph patch over a strict unit-gap neighborhood is a product
with the fixed finite-coordinate model of its anchor kernel. -/
noncomputable def finiteRankKernelAtlasLocalProduct (c : X) :
    let E : X → Type uA := fun x => ↥(LinearMap.ker (P x).toLinearMap)
    @Homeomorph
      {e : Bundle.TotalSpace F E // ‖P e.proj - P c‖ < 1}
      ({x : X // ‖P x - P c‖ < 1} × (Fin (Module.finrank K (E c)) → K))
      (TopologicalSpace.induced
        (Subtype.val : {e : Bundle.TotalSpace F E // ‖P e.proj - P c‖ < 1} →
          Bundle.TotalSpace F E)
        (TopologicalSpace.induced
          (fun e : Bundle.TotalSpace F E => (e.proj, (e.2 : A))) inferInstance))
      inferInstance := by
  let E : X → Type uA := fun x => ↥(LinearMap.ker (P x).toLinearMap)
  letI : TopologicalSpace (Bundle.TotalSpace F E) :=
    TopologicalSpace.induced
      (fun e : Bundle.TotalSpace F E => (e.proj, (e.2 : A))) inferInstance
  change {e : Bundle.TotalSpace F E // ‖P e.proj - P c‖ < 1} ≃ₜ
    ({x : X // ‖P x - P c‖ < 1} × (Fin (Module.finrank K (E c)) → K))
  let a := finiteRankKernelAtlas F P hP hid hfd hmt
  have hbase : a.baseSet c = {x | ‖P x - P c‖ < 1} := by
    exact finiteRankKernelAtlas_baseSet F P hP hid hfd hmt c
  change (a.chart c).baseSet = {x | ‖P x - P c‖ < 1} at hbase
  have hsource : (a.chart c).source =
      {e : Bundle.TotalSpace F E | ‖P e.proj - P c‖ < 1} := by
    ext e
    change e ∈ (a.chart c).source ↔ ‖P e.proj - P c‖ < 1
    rw [a.mem_source_iff c e, hbase]
    rfl
  have hrank : a.rank c = Module.finrank K (E c) := rfl
  have hlocal :
      (a.chart c).source ≃ₜ
        (a.chart c).baseSet × (Fin (a.rank c) → K) :=
    a.sourceHomeomorph c
  rw [hsource, hbase, hrank] at hlocal
  exact hlocal

-- Retain the deprecated spelling for compatibility of the product homeomorphism.
@[deprecated (since := "2026-11-03"), nolint defsWithUnderscore]
alias finiteRankKernelAtlas_localProduct := finiteRankKernelAtlasLocalProduct

end

end ContinuousLinearMap
