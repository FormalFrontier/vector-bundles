/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Section
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Lifting fiber values to continuous sections

For a vector bundle over a completely regular base,
`VectorBundle.continuousSectionLift` lifts a value in a fiber to a global continuous
section, linearly over the scalar field. Its characteristic value at the chosen point
is `VectorBundle.continuousSectionLift_apply_self`. Consequently, composition with
`VectorBundle.continuousSectionEval` is the identity and evaluation is surjective.

The scalar field is a real algebra with continuous real scalar multiplication. Only
the model fiber is normed; the given fiber and total-space topologies and the given
bundle structures are retained. No topology on the module of sections is needed.
Linearity is over constant scalars, not over the ring of continuous scalar functions.

## References

* Mathlib's completely regular spaces and continuous real-algebra scalar maps.
* The continuous-section module and its constant-scalar evaluation API.
-/

@[expose] public section

private theorem exists_continuous_cutoff {B : Type*} [TopologicalSpace B]
    [CompletelyRegularSpace B] (x : B) (U : Set B) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ φ : C(B, ℝ), φ x = 1 ∧ tsupport (φ : B → ℝ) ⊆ U := by
  obtain ⟨V, ⟨hxV, hV⟩, hVU⟩ :=
    (hasBasis_opens_closure x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨f, hf, hfx, hfV⟩ :=
    CompletelyRegularSpace.completely_regular_isOpen x V hV hxV
  let φ : C(B, ℝ) := ⟨fun y ↦ 1 - (f y : ℝ),
    continuous_const.sub (continuous_subtype_val.comp hf)⟩
  refine ⟨φ, ?_, ?_⟩
  · change 1 - (f x : ℝ) = 1
    rw [hfx]
    simp
  · have hsupport : Function.support (φ : B → ℝ) ⊆ V := by
      intro y hy
      by_contra hyV
      have hfy := hfV hyV
      have hφy : φ y = 0 := by
        change 1 - (f y : ℝ) = 0
        rw [hfy]
        simp
      exact hy hφy
    exact (closure_mono hsupport).trans hVU

open Bundle

universe u𝕜 uB uF uE

private noncomputable def continuousCutoff
    {B : Type uB} [TopologicalSpace B] [CompletelyRegularSpace B]
    (x : B) (U : Set B) (hU : IsOpen U) (hx : x ∈ U) : C(B, ℝ) :=
  Classical.choose (exists_continuous_cutoff x U hU hx)

private theorem continuousCutoff_spec
    {B : Type uB} [TopologicalSpace B] [CompletelyRegularSpace B]
    (x : B) (U : Set B) (hU : IsOpen U) (hx : x ∈ U) :
    continuousCutoff x U hU hx x = 1 ∧
      tsupport (continuousCutoff x U hU hx : B → ℝ) ⊆ U :=
  Classical.choose_spec (exists_continuous_cutoff x U hU hx)

namespace VectorBundle

/-- A scalar-linear lift of a fiber value to a global continuous section. Evaluation
at the chosen point recovers the value, as stated in `continuousSectionLift_apply_self`. -/
@[no_expose]
noncomputable def continuousSectionLift
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    [Algebra ℝ 𝕜] [ContinuousSMul ℝ 𝕜]
    {B : Type uB} [TopologicalSpace B] [CompletelyRegularSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (x : B) : E x →ₗ[𝕜] continuousSectionSubmodule 𝕜 F E := by
  classical
  let e := trivializationAt F E x
  let φ : C(B, ℝ) := continuousCutoff x e.baseSet e.open_baseSet
    (FiberBundle.mem_baseSet_trivializationAt F E x)
  have hφ : tsupport (φ : B → ℝ) ⊆ e.baseSet :=
    (continuousCutoff_spec x e.baseSet e.open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt F E x)).2
  let g (v : E x) : C(B, F) :=
    ⟨fun b ↦ algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x v,
      ((continuous_algebraMap ℝ 𝕜).comp φ.continuous).smul continuous_const⟩
  have hg (v : E x) : tsupport (g v : B → F) ⊆ e.baseSet :=
    (tsupport_smul_subset_left (fun b ↦ algebraMap ℝ 𝕜 (φ b))
      (fun _ ↦ e.linearMapAt 𝕜 x v)).trans
        ((tsupport_comp_subset (map_zero (algebraMap ℝ 𝕜)) (φ : B → ℝ)).trans hφ)
  refine
    { toFun := fun v ↦ ⟨fun b ↦ e.symmL 𝕜 b (g v b),
        e.continuous_section_symmL_of_tsupport_subset
          (𝕜 := 𝕜) (g v) (g v).continuous (hg v)⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    apply Subtype.ext
    funext b
    change e.symmL 𝕜 b (algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x (v + w)) =
      e.symmL 𝕜 b (algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x v) +
        e.symmL 𝕜 b (algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x w)
    rw [map_add, smul_add, map_add]
  · intro a v
    apply Subtype.ext
    funext b
    change e.symmL 𝕜 b (algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x (a • v)) =
      a • e.symmL 𝕜 b (algebraMap ℝ 𝕜 (φ b) • e.linearMapAt 𝕜 x v)
    rw [(e.linearMapAt 𝕜 x).map_smul,
      smul_comm (algebraMap ℝ 𝕜 (φ b)) a, (e.symmL 𝕜 b).map_smul]

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  [realAlgebra : Algebra ℝ 𝕜] [realSMulContinuous : ContinuousSMul ℝ 𝕜]
  {B : Type uB} [TopologicalSpace B] [completelyRegular : CompletelyRegularSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The lifted section takes the prescribed value at the chosen point. -/
@[simp] theorem continuousSectionLift_apply_self (x : B) (v : E x) :
    (continuousSectionLift (𝕜 := 𝕜) (F := F) (E := E) x v).1 x = v := by
  let e := trivializationAt F E x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F E x
  have hφ := (continuousCutoff_spec x e.baseSet e.open_baseSet hx).1
  change e.symmL 𝕜 x
    (algebraMap ℝ 𝕜 (continuousCutoff x e.baseSet e.open_baseSet hx x) •
      e.linearMapAt 𝕜 x v) = v
  rw [hφ, map_one, one_smul]
  exact e.symmL_continuousLinearMapAt hx v

/-- Evaluation after lifting is the identity linear map on the original fiber. -/
theorem continuousSectionEval_comp_lift (x : B) :
    (continuousSectionEval (𝕜 := 𝕜) (F := F) (E := E) x).comp
      (continuousSectionLift (𝕜 := 𝕜) (F := F) (E := E) x) = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, continuousSectionEval_apply,
    continuousSectionLift_apply_self, LinearMap.id_apply]

include realAlgebra realSMulContinuous completelyRegular in
/-- Every fiber value is attained by a global continuous section. -/
theorem continuousSectionEval_surjective (x : B) :
    Function.Surjective (continuousSectionEval (𝕜 := 𝕜) (F := F) (E := E) x) := by
  intro v
  refine ⟨continuousSectionLift (𝕜 := 𝕜) (F := F) (E := E) x v, ?_⟩
  simp only [continuousSectionEval_apply, continuousSectionLift_apply_self]

end VectorBundle
