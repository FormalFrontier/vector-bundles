/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.Algebra.Support

/-!
# Weighted sesquilinear forms in a bundle chart

A continuous form on the model fiber, semilinear in its first slot and linear in its second,
pulls back along a linear bundle chart.
Multiplying it by a continuous scalar function whose topological support lies in the chart
produces a continuous section of the iterated hom bundle. No norm on the individual fibers
or separation hypothesis on the base is required.

The construction uses Mathlib's zero-extended `Trivialization.continuousLinearMapAt`, and
continuity on the chart is read using the iterated hom trivialization from Mathlib's
`Topology.VectorBundle.Hom`. Off the topological support the section is locally zero; no
continuity of the zero-extended chart map at the chart boundary is asserted. For continuity,
the first-slot scalar endomorphism need only be isometric, not surjective. The identity
specialization recovers weighted bilinear forms over any nontrivially normed field.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Proposition 1.2: the weighted
  local-form step in the partition-of-unity construction.
* Mathlib's hom-bundle constructions, by Heather Macbeth and Floris van Doorn, and its
  bounded-convergence topology on spaces of continuous linear maps.
-/

@[expose] public section

noncomputable section

open Bundle Set Topology
open scoped Bundle

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]
  (e : Trivialization F (π F E)) {σ : 𝕜 →+* 𝕜}

section

variable [e.IsLinear 𝕜]

/-- Pull a continuous form, `σ`-semilinear in the first slot and linear in the second, back
along a chart and multiply it by a scalar weight. The result is defined on every fiber,
using the zero extension of the chart's continuous linear map. -/
def weightedSesquilinearForm (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) (b : B) :
    E b →SL[σ] E b →L[𝕜] 𝕜 :=
  φ b • ((e.continuousLinearMapAt 𝕜 b).precomp 𝕜).comp
    (q.comp (e.continuousLinearMapAt 𝕜 b))

/-- Evaluation of the weighted pullback is the weighted form evaluated on chart coordinates. -/
@[simp]
theorem weightedSesquilinearForm_apply (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜)
    (b : B) (v w : E b) :
    e.weightedSesquilinearForm q φ b v w =
      φ b * q (e.continuousLinearMapAt 𝕜 b v) (e.continuousLinearMapAt 𝕜 b w) :=
  rfl

/-- On the chart, evaluation uses the chart coordinates of the two vectors. -/
theorem weightedSesquilinearForm_apply_of_mem (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜)
    {b : B} (hb : b ∈ e.baseSet) (v w : E b) :
    e.weightedSesquilinearForm q φ b v w = φ b * q (e ⟨b, v⟩).2 (e ⟨b, w⟩).2 := by
  simp [continuousLinearMapAt_apply_of_mem, hb]

/-- The weighted form vanishes away from the topological support of the weight. -/
theorem weightedSesquilinearForm_eq_zero_of_notMem_tsupport
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ tsupport φ) :
    e.weightedSesquilinearForm q φ b = 0 := by
  ext v w
  simp [image_eq_zero_of_notMem_tsupport hb]

/-- Outside the topological support of the weight, the weighted form is locally zero. -/
theorem eventually_weightedSesquilinearForm_eq_zero
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ tsupport φ) :
    ∀ᶠ c in 𝓝 b, e.weightedSesquilinearForm q φ c = 0 := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hb] with c hc
  exact weightedSesquilinearForm_eq_zero_of_notMem_tsupport e q φ hc

/-- A zero scalar weight gives the zero form on every fiber. -/
@[simp]
theorem weightedSesquilinearForm_zero_weight (q : F →SL[σ] F →L[𝕜] 𝕜) (b : B) :
    e.weightedSesquilinearForm q 0 b = 0 := by
  ext v w
  simp

/-- Outside the chart the weighted form is zero, irrespective of the weight. -/
theorem weightedSesquilinearForm_eq_zero_of_notMem_baseSet
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ e.baseSet) :
    e.weightedSesquilinearForm q φ b = 0 := by
  ext v w
  simp [continuousLinearMapAt_apply, linearMapAt_def_of_notMem e hb]

/-- Pull a continuous bilinear form on the model fiber back along a chart and multiply it
by a scalar weight. The result is defined on every fiber, using the zero extension of the
chart's continuous linear map. -/
def weightedBilinearForm (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) (b : B) :
    E b →L[𝕜] E b →L[𝕜] 𝕜 :=
  e.weightedSesquilinearForm (σ := RingHom.id 𝕜) q φ b

/-- Evaluation of the weighted pullback is the weighted form evaluated on chart coordinates. -/
@[simp]
theorem weightedBilinearForm_apply (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜)
    (b : B) (v w : E b) :
    e.weightedBilinearForm q φ b v w =
      φ b * q (e.continuousLinearMapAt 𝕜 b v) (e.continuousLinearMapAt 𝕜 b w) :=
  e.weightedSesquilinearForm_apply q φ b v w

/-- The weighted form vanishes away from the topological support of the weight. -/
theorem weightedBilinearForm_eq_zero_of_notMem_tsupport
    (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ tsupport φ) :
    e.weightedBilinearForm q φ b = 0 :=
  e.weightedSesquilinearForm_eq_zero_of_notMem_tsupport q φ hb

/-- Outside the topological support of the weight, the weighted form is locally zero. -/
theorem eventually_weightedBilinearForm_eq_zero
    (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ tsupport φ) :
    ∀ᶠ c in 𝓝 b, e.weightedBilinearForm q φ c = 0 :=
  e.eventually_weightedSesquilinearForm_eq_zero q φ hb

/-- A zero scalar weight gives the zero form on every fiber. -/
@[simp]
theorem weightedBilinearForm_zero_weight (q : F →L[𝕜] F →L[𝕜] 𝕜) (b : B) :
    e.weightedBilinearForm q 0 b = 0 :=
  e.weightedSesquilinearForm_zero_weight q b

/-- Outside the chart the weighted form is zero, irrespective of the weight. -/
theorem weightedBilinearForm_eq_zero_of_notMem_baseSet
    (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ e.baseSet) :
    e.weightedBilinearForm q φ b = 0 :=
  e.weightedSesquilinearForm_eq_zero_of_notMem_baseSet q φ hb

end

/-- On the trivial bundle with its standard chart, the construction is just the scalar
multiple of the original sesquilinear form. -/
@[simp]
theorem weightedSesquilinearForm_trivialization (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) (b : B) :
    (Trivial.trivialization B F).weightedSesquilinearForm q φ b = φ b • q := by
  ext v w
  simp

/-- On the trivial bundle with its standard chart, the construction is just the scalar
multiple of the original bilinear form. -/
@[simp]
theorem weightedBilinearForm_trivialization (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) (b : B) :
    (Trivial.trivialization B F).weightedBilinearForm q φ b = φ b • q :=
  weightedSesquilinearForm_trivialization q φ b

variable [RingHomIsometric σ] [VectorBundle 𝕜 F E] [MemTrivializationAtlas e]

local instance : MemTrivializationAtlas (Trivial.trivialization B 𝕜) := ⟨rfl⟩

private def sesquilinearTrivialization :
    Trivialization (F →SL[σ] F →L[𝕜] 𝕜)
      (π (F →SL[σ] F →L[𝕜] 𝕜) (fun b ↦ E b →SL[σ] E b →L[𝕜] 𝕜)) :=
  e.continuousLinearMap σ
    (e.continuousLinearMap (RingHom.id 𝕜) (Trivial.trivialization B 𝕜))

private theorem weightedSesquilinearForm_symm (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜)
    {b : B} (hb : b ∈ e.baseSet) :
    e.weightedSesquilinearForm q φ b =
      (sesquilinearTrivialization (σ := σ) e).symm b (φ b • q) := by
  have hbe : b ∈ (sesquilinearTrivialization (σ := σ) e).baseSet := by
    simpa [sesquilinearTrivialization] using hb
  conv_lhs => rw [← (sesquilinearTrivialization (σ := σ) e).symm_apply_apply_mk hbe
    (e.weightedSesquilinearForm q φ b)]
  congr 1
  ext v w
  simp [sesquilinearTrivialization, Trivialization.continuousLinearMap_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem, hb, weightedSesquilinearForm_apply]

private theorem continuousAt_weightedSesquilinearForm_of_mem
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B}
    (hb : b ∈ e.baseSet) (hφ : ContinuousAt φ b) :
    ContinuousAt
      (fun c ↦ TotalSpace.mk' (F →SL[σ] F →L[𝕜] 𝕜) c (e.weightedSesquilinearForm q φ c)) b := by
  -- Use the normed model's scalar action; the general semilinear-map instance assumes
  -- surjectivity, which is unnecessary here.
  let : IsBoundedSMul 𝕜 (F →SL[σ] F →L[𝕜] 𝕜) :=
    NormedSpace.toIsBoundedSMul (𝕜 := 𝕜) (E := F →SL[σ] F →L[𝕜] 𝕜)
  let : ContinuousSMul 𝕜 (F →SL[σ] F →L[𝕜] 𝕜) :=
    IsBoundedSMul.continuousSMul (α := 𝕜) (β := F →SL[σ] F →L[𝕜] 𝕜)
  let t := sesquilinearTrivialization (σ := σ) e
  have hbt : b ∈ t.baseSet := by simpa [t, sesquilinearTrivialization] using hb
  have h := (t.toOpenPartialHomeomorph.continuousAt_symm (t.mem_target.mpr hbt)).comp
    (continuousAt_id.prodMk (hφ.smul (continuousAt_const (y := q))))
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hb] with c hc
  have hct : c ∈ t.baseSet := by simpa [t, sesquilinearTrivialization] using hc
  rw [weightedSesquilinearForm_symm e q φ hc]
  exact t.mk_symm hct (φ c • q)

/-- A model sesquilinear form, pulled back through a chart and multiplied by a continuous weight
whose topological support lies in the chart, is a continuous section of the iterated hom
bundle. For the identity scalar endomorphism, this is the local weighted-form step in
Hatcher's Proposition 1.2.

Topological support containment ensures the section is locally zero at every point outside
the chart. Containment of only the nonzero locus would not suffice. -/
theorem continuous_weightedSesquilinearForm
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) (hφ : Continuous φ)
    (hs : tsupport φ ⊆ e.baseSet) :
    Continuous
      (fun b ↦ TotalSpace.mk' (F →SL[σ] F →L[𝕜] 𝕜) b (e.weightedSesquilinearForm q φ b)) := by
  refine continuous_iff_continuousAt.2 fun b ↦ ?_
  by_cases hb : b ∈ tsupport φ
  · exact continuousAt_weightedSesquilinearForm_of_mem e q φ (hs hb) hφ.continuousAt
  · apply (continuousAt_zeroSection (F := F →SL[σ] F →L[𝕜] 𝕜)
      (E := fun b ↦ E b →SL[σ] E b →L[𝕜] 𝕜) 𝕜 b).congr_of_eventuallyEq
    filter_upwards [eventually_weightedSesquilinearForm_eq_zero e q φ hb] with c hc
    simp only [zeroSection, hc]

/-- A model bilinear form, pulled back through a chart and multiplied by a continuous weight
whose topological support lies in the chart, is a continuous section of the iterated hom
bundle. This is the local weighted-form step in Hatcher's Proposition 1.2.

Topological support containment ensures the section is locally zero at every point outside
the chart. Containment of only the nonzero locus would not suffice. -/
theorem continuous_weightedBilinearForm
    (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜) (hφ : Continuous φ)
    (hs : tsupport φ ⊆ e.baseSet) :
    Continuous
      (fun b ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) b (e.weightedBilinearForm q φ b)) :=
  e.continuous_weightedSesquilinearForm q φ hφ hs

end Bundle.Trivialization
