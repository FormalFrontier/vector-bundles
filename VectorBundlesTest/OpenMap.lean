/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OpenMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Open bundle maps in global linear charts

The rotating linear functional `(x, y) ↦ cos b * x + sin b * y` is jointly continuous,
surjective on every fibre, and genuinely depends on the base point. Given global linear
charts of existing bundles, it induces an open map on their total spaces. The same chart
transport applies to product projections with an arbitrary topological vector-space
factor and to zero maps with a subsingleton target.
-/

@[expose] public section

noncomputable section

universe u𝕜 uB uF uG uE uE'

namespace Bundle.OpenMap

/-- The linear functional on the real plane whose coefficients rotate with the parameter. -/
def movingPlaneMap (b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  Real.cos b • LinearMap.fst ℝ ℝ ℝ + Real.sin b • LinearMap.snd ℝ ℝ ℝ

@[simp]
theorem movingPlaneMap_apply (b : ℝ) (v : ℝ × ℝ) :
    movingPlaneMap b v = Real.cos b * v.1 + Real.sin b * v.2 := by
  simp [movingPlaneMap, smul_eq_mul]

/-- The moving linear quotient as a map of concrete product spaces. -/
private def movingPlaneTotalMap (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (p.1, movingPlaneMap p.1 p.2)

/-- Continuity here is joint in the base and both plane coordinates. -/
private theorem continuous_movingPlaneTotalMap : Continuous movingPlaneTotalMap := by
  change Continuous (fun p : ℝ × (ℝ × ℝ) ↦
    (p.1, Real.cos p.1 * p.2.1 + Real.sin p.1 * p.2.2))
  exact continuous_fst.prodMk
    (((Real.continuous_cos.comp continuous_fst).mul continuous_snd.fst).add
      ((Real.continuous_sin.comp continuous_fst).mul continuous_snd.snd))

/-- Every fibre functional is onto: the unit vector in its coefficient direction gives
an explicit preimage, using `sin b ^ 2 + cos b ^ 2 = 1`. -/
private theorem surjective_movingPlaneMap (b : ℝ) : Function.Surjective (movingPlaneMap b) := by
  intro t
  refine ⟨(Real.cos b * t, Real.sin b * t), ?_⟩
  rw [movingPlaneMap_apply]
  calc
    Real.cos b * (Real.cos b * t) + Real.sin b * (Real.sin b * t) =
        (Real.cos b ^ 2 + Real.sin b ^ 2) * t := by
          simp only [pow_two, add_mul, mul_assoc]
    _ = t := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]

/- The rotating quotient also exercises the product-family openness theorem directly. -/
example : IsOpenMap movingPlaneTotalMap := by
  exact LinearMap.isOpenMap_prodMap movingPlaneMap
    (continuous_snd.comp continuous_movingPlaneTotalMap) surjective_movingPlaneMap

private theorem movingPlaneMap_zero_apply (v : ℝ × ℝ) : movingPlaneMap 0 v = v.1 := by
  simp

private theorem movingPlaneMap_pi_div_two_apply (v : ℝ × ℝ) :
    movingPlaneMap (Real.pi / 2) v = v.2 := by
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The family is genuinely base-dependent: at `0` it is the first projection,
whereas at `π / 2` it is the second projection. -/
private theorem movingPlaneMap_zero_ne_pi_div_two :
    movingPlaneMap 0 ≠ movingPlaneMap (Real.pi / 2) := by
  intro h
  have hv := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ ↦ f (1, 0)) h
  simp at hv

section GlobalLinearCharts

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {B : Type uB} [TopologicalSpace B]
variable {F : Type uF} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
variable {G : Type uG} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [ContinuousAdd G] [ContinuousSMul 𝕜 G]
variable {E : B → Type uE} {E' : B → Type uE'}
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
variable [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
variable [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]
variable (e : Trivialization F (π F E)) (e' : Trivialization G (π G E'))
variable [e.IsLinear 𝕜] [e'.IsLinear 𝕜]
variable (he : e.baseSet = Set.univ) (he' : e'.baseSet = Set.univ)

/-- Conjugate a family of model linear maps by given global linear charts of existing
bundles. The fibre structures and both total-space topologies remain unchanged. -/
private def linearMapInGlobalCharts (ψ : B → F →ₗ[𝕜] G) (b : B) : E b →ₗ[𝕜] E' b :=
  ((e'.linearEquivAt 𝕜 b (by rw [he']; exact Set.mem_univ b)).symm.toLinearMap).comp
    ((ψ b).comp (e.linearEquivAt 𝕜 b (by rw [he]; exact Set.mem_univ b)).toLinearMap)

omit [ContinuousAdd F] [ContinuousSMul 𝕜 F] [ContinuousAdd G] [ContinuousSMul 𝕜 G]
  [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] in
@[simp]
private theorem linearMapInGlobalCharts_apply (ψ : B → F →ₗ[𝕜] G) (b : B) (v : E b) :
    linearMapInGlobalCharts e e' he he' ψ b v = e'.symm b (ψ b (e ⟨b, v⟩).2) :=
  rfl

omit [ContinuousAdd F] [ContinuousSMul 𝕜 F] [ContinuousAdd G] [ContinuousSMul 𝕜 G]
  [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] in
/-- Joint continuity of the model family transports to the original total spaces by
composition of the given global chart, the model map, and the inverse target chart. -/
private theorem continuous_totalSpaceMap_linearMapInGlobalCharts
    (ψ : B → F →ₗ[𝕜] G)
    (hψ : Continuous (fun p : B × F ↦ (p.1, ψ p.1 p.2))) :
    Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (linearMapInGlobalCharts e e' he he' ψ p.proj p.snd)) := by
  have hc : Continuous e := by
    simpa [e.source_eq, he] using e.continuousOn
  have hi : Continuous (fun z : B × G ↦ TotalSpace.mk' G z.1 (e'.symm z.1 z.2)) := by
    simpa [he'] using e'.continuousOn_symm
  have hEq : (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (linearMapInGlobalCharts e e' he he' ψ p.proj p.snd)) =
      (fun z : B × G ↦ TotalSpace.mk' G z.1 (e'.symm z.1 z.2)) ∘
        (fun z : B × F ↦ (z.1, ψ z.1 z.2)) ∘ e := by
    funext p
    have hp : (e p).1 = p.proj :=
      e.coe_fst (e.mem_source.mpr (by rw [he]; exact Set.mem_univ p.proj))
    change TotalSpace.mk' G p.proj
        (linearMapInGlobalCharts e e' he he' ψ p.proj p.snd) =
      TotalSpace.mk' G (e p).1 (e'.symm (e p).1 (ψ (e p).1 (e p).2))
    rw [hp, linearMapInGlobalCharts_apply]
  rw [hEq]
  exact hi.comp (hψ.comp hc)

omit [ContinuousAdd F] [ContinuousSMul 𝕜 F] [ContinuousAdd G] [ContinuousSMul 𝕜 G]
  [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] in
/-- Fibrewise surjectivity is preserved by conjugation with the given chart equivalences. -/
private theorem surjective_linearMapInGlobalCharts
    (ψ : B → F →ₗ[𝕜] G) (hψ : ∀ b, Function.Surjective (ψ b)) :
    ∀ b, Function.Surjective (linearMapInGlobalCharts e e' he he' ψ b) := by
  intro b
  exact (e'.linearEquivAt 𝕜 b (by rw [he']; exact Set.mem_univ b)).symm.surjective.comp
    ((hψ b).comp (e.linearEquivAt 𝕜 b (by rw [he]; exact Set.mem_univ b)).surjective)

/-- Jointly continuous, fibrewise-surjective model maps induce open total-space maps
through the given global linear charts. -/
private theorem isOpenMap_totalSpaceMap_linearMapInGlobalCharts
    [FiniteDimensional 𝕜 G] [IsModuleTopology 𝕜 G]
    [FiberBundle F E] [FiberBundle G E']
    (hF : ∀ b, (trivializationAt F E b).IsLinear 𝕜)
    (hG : ∀ b, (trivializationAt G E' b).IsLinear 𝕜)
    (ψ : B → F →ₗ[𝕜] G)
    (hψ : Continuous (fun p : B × F ↦ (p.1, ψ p.1 p.2)))
    (hSurj : ∀ b, Function.Surjective (ψ b)) :
    IsOpenMap (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (linearMapInGlobalCharts e e' he he' ψ p.proj p.snd)) := by
  exact Bundle.isOpenMap_totalSpaceMap hF hG
    (linearMapInGlobalCharts e e' he he' ψ)
    (continuous_totalSpaceMap_linearMapInGlobalCharts e e' he he' ψ hψ)
    (surjective_linearMapInGlobalCharts e e' he he' ψ hSurj)

/- A zero map to a subsingleton model induces an open total-space map. -/
example
    [Subsingleton G] [FiniteDimensional 𝕜 G] [IsModuleTopology 𝕜 G]
    [FiberBundle F E] [FiberBundle G E']
    (hF : ∀ b, (trivializationAt F E b).IsLinear 𝕜)
    (hG : ∀ b, (trivializationAt G E' b).IsLinear 𝕜) :
    IsOpenMap (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj
        (linearMapInGlobalCharts e e' he he' (fun _ : B ↦ (0 : F →ₗ[𝕜] G))
          p.proj p.snd)) := by
  apply isOpenMap_totalSpaceMap_linearMapInGlobalCharts e e' he he' hF hG
    (fun _ : B ↦ (0 : F →ₗ[𝕜] G))
  · exact continuous_fst.prodMk continuous_const
  · intro b y
    exact ⟨0, Subsingleton.elim _ _⟩

end GlobalLinearCharts

section MovingPlaneBundles

variable {E : ℝ → Type uE} {E' : ℝ → Type uE'}
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
variable [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
variable [TopologicalSpace (TotalSpace (ℝ × ℝ) E)] [TopologicalSpace (TotalSpace ℝ E')]
variable (e : Trivialization (ℝ × ℝ) (π (ℝ × ℝ) E))
  (e' : Trivialization ℝ (π ℝ E'))
variable [e.IsLinear ℝ] [e'.IsLinear ℝ]
variable (he : e.baseSet = Set.univ) (he' : e'.baseSet = Set.univ)

/- The rotating plane quotient is open on the total spaces of the given bundles. -/
example
    [FiberBundle (ℝ × ℝ) E] [FiberBundle ℝ E']
    (hF : ∀ b, (trivializationAt (ℝ × ℝ) E b).IsLinear ℝ)
    (hG : ∀ b, (trivializationAt ℝ E' b).IsLinear ℝ) :
    IsOpenMap (fun p : TotalSpace (ℝ × ℝ) E ↦
      TotalSpace.mk' ℝ p.proj
        (linearMapInGlobalCharts e e' he he' movingPlaneMap p.proj p.snd)) := by
  exact Bundle.isOpenMap_totalSpaceMap hF hG
    (linearMapInGlobalCharts e e' he he' movingPlaneMap)
    (continuous_totalSpaceMap_linearMapInGlobalCharts e e' he he'
      movingPlaneMap continuous_movingPlaneTotalMap)
    (surjective_linearMapInGlobalCharts e e' he he' movingPlaneMap
      surjective_movingPlaneMap)

end MovingPlaneBundles

section ProductProjectionBundles

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {B : Type uB} [TopologicalSpace B]
variable {F : Type uF} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
variable {E : B → Type uE} {E' : B → Type uE'}
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
variable [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
variable [TopologicalSpace (TotalSpace (F × 𝕜) E)] [TopologicalSpace (TotalSpace 𝕜 E')]
variable (e : Trivialization (F × 𝕜) (π (F × 𝕜) E))
  (e' : Trivialization 𝕜 (π 𝕜 E'))
variable [e.IsLinear 𝕜] [e'.IsLinear 𝕜]
variable (he : e.baseSet = Set.univ) (he' : e'.baseSet = Set.univ)

/- Projection `F × 𝕜 → 𝕜` induces an open total-space map over any base, with an
arbitrary topological vector-space factor `F`. -/
example
    [FiberBundle (F × 𝕜) E] [FiberBundle 𝕜 E']
    (hF : ∀ b, (trivializationAt (F × 𝕜) E b).IsLinear 𝕜)
    (hG : ∀ b, (trivializationAt 𝕜 E' b).IsLinear 𝕜) :
    IsOpenMap (fun p : TotalSpace (F × 𝕜) E ↦
      TotalSpace.mk' 𝕜 p.proj
        (linearMapInGlobalCharts e e' he he'
          (fun _ : B ↦ LinearMap.snd 𝕜 F 𝕜) p.proj p.snd)) := by
  exact isOpenMap_totalSpaceMap_linearMapInGlobalCharts e e' he he' hF hG
    (fun _ : B ↦ LinearMap.snd 𝕜 F 𝕜)
    (continuous_fst.prodMk continuous_snd.snd)
    (fun _ ↦ LinearMap.snd_surjective)

end ProductProjectionBundles

end Bundle.OpenMap
