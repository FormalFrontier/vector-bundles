/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Operator.Basic
public import VectorBundles.Analysis.Normed.Operator.Restrict
public import VectorBundles.Topology.Module.FiniteCoordinates.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact families of continuous semilinear maps

For a finite-dimensional seminormed domain and a proper seminormed target, a closed family
of continuous semilinear maps is compact if and only if every fixed-vector image is
metrically bounded. The scalar field of the domain may be incomplete, and the isometric
scalar homomorphism need not be surjective.

The closed-family criterion uses the topology of uniform convergence on bounded sets.
With its canonical operator seminorm, the space of maps is proper more generally when
the domain contains a dense finite-dimensional submodule. The target may be nonseparated,
so closedness of a family remains an explicit assumption.
-/

@[expose] public section

universe uK uL uA uG

namespace ContinuousLinearMap

/-- A closed family of continuous semilinear maps from a finite-dimensional seminormed
space to a proper seminormed space is compact exactly when each fixed-vector image is
metrically bounded. The scalar fields may be incomplete and the target need not be separated. -/
theorem isCompact_iff_forall_isBounded_image_apply_of_isClosed
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    [pG : ProperSpace G]
    (s : Set (A →SL[σ] G)) (hs : IsClosed s) :
    IsCompact s ↔
      ∀ v : A, Bornology.IsBounded ((fun T : A →SL[σ] G => T v) '' s) := by
  constructor
  · intro h v
    exact (h.image (continuous_eval_const v)).isBounded
  · intro h
    have ht : TotallyBounded s :=
      (totallyBounded_iff_apply_of_finiteDimensionalₛₗ s).2 fun v =>
        (h v).isCompact_closure.totallyBounded.subset subset_closure
    exact ht.isCompact_of_isClosed hs

section ProperOperatorSpace

variable {K : Type uK} [kK : NontriviallyNormedField K]
  {L : Type uL} [kL : NormedField L]
  {σ : K →+* L} [RingHomIsometric σ]
  {A : Type uA} [sA : SeminormedAddCommGroup A]
  [nA : @NormedSpace K A kK.toNormedField sA]
  [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
    sA.toAddCommGroup nA.toModule]
  {G : Type uG} [sG : SeminormedAddCommGroup G]
  [nG : @NormedSpace L G kL sG] [ProperSpace G]

/-- The canonical operator space of continuous semilinear maps from a finite-dimensional
seminormed space to a proper seminormed space is proper. Neither scalar field is required
to be complete, the target need not be separated, and the scalar homomorphism need not
be surjective. -/
theorem properSpace_of_finiteDimensionalₛₗ : ProperSpace (A →SL[σ] G) := by
  refine ⟨fun T₀ r => ?_⟩
  refine (isCompact_iff_forall_isBounded_image_apply_of_isClosed
    (Metric.closedBall T₀ r) Metric.isClosed_closedBall).2 ?_
  intro a
  refine (Metric.isBounded_closedBall (x := T₀ a) (r := r * ‖a‖)).subset ?_
  rintro _ ⟨T, hT, rfl⟩
  have hnorm : ‖T - T₀‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hT
  apply Metric.mem_closedBall.mpr
  calc
    dist (T a) (T₀ a) = ‖(T - T₀) a‖ := by rw [dist_eq_norm]; rfl
    _ ≤ ‖T - T₀‖ * ‖a‖ :=
      (opNorm_le_iff_ofNormedField (f := T - T₀) (norm_nonneg (T - T₀))).1 le_rfl a
    _ ≤ r * ‖a‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg a)

/-- Continuous semilinear maps from a finite-dimensional seminormed space to a proper
seminormed space form a proper space for the canonical operator seminorm. -/
instance (priority := 100) instProperSpaceOfIsometricRingHom : ProperSpace (A →SL[σ] G) :=
  properSpace_of_finiteDimensionalₛₗ

end ProperOperatorSpace

/-- The canonical operator space of continuous semilinear maps to a proper seminormed space
is proper when the domain contains a dense finite-dimensional submodule. Neither scalar field
is required to be complete, the target need not be separated, and the scalar homomorphism
need not be surjective. -/
theorem properSpace_of_dense_finiteDimensionalₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG] [ProperSpace G]
    (P : Submodule K A) [FiniteDimensional K P]
    (hP : Dense (P : Set A)) : ProperSpace (A →SL[σ] G) := by
  have hR : Isometry (fun T : A →SL[σ] G => T.domRestrict P) := by
    let : NontriviallyNormedField L :=
      { toNormedField := kL
        non_trivial := by
          obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
          exact ⟨σ c, by simpa only [RingHomIsometric.norm_map] using hc⟩ }
    exact isometry_domRestrict_of_dense (σ := σ) (G := G) P hP
  let : ProperSpace (P →SL[σ] G) :=
    properSpace_of_finiteDimensionalₛₗ (K := K) (L := L) (σ := σ)
  refine ⟨fun T r => ?_⟩
  have ht := totallyBounded_preimage hR.isUniformInducing
    (isCompact_closedBall (T.domRestrict P) r).totallyBounded
  rw [hR.preimage_closedBall T r] at ht
  exact ht.isCompact_of_isClosed Metric.isClosed_closedBall

end ContinuousLinearMap
