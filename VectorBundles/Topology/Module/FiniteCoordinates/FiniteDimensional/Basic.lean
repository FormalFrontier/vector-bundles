/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates.OperatorNorm
public import VectorBundles.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import VectorBundles.Analysis.Normed.Module.Completion
public import VectorBundles.Analysis.Normed.Operator.Restrict
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional seminormed domains and evaluation

A finite-dimensional seminormed domain admits a finite-evaluation bound for operator norms,
uniformly over all seminormed targets. The scalar field may be incomplete, and the domain
and target need not be separated or complete. The sample vectors and constant depend only
on the given domain, without requiring its algebraic coordinates to be continuous.
Consequently, continuity of an operator-valued family in the given operator-norm topology
is equivalent to continuity of every fixed-vector evaluation.

The canonical identity to the pointwise-convergence copy is a continuous linear equivalence,
so convergence along any filter is likewise equivalent to convergence of every fixed-vector
evaluation. The equivalence is also a uniform embedding for the inherited additive uniformities.
Together with Mathlib's uniform embedding of the pointwise-convergence space into the full
function space, this identifies total boundedness for the operator-norm uniformity with total
boundedness of every fixed-vector image.

The same criterion holds for continuous semilinear maps along an isometric homomorphism
of normed fields. More generally, the ambient domain can have infinite algebraic dimension:
it is enough to test evaluations on a set whose original scalar span is finite-dimensional
and dense. Uniform convergence on any bounded family whose union algebraically spans
such a controlling test set also gives the operator-norm topology, even if the whole
union has infinite-dimensional span. The identity with this family topology is linear
over the original target field; its action on the target is unchanged. Dense span need
not be algebraically the whole domain, and restriction to a dense subspace need not be
injective when the target is not separated. Total boundedness is likewise detected by
all evaluations on a dense finite-dimensional submodule, with an arbitrary seminormed target.

## References

The finite-evaluation estimate follows Formal Frontier Agents, *Operator-norm continuity over
an incomplete scalar field*, using coefficient bounds over the completed field before
establishing closedness of finite spans. The proof uses Mathlib's completion and
continuous-linear-map APIs.
-/

@[expose] public section

universe uK uF uι

/-!
## Coefficient bounds over a complete field

The following argument proves coefficient bounds before using closedness of a finite span.
It follows the simultaneous bounds-and-completeness induction in Formal Frontier Agents,
*Operator-norm continuity over an incomplete scalar field*, “Finite spans over a complete field:
bounds before closedness”. In particular, no independence assertion survives a change of
scalar field without a new proof.
-/

namespace FiniteDimensional

open scoped BigOperators NNReal

section CompleteField

variable {F : Type uK} [NontriviallyNormedField F]
variable {E : Type uF} [NormedAddCommGroup E] [NormedSpace F E]

/-- Finite synthesis uses the given action on the target. -/
private noncomputable def finiteSynthesis {ι : Type uι} [Fintype ι]
    (b : ι → E) : (ι → F) →L[F] E :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton F (b i)).comp
    (ContinuousLinearMap.proj (R := F) (φ := fun _ : ι => F) i)

private theorem finiteSynthesis_apply {ι : Type uι} [Fintype ι]
    (b : ι → E) (c : ι → F) : finiteSynthesis b c = ∑ i, c i • b i := by
  classical
  simp only [finiteSynthesis, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply]

/-- A uniform coefficient bound makes finite synthesis antilipschitz. -/
private theorem antilipschitz_finiteSynthesis {ι : Type uι} [Fintype ι]
    (b : ι → E) (C : ℝ≥0)
    (hC : ∀ (c : ι → F) i, ‖c i‖ ≤ (C : ℝ) * ‖finiteSynthesis b c‖) :
    AntilipschitzWith C (finiteSynthesis (F := F) b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro c d
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact (pi_norm_le_iff_of_nonneg
    (mul_nonneg C.coe_nonneg (norm_nonneg _))).mpr (hC (c - d))

/-- The induction proves bounds first; completeness of the finite scalar product then makes
its image complete and closed, even when the ambient space is incomplete. -/
private theorem exists_coefficient_bound [CompleteSpace F] {ι : Type uι} [Fintype ι]
    (b : ι → E) (hb : LinearIndependent F b) :
    ∃ C : ℝ≥0, ∀ (c : ι → F) i,
      ‖c i‖ ≤ (C : ℝ) * ‖finiteSynthesis b c‖ := by
  classical
  let P := fun (ι : Type uι) [Fintype ι] =>
    ∀ (b : ι → E), LinearIndependent F b →
      ∃ C : ℝ≥0, ∀ (c : ι → F) i,
        ‖c i‖ ≤ (C : ℝ) * ‖finiteSynthesis b c‖
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι b hb
  · intro α β _ e ih b hb
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨C, hC⟩ := ih (b ∘ e) (hb.comp e e.injective)
    refine ⟨C, ?_⟩
    intro c i
    have hsum : (∑ j : α, c (e j) • b (e j)) = ∑ j : β, c j • b j :=
      e.sum_comp (fun j => c j • b j)
    simpa only [finiteSynthesis_apply, Function.comp_apply, Equiv.apply_symm_apply, hsum]
      using hC (c ∘ e) (e.symm i)
  · intro b _
    exact ⟨0, fun _ i => PEmpty.elim i⟩
  · intro α _ ih b hb
    obtain ⟨hb', hnot⟩ := linearIndependent_option.mp hb
    let b' : α → E := b ∘ some
    obtain ⟨C, hC⟩ := ih b' hb'
    let S := finiteSynthesis (F := F) b'
    have hclosed : IsClosed (Set.range S) :=
      (antilipschitz_finiteSynthesis b' C hC).isClosed_range S.uniformContinuous
    have hbnot : b none ∉ Set.range S := by
      rintro ⟨c, hc⟩
      apply hnot
      rw [← hc]
      change finiteSynthesis b' c ∈ Submodule.span F (Set.range b')
      rw [finiteSynthesis_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp hclosed.isOpen_compl (b none) hbnot
    have hsep (z : E) (hz : z ∈ Set.range S) : δ ≤ ‖b none - z‖ := by
      apply le_of_not_gt
      intro hzδ
      have hzb : z ∈ Metric.ball (b none) δ := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hzδ
      exact hball hzb hz
    let r : ℝ≥0 := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
    let D : ℝ≥0 := max r (C * (1 + r * ‖b none‖₊))
    refine ⟨D, ?_⟩
    intro c i
    let q := c none
    let c' : α → F := fun j => c (some j)
    let x := finiteSynthesis b c
    have hx : x = q • b none + S c' := by
      simp only [x, finiteSynthesis_apply, Fintype.sum_option, S, b', c', q,
        Function.comp_apply]
    have hqbound : ‖q‖ ≤ (r : ℝ) * ‖x‖ := by
      by_cases hq : q = 0
      · rw [hq, norm_zero]
        exact mul_nonneg r.coe_nonneg (norm_nonneg x)
      have hd := hsep (-(q⁻¹) • S c')
        ⟨-(q⁻¹) • c', by simp only [map_smul]⟩
      have heq : q • (b none - -(q⁻¹) • S c') = x := by
        rw [smul_sub, smul_smul]
        simp only [mul_neg, mul_inv_cancel₀ hq, neg_one_smul, sub_neg_eq_add]
        exact hx.symm
      have hmul : ‖q‖ * δ ≤ ‖x‖ := by
        calc
          ‖q‖ * δ ≤ ‖q‖ * ‖b none - -(q⁻¹) • S c'‖ :=
            mul_le_mul_of_nonneg_left hd (norm_nonneg q)
          _ = ‖x‖ := by rw [← norm_smul, heq]
      change ‖q‖ ≤ δ⁻¹ * ‖x‖
      simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hδ).2 hmul
    have hres : ‖S c'‖ ≤ (1 + (r : ℝ) * ‖b none‖) * ‖x‖ := by
      calc
        ‖S c'‖ = ‖x - q • b none‖ := by rw [hx]; congr 1; abel
        _ ≤ ‖x‖ + ‖q • b none‖ := norm_sub_le _ _
        _ = ‖x‖ + ‖q‖ * ‖b none‖ := by rw [norm_smul]
        _ ≤ ‖x‖ + ((r : ℝ) * ‖x‖) * ‖b none‖ :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hqbound (norm_nonneg (b none)))
        _ = (1 + (r : ℝ) * ‖b none‖) * ‖x‖ := by ring
    cases i with
    | none =>
      exact hqbound.trans (mul_le_mul_of_nonneg_right
        (show (r : ℝ) ≤ (D : ℝ) from (show r ≤ D from le_max_left _ _))
        (norm_nonneg x))
    | some i =>
      have hi : ‖c' i‖ ≤ ((C * (1 + r * ‖b none‖₊) : ℝ≥0) : ℝ) * ‖x‖ := by
        change ‖c' i‖ ≤ (C : ℝ) * (1 + (r : ℝ) * ‖b none‖) * ‖x‖
        calc
          ‖c' i‖ ≤ (C : ℝ) * ‖S c'‖ := hC c' i
          _ ≤ (C : ℝ) * ((1 + (r : ℝ) * ‖b none‖) * ‖x‖) :=
            mul_le_mul_of_nonneg_left hres C.coe_nonneg
          _ = _ := (mul_assoc _ _ _).symm
      exact hi.trans (mul_le_mul_of_nonneg_right
        (show ((C * (1 + r * ‖b none‖₊) : ℝ≥0) : ℝ) ≤ (D : ℝ)
          from (show C * (1 + r * ‖b none‖₊) ≤ D from le_max_right _ _)) (norm_nonneg x))

private theorem range_finiteSynthesis {ι : Type uι} [Fintype ι] (b : ι → E) :
    (finiteSynthesis b).toLinearMap.range = Submodule.span F (Set.range b) := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    change finiteSynthesis b c ∈ Submodule.span F (Set.range b)
    rw [finiteSynthesis_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [finiteSynthesis_apply, Pi.single_apply]⟩

private theorem isClosed_span_range_of_linearIndependent [CompleteSpace F]
    {ι : Type uι} [Finite ι] (b : ι → E) (hb : LinearIndependent F b) :
    IsClosed (Submodule.span F (Set.range b) : Set E) := by
  let := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := exists_coefficient_bound (F := F) b hb
  rw [← range_finiteSynthesis (F := F) b]
  exact (antilipschitz_finiteSynthesis (F := F) b C hC).isClosed_range
    (finiteSynthesis (F := F) b).uniformContinuous

end CompleteField

end FiniteDimensional

universe uA uG uX

namespace FiniteDimensional

open UniformSpace
open UniformSpace.Completion
open scoped BigOperators NNReal

/-- A finite-dimensional seminormed domain has finitely many original sample vectors that
control the operator norm, uniformly over all seminormed targets and all continuous linear
maps. The original scalar field need not be complete, and the original spaces need not be
complete or separated. The finite set and its nonnegative constant depend only on the given domain.

The proof completes the given scalar actions, selects an independent subfamily only after
completion, and uses the complete-field coefficient bounds proved above. It follows Formal
Frontier Agents, *Operator-norm continuity over an incomplete scalar field*, “A finite sampling
list selected from the original domain” and “Proof of the uniform finite-evaluation estimate”. -/
theorem exists_finset_opNorm_le_sum (K : Type uK) [kK : NontriviallyNormedField K]
    (A : Type uA) [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule] :
    ∃ s : Finset A, ∃ C : ℝ≥0,
      ∀ (G : Type uG) (sG : SeminormedAddCommGroup G)
        (nG : @NormedSpace K G kK.toNormedField sG)
        (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
          A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          sA.toAddCommGroup.toAddCommMonoid
          G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule),
        @Norm.norm _ (@ContinuousLinearMap.hasOpNorm K K A G
          sA sG kK kK nA nG (RingHom.id K)) T ≤
          (C : ℝ) * ∑ v ∈ s, @Norm.norm G sG.toNorm (T v) := by
  classical
  let := nontriviallyNormedField K
  let := normedSpaceOverCompletion K A
  let a₀ := Module.finBasis K A
  let b₀ := fun i => (a₀ i : Completion A)
  obtain ⟨ι, j, hj, hspan, hli⟩ :=
    exists_linearIndependent' (K := Completion K) b₀
  let : Finite ι := Finite.of_injective j hj
  let := Fintype.ofFinite ι
  let v : ι → A := fun i => a₀ (j i)
  let b : ι → Completion A := fun i => (v i : Completion A)
  have hb : LinearIndependent (Completion K) b := hli
  obtain ⟨C, hC⟩ := exists_coefficient_bound b hb
  let S := Submodule.span (Completion K) (Set.range b)
  have hclosed : IsClosed (S : Set (Completion A)) :=
    isClosed_span_range_of_linearIndependent b hb
  have hmem (i : Fin (Module.finrank K A)) : (a₀ i : Completion A) ∈ S := by
    change (a₀ i : Completion A) ∈
      Submodule.span (Completion K) (Set.range (b₀ ∘ j))
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcoe (a : A) : (a : Completion A) ∈ S := by
    let η : A →ₗ[K] Completion A :=
      (toComplₗᵢ : A →ₗᵢ[K] Completion A).toLinearMap
    have hη : η a ∈ S := by
      rw [← a₀.sum_repr a, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [map_smul]
      have hi := S.smul_mem ((a₀.repr a i : K) : Completion K) (hmem i)
      have hsmul :=
        (UniformSpace.Completion.normedSpaceOverCompletion_smul K A
          ((a₀.repr a i : K) : Completion K) (a₀ i : Completion A)).trans
          (UniformSpace.Completion.smulOverCompletion_coe K A
            (a₀.repr a i) (a₀ i : Completion A))
      exact hsmul ▸ hi
    exact hη
  have honto : Function.Surjective (finiteSynthesis (F := Completion K) b) := by
    intro z
    have hz : z ∈ S := Completion.induction_on z hclosed hcoe
    have hzr : z ∈ (finiteSynthesis (F := Completion K) b).toLinearMap.range := by
      rw [range_finiteSynthesis]
      exact hz
    exact hzr
  have hv : Function.Injective v := by
    intro i i' h
    apply hb.injective
    exact congrArg (fun a : A => (a : Completion A)) h
  let s : Finset A := Finset.univ.image v
  refine ⟨s, C, ?_⟩
  intro G sG nG T
  let := sG
  let := nG
  let := normedSpaceOverCompletion K G
  let U := T.completionOverCompletion
  have hsum : (∑ i, ‖T (v i)‖) = ∑ a ∈ s, ‖T a‖ := by
    simpa only [s] using
      (Finset.sum_image (s := (Finset.univ : Finset ι)) (g := v)
        (f := fun a : A => ‖T a‖) (fun i _ i' _ h => hv h)).symm
  have hU : ‖U‖ ≤ (C : ℝ) * ∑ i, ‖T (v i)‖ := by
    apply U.opNorm_le_bound
      (mul_nonneg C.coe_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    intro z
    obtain ⟨c, rfl⟩ := honto z
    calc
      ‖U (finiteSynthesis b c)‖ = ‖∑ i, c i • U (b i)‖ := by
        rw [finiteSynthesis_apply, map_sum]
        simp only [map_smul]
      _ ≤ ∑ i, ‖c i • U (b i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖T (v i)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul]
        congr 1
        exact (congrArg norm (T.completionOverCompletion_apply_coe (v i))).trans
          (norm_coe (T (v i)))
      _ ≤ ∑ i, ((C : ℝ) * ‖finiteSynthesis b c‖) * ‖T (v i)‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hC c i) (norm_nonneg _)
      _ = ((C : ℝ) * ∑ i, ‖T (v i)‖) * ‖finiteSynthesis b c‖ := by
        rw [← Finset.mul_sum]
        ring
  calc
    ‖T‖ = ‖U‖ := (ContinuousLinearMap.norm_completionOverCompletion T).symm
    _ ≤ (C : ℝ) * ∑ i, ‖T (v i)‖ := hU
    _ = (C : ℝ) * ∑ a ∈ s, ‖T a‖ := congrArg (fun r : ℝ => (C : ℝ) * r) hsum

end FiniteDimensional

namespace ContinuousLinearMap

/-- For a finite-dimensional seminormed domain, an operator-valued family is continuous
for the operator-norm topology exactly when every fixed-vector evaluation is continuous.
The scalar field need not be complete, and the original spaces need not be complete
or separated. -/
theorem continuous_iff_apply_of_finiteDimensional
    {K : Type uK} [kK : NontriviallyNormedField K]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace K G kK.toNormedField sG]
    {X : Type uX} [tX : TopologicalSpace X]
    (L : X → A →L[K] G) :
    Continuous L ↔ ∀ v : A, Continuous (fun x : X => L x v) := by
  constructor
  · intro hL v
    exact (ContinuousLinearMap.apply K G v).continuous.comp hL
  · intro hL
    obtain ⟨s, C, hbound⟩ :=
      FiniteDimensional.exists_finset_opNorm_le_sum.{uK, uA, uG}
        K A (kK := kK) (sA := sA) (nA := nA) (hA := hA)
    exact (continuous_iff_apply_finset_of_opNorm_le s C (hbound G sG nG) L).2
      (fun v _ => hL v)

end ContinuousLinearMap

universe uL

namespace ContinuousLinearMap

section SemilinearRestriction

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {L : Type uL} [kL : NontriviallyNormedField L]
variable [NormedAlgebra K L] [RingHomIsometric (algebraMap K L)]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace L G kL.toNormedField sG]

/-- The same-function identification preserves the operator-norm topology. -/
private def semilinearRestrictHomeomorph :
    let S := @ContinuousLinearMap K L _ _ (algebraMap K L)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule
    letI : NormedSpace K G := NormedSpace.restrictScalars K L G
    S ≃ₜ (A →L[K] G) := by
  -- Form the semilinear source with its original data before restricting the right-hand action.
  let S := @ContinuousLinearMap K L _ _ (algebraMap K L)
    A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    sA.toAddCommGroup.toAddCommMonoid
    G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule
  letI : NormedSpace K G := NormedSpace.restrictScalars K L G
  let e : S ≃+ (A →L[K] G) :=
    { toFun T :=
        { toFun := fun a => T a
          map_add' := T.map_add
          map_smul' := T.map_smulₛₗ
          cont := T.continuous }
      invFun T :=
        { toFun := fun a => T a
          map_add' := T.map_add
          map_smul' := T.map_smul
          cont := T.continuous }
      left_inv T := by ext a; rfl
      right_inv T := by ext a; rfl
      map_add' T U := by ext a; rfl }
  -- The operator norms are infima of exactly the same set of bounds.
  have he (T : S) : ‖e T‖ = ‖T‖ := rfl
  have he' (T : A →L[K] G) : ‖e.symm T‖ = ‖T‖ := rfl
  exact
    { toEquiv := e.toEquiv
      continuous_toFun := (AddMonoidHomClass.isometry_of_norm e he).continuous
      continuous_invFun := (AddMonoidHomClass.isometry_of_norm e.symm he').continuous }

private theorem semilinearRestrictHomeomorph_apply (T : A →SL[algebraMap K L] G) (a : A) :
    semilinearRestrictHomeomorph T a = T a := rfl

end SemilinearRestriction

/-- For an isometric scalar homomorphism and a finite-dimensional seminormed domain,
continuity of a family of continuous semilinear maps is equivalent to continuity of every
fixed-vector evaluation. The target retains its given scalar action. No completeness of the
scalar fields or spaces, and no separation of the seminormed spaces, is assumed.

The proof reuses `continuous_iff_apply_of_finiteDimensional` through same-function,
norm-preserving restriction of the target scalars. -/
theorem continuous_iff_apply_of_finiteDimensionalₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    {X : Type uX} [tX : TopologicalSpace X]
    (f : X → A →SL[σ] G) :
    Continuous f ↔ ∀ a : A, Continuous (fun x : X => f x a) := by
  let : NontriviallyNormedField L :=
    { toNormedField := kL
      non_trivial := by
        obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
        exact ⟨σ c, by simpa only [RingHomIsometric.norm_map] using hc⟩ }
  let : NormedAlgebra K L :=
    { toAlgebra := σ.toAlgebra
      norm_smul_le := fun c x => by
        change ‖σ c * x‖ ≤ ‖c‖ * ‖x‖
        rw [norm_mul, RingHomIsometric.norm_map] }
  have : RingHomIsometric (algebraMap K L) :=
    ⟨fun {c} => norm_algebraMap' L c⟩
  let : NormedSpace K G := NormedSpace.restrictScalars K L G
  let e := semilinearRestrictHomeomorph (K := K) (L := L) (nA := nA) (nG := nG)
  constructor
  · intro hf a
    have h := (continuous_iff_apply_of_finiteDimensional
      (fun x : X => e (f x))).1 (e.continuous.comp hf) a
    simpa only [e, semilinearRestrictHomeomorph_apply] using h
  · intro hf
    have h : Continuous (fun x : X => e (f x)) :=
      (continuous_iff_apply_of_finiteDimensional (fun x : X => e (f x))).2
        (fun a => by simpa only [e, semilinearRestrictHomeomorph_apply] using hf a)
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using e.symm.continuous.comp h

/-- Continuity of fixed-vector evaluations propagates algebraically to the span. -/
private theorem continuous_apply_of_mem_span
    {K : Type uK} [Semiring K] {L : Type uL} [Semiring L]
    {σ : K →+* L}
    {A : Type uA} [AddCommMonoid A] [Module K A] [TopologicalSpace A]
    {G : Type uG} [AddCommMonoid G] [Module L G] [TopologicalSpace G]
    [ContinuousAdd G] [ContinuousConstSMul L G]
    {X : Type uX} [TopologicalSpace X]
    (f : X → A →SL[σ] G) {D : Set A}
    (hD : ∀ a ∈ D, Continuous (fun x : X => f x a))
    {a : A} (ha : a ∈ Submodule.span K D) :
    Continuous (fun x : X => f x a) := by
  let P : Submodule K A :=
    { carrier := {a | Continuous (fun x : X => f x a)}
      zero_mem' := by
        simpa only [Set.mem_ofPred_eq, map_zero] using
          (continuous_const : Continuous (fun _ : X => (0 : G)))
      add_mem' := by
        intro a b ha hb
        change Continuous (fun x : X => f x (a + b))
        have hfun : ((fun x : X => f x a) + fun x => f x b) =
            (fun x : X => f x (a + b)) := by
          funext x
          exact (map_add (f x) a b).symm
        exact hfun ▸ ha.add hb
      smul_mem' := by
        intro c a ha
        change Continuous (fun x : X => f x (c • a))
        have hfun : (σ c • fun x : X => f x a) =
            (fun x : X => f x (c • a)) := by
          funext x
          exact (map_smulₛₗ (f x) c a).symm
        exact hfun ▸ ha.const_smul (σ c) }
  exact (Submodule.span_le.mpr (show D ⊆ P from hD)) ha

/-- Continuity of a family of continuous semilinear maps can be tested on a set whose
scalar span is finite-dimensional and dense in the original seminormed domain. The
ambient domain need not be finite-dimensional, and the testing set need not be bounded.
The fields and spaces may be incomplete, the spaces need not be separated, and the
target retains its original scalar action.

The proof applies the independent global evaluation criterion to the inherited
submodule spanned by the tests, then reflects continuity through dense restriction. -/
theorem continuous_iff_apply_of_dense_spanₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    {X : Type uX} [tX : TopologicalSpace X]
    (D : Set A)
    [hD : FiniteDimensional K (Submodule.span K D)]
    (hdense : Dense (Submodule.span K D : Set A))
    (f : X → A →SL[σ] G) :
    Continuous f ↔ ∀ a ∈ D, Continuous (fun x : X => f x a) := by
  constructor
  · intro hf a _
    exact hf.eval_const a
  · intro hf
    -- Test on the inherited span, then reflect continuity through dense restriction.
    have hr : Continuous (fun x : X => (f x).domRestrict (Submodule.span K D)) := by
      apply (continuous_iff_apply_of_finiteDimensionalₛₗ _).2
      intro a
      change Continuous (fun x : X => f x (a : A))
      exact continuous_apply_of_mem_span f hf a.property
    exact (isUniformInducing_domRestrict_of_dense (σ := σ) (G := G)
      (Submodule.span K D) hdense).isInducing.continuous_iff.mpr hr

end ContinuousLinearMap

namespace UniformConvergenceCLM

/-- Continuous evaluations extend from a family union to its algebraic span. -/
private theorem continuous_eval_of_mem_span
    {K : Type uK} [NormedField K] {L : Type uL} [NormedField L]
    {σ : K →+* L}
    {A : Type uA} [AddCommGroup A] [Module K A] [TopologicalSpace A]
    {G : Type uG} [AddCommGroup G] [Module L G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul L G]
    (𝔖 : Set (Set A)) {a : A} (ha : a ∈ Submodule.span K (⋃₀ 𝔖)) :
    Continuous (fun T : UniformConvergenceCLM σ G 𝔖 => T a) := by
  apply ContinuousLinearMap.continuous_apply_of_mem_span
    (fun T : UniformConvergenceCLM σ G 𝔖 => T) (a := a) (D := ⋃₀ 𝔖) ?_ ha
  intro a ha
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  exact (UniformOnFun.uniformContinuous_eval_of_mem_sUnion G 𝔖 ha).continuous.comp
    (UniformConvergenceCLM.isEmbedding_coeFn σ G 𝔖).continuous

end UniformConvergenceCLM

namespace ContinuousLinearEquiv

/-- Uniform convergence on a bounded family agrees with the operator-norm topology when
its union algebraically spans a set of tests with finite-dimensional dense scalar span.
Only the controlling test span is required to be finite-dimensional; the ambient domain
and the whole family union may have infinite-dimensional span. The tests need not be bounded.
The underlying equivalence is Mathlib's canonical identity on the same full maps, linear
over the original target field. No completeness, separation or surjectivity of the scalar
homomorphism is assumed. -/
def toUniformConvergenceCLMOfDenseTestSpan
    (K : Type uK) [kK : NontriviallyNormedField K]
    (L : Type uL) [kL : NormedField L]
    (σ : K →+* L) [RingHomIsometric σ]
    (A : Type uA) [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    (G : Type uG) [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (𝔖 : Set (Set A)) (D : Set A)
    [hD : FiniteDimensional K (Submodule.span K D)]
    (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
    (hcontrol : D ⊆ Submodule.span K (⋃₀ 𝔖))
    (hdense : Dense (Submodule.span K D : Set A)) :
    (A →SL[σ] G) ≃L[L] UniformConvergenceCLM σ G 𝔖 :=
  { toLinearEquiv := ContinuousLinearMap.toUniformConvergenceCLM σ G 𝔖
    continuous_toFun := ContinuousLinearMap.toUniformConvergenceCLM_continuous σ G 𝔖
      (fun s hs => NormedSpace.isVonNBounded_of_isBounded K (hbounded s hs))
    continuous_invFun := by
      apply (ContinuousLinearMap.continuous_iff_apply_of_dense_spanₛₗ D hdense
        ((ContinuousLinearMap.toUniformConvergenceCLM σ G 𝔖).symm :
          UniformConvergenceCLM σ G 𝔖 → A →SL[σ] G)).2
      intro a ha
      simpa only [ContinuousLinearMap.toUniformConvergenceCLM_symm_apply] using
        UniformConvergenceCLM.continuous_eval_of_mem_span (σ := σ) 𝔖 (hcontrol ha) }

section DenseTestUniformConvergence

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {L : Type uL} [kL : NormedField L]
variable {σ : K →+* L} [RingHomIsometric σ]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace L G kL sG]
variable (𝔖 : Set (Set A)) (D : Set A)
variable [hD : FiniteDimensional K (Submodule.span K D)]
variable (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
variable (hcontrol : D ⊆ Submodule.span K (⋃₀ 𝔖))
variable (hdense : Dense (Submodule.span K D : Set A))

/-- The dense-test-span equivalence preserves every original fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseTestSpan_apply (T : A →SL[σ] G) (v : A) :
    toUniformConvergenceCLMOfDenseTestSpan K L σ A G 𝔖 D hbounded hcontrol hdense T v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_apply

/-- The inverse dense-test-span equivalence preserves every original fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseTestSpan_symm_apply
    (T : UniformConvergenceCLM σ G 𝔖) (v : A) :
    (toUniformConvergenceCLMOfDenseTestSpan K L σ A G 𝔖 D hbounded hcontrol hdense).symm T v =
      T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_symm_apply

/-- Forgetting continuity gives the canonical same-function linear equivalence. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseTestSpan_toLinearEquiv :
    (toUniformConvergenceCLMOfDenseTestSpan K L σ A G 𝔖 D hbounded hcontrol hdense).toLinearEquiv =
      ContinuousLinearMap.toUniformConvergenceCLM σ G 𝔖 := rfl

end DenseTestUniformConvergence

/-- Uniform convergence on a bounded family whose union has finite-dimensional dense
scalar span agrees with the operator-norm topology on continuous semilinear maps. The
ambient seminormed domain need not be finite-dimensional. The underlying equivalence
is Mathlib's canonical identity on the same full maps, linear over the original target
field. No completeness, separation or surjectivity of the scalar homomorphism is assumed. -/
def toUniformConvergenceCLMOfDenseSpan
    (K : Type uK) [kK : NontriviallyNormedField K]
    (L : Type uL) [kL : NormedField L]
    (σ : K →+* L) [RingHomIsometric σ]
    (A : Type uA) [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    (G : Type uG) [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (𝔖 : Set (Set A))
    [h𝔖 : FiniteDimensional K (Submodule.span K (⋃₀ 𝔖))]
    (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
    (hdense : Dense (Submodule.span K (⋃₀ 𝔖) : Set A)) :
    (A →SL[σ] G) ≃L[L] UniformConvergenceCLM σ G 𝔖 :=
  toUniformConvergenceCLMOfDenseTestSpan K L σ A G 𝔖 (⋃₀ 𝔖) hbounded
    (fun _ ha => Submodule.subset_span ha) hdense

section DenseUniformConvergence

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {L : Type uL} [kL : NormedField L]
variable {σ : K →+* L} [RingHomIsometric σ]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace L G kL sG]
variable (𝔖 : Set (Set A))
variable [h𝔖 : FiniteDimensional K (Submodule.span K (⋃₀ 𝔖))]
variable (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
variable (hdense : Dense (Submodule.span K (⋃₀ 𝔖) : Set A))

/-- The dense-span equivalence preserves every original fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseSpan_apply (T : A →SL[σ] G) (v : A) :
    toUniformConvergenceCLMOfDenseSpan K L σ A G 𝔖 hbounded hdense T v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_apply

/-- The inverse dense-span equivalence preserves every original fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseSpan_symm_apply
    (T : UniformConvergenceCLM σ G 𝔖) (v : A) :
    (toUniformConvergenceCLMOfDenseSpan K L σ A G 𝔖 hbounded hdense).symm T v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_symm_apply

/-- Forgetting continuity gives the canonical same-function linear equivalence. -/
@[simp]
theorem toUniformConvergenceCLMOfDenseSpan_toLinearEquiv :
    (toUniformConvergenceCLMOfDenseSpan K L σ A G 𝔖 hbounded hdense).toLinearEquiv =
      ContinuousLinearMap.toUniformConvergenceCLM σ G 𝔖 := rfl

end DenseUniformConvergence

/-- Uniform convergence on a bounded family whose union algebraically spans a
finite-dimensional seminormed domain agrees with the operator-norm topology on continuous
semilinear maps. The underlying linear equivalence is Mathlib's identity, over the target
field. In particular this applies to bounded covers and to a family containing a finite
algebraic basis. No completeness, separation or surjectivity of the scalar homomorphism
is assumed. -/
def toUniformConvergenceCLMOfFiniteDimensional
    (K : Type uK) [kK : NontriviallyNormedField K]
    (L : Type uL) [kL : NormedField L]
    (σ : K →+* L) [RingHomIsometric σ]
    (A : Type uA) [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    (G : Type uG) [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (𝔖 : Set (Set A))
    (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
    (hspan : Submodule.span K (⋃₀ 𝔖) = ⊤) :
    (A →SL[σ] G) ≃L[L] UniformConvergenceCLM σ G 𝔖 :=
  toUniformConvergenceCLMOfDenseSpan K L σ A G 𝔖 hbounded
    (by
      rw [hspan]
      change Dense (Set.univ : Set A)
      exact dense_univ)

section UniformConvergence

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {L : Type uL} [kL : NormedField L]
variable {σ : K →+* L} [RingHomIsometric σ]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
  sA.toAddCommGroup nA.toModule]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace L G kL sG]
variable (𝔖 : Set (Set A)) (hbounded : ∀ s ∈ 𝔖, Bornology.IsBounded s)
variable (hspan : Submodule.span K (⋃₀ 𝔖) = ⊤)

/-- The family-topology equivalence preserves each fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfFiniteDimensional_apply (T : A →SL[σ] G) (v : A) :
    toUniformConvergenceCLMOfFiniteDimensional K L σ A G 𝔖 hbounded hspan T v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_apply

/-- The inverse family-topology equivalence preserves each fixed-vector evaluation. -/
@[simp]
theorem toUniformConvergenceCLMOfFiniteDimensional_symm_apply
    (T : UniformConvergenceCLM σ G 𝔖) (v : A) :
    (toUniformConvergenceCLMOfFiniteDimensional K L σ A G 𝔖 hbounded hspan).symm T v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_symm_apply

/-- Forgetting continuity gives Mathlib's same-function linear equivalence. -/
theorem toUniformConvergenceCLMOfFiniteDimensional_toLinearEquiv :
    (toUniformConvergenceCLMOfFiniteDimensional K L σ A G 𝔖 hbounded hspan).toLinearEquiv =
      ContinuousLinearMap.toUniformConvergenceCLM σ G 𝔖 := rfl

end UniformConvergence

end ContinuousLinearEquiv

open Filter
open scoped Topology

namespace ContinuousLinearEquiv

/-- For a finite-dimensional seminormed domain, the identity identifies the
given operator-norm topology with the pointwise-convergence topology on
continuous linear maps. The scalar field and both spaces may be incomplete,
and the spaces need not be separated. -/
def toPointwiseConvergenceCLMOfFiniteDimensional
    (K : Type uK) [kK : NontriviallyNormedField K]
    (A : Type uA) [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    (G : Type uG) [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace K G kK.toNormedField sG] :
    (A →L[K] G) ≃L[K] (A →Lₚₜ[K] G) := by
  have hcover : ⋃₀ {s : Set A | Finite s} = Set.univ := by
    ext a
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_sUnion.mpr
        ⟨{a}, Set.finite_coe_iff.mpr (Set.finite_singleton a), by simp⟩
  exact toUniformConvergenceCLMOfFiniteDimensional K K (RingHom.id K) A G
    {s : Set A | Finite s}
    (fun s hs => (Set.finite_coe_iff.mp hs).isBounded)
    (by rw [hcover, Submodule.span_univ])

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
  sA.toAddCommGroup nA.toModule]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace K G kK.toNormedField sG]

/-- The equivalence preserves each original fixed-vector evaluation. -/
@[simp]
theorem toPointwiseConvergenceCLMOfFiniteDimensional_apply
    (T : A →L[K] G) (v : A) :
    toPointwiseConvergenceCLMOfFiniteDimensional K A G T v = T v := by
  exact ContinuousLinearMap.toUniformConvergenceCLM_apply
    (σ := RingHom.id K) (F := G) (𝔖 := {s : Set A | Finite s})

/-- The inverse equivalence preserves each original fixed-vector evaluation. -/
@[simp]
theorem toPointwiseConvergenceCLMOfFiniteDimensional_symm_apply
    (T : A →Lₚₜ[K] G) (v : A) :
    (toPointwiseConvergenceCLMOfFiniteDimensional K A G).symm T v = T v := by
  exact ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
    (σ := RingHom.id K) (F := G) (𝔖 := {s : Set A | Finite s})

/-- Forgetting the inverse recovers Mathlib's canonical map to the
pointwise-convergence space on the same continuous linear maps. -/
theorem toPointwiseConvergenceCLMOfFiniteDimensional_toContinuousLinearMap :
    (toPointwiseConvergenceCLMOfFiniteDimensional K A G).toContinuousLinearMap =
      ContinuousLinearMap.toPointwiseConvergenceCLM K (RingHom.id K) A G := by
  ext T v
  exact toPointwiseConvergenceCLMOfFiniteDimensional_apply T v

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- From a finite-dimensional seminormed domain, convergence in the given
operator-norm topology along any filter is equivalent to convergence of every
fixed-vector evaluation. The scalar field may be incomplete, and the original
spaces need not be separated or complete. Finite-dimensionality uses the given
domain module structure. -/
theorem tendsto_iff_apply_of_finiteDimensional
    {K : Type uK} [kK : NontriviallyNormedField K]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace K G kK.toNormedField sG]
    {X : Type uX} {l : Filter X}
    {L : X → A →L[K] G} {L0 : A →L[K] G} :
    Tendsto L l (𝓝 L0) ↔
      ∀ v : A, Tendsto (fun x : X => L x v) l (𝓝 (L0 v)) := by
  let e := ContinuousLinearEquiv.toPointwiseConvergenceCLMOfFiniteDimensional K A G
  have htransport :
      Tendsto L l (𝓝 L0) ↔ Tendsto (fun x : X => e (L x)) l (𝓝 (e L0)) :=
    e.toHomeomorph.isEmbedding.tendsto_nhds_iff
  rw [htransport, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  simp only [e, ContinuousLinearEquiv.toPointwiseConvergenceCLMOfFiniteDimensional_apply]

/-- The finite-source total-boundedness calculation, used after dense restriction. -/
private theorem totallyBounded_iff_apply_of_finiteDimensionalₛₗ_core
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (s : Set (A →SL[σ] G)) :
    TotallyBounded s ↔
      ∀ v : A, TotallyBounded ((fun T : A →SL[σ] G => T v) '' s) := by
  let e : (A →SL[σ] G) ≃L[L] (A →SLₚₜ[σ] G) :=
    ContinuousLinearEquiv.toUniformConvergenceCLMOfFiniteDimensional K L σ A G
      {s : Set A | Finite s}
      (fun s hs => (Set.finite_coe_iff.mp hs).isBounded)
      (by
        have hcover : ⋃₀ {s : Set A | Finite s} = Set.univ :=
          Set.sUnion_finite_eq_univ
        rw [hcover, Submodule.span_univ])
  calc
    TotallyBounded s ↔ TotallyBounded (e '' s) :=
      (totallyBounded_image_iff e.isUniformEmbedding.isUniformInducing).symm
    _ ↔ TotallyBounded (((↑) : (A →SLₚₜ[σ] G) → A → G) '' (e '' s)) :=
      (totallyBounded_image_iff
        (PointwiseConvergenceCLM.isUniformEmbedding_coeFn σ A G).isUniformInducing).symm
    _ ↔ ∀ v : A, TotallyBounded ((fun T : A →SL[σ] G => T v) '' s) := by
      rw [totallyBounded_pi_iff]
      simp only [Set.image_image, e,
        ContinuousLinearEquiv.toUniformConvergenceCLMOfFiniteDimensional_apply]

/-- A family of continuous semilinear maps is totally bounded if and only if its evaluation
image at every vector of a dense finite-dimensional submodule is totally bounded. The ambient
source need not be finite-dimensional, the fields and spaces need not be complete, and the
spaces need not be separated. -/
theorem totallyBounded_iff_apply_of_dense_finiteDimensionalₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (P : Submodule K A) [FiniteDimensional K P]
    (hP : Dense (P : Set A)) (s : Set (A →SL[σ] G)) :
    TotallyBounded s ↔
      ∀ p : P, TotallyBounded ((fun T : A →SL[σ] G => T (p : A)) '' s) := by
  calc
    TotallyBounded s ↔
        TotallyBounded ((fun T : A →SL[σ] G => T.domRestrict P) '' s) :=
      (totallyBounded_image_iff
        (isUniformInducing_domRestrict_of_dense (σ := σ) (G := G) P hP)).symm
    _ ↔ ∀ p : P, TotallyBounded ((fun T : A →SL[σ] G => T (p : A)) '' s) := by
      simpa only [Set.image_image, ContinuousLinearMap.coe_domRestrict,
        Set.domRestrict_apply] using
        (totallyBounded_iff_apply_of_finiteDimensionalₛₗ_core
          ((fun T : A →SL[σ] G => T.domRestrict P) '' s))

/-- A set of continuous semilinear maps on a finite-dimensional seminormed domain
is totally bounded for the original bounded-convergence uniformity if and only if its image
under every fixed-vector evaluation is totally bounded. The target field is only assumed
normed. The scalar homomorphism is isometric but need not be surjective, and the target retains
its given scalar action. Neither scalar field nor either space needs to be complete, and the
spaces need not be separated. -/
theorem totallyBounded_iff_apply_of_finiteDimensionalₛₗ
    {K : Type uK} [kK : NontriviallyNormedField K]
    {L : Type uL} [kL : NormedField L]
    {σ : K →+* L} [RingHomIsometric σ]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace L G kL sG]
    (s : Set (A →SL[σ] G)) :
    TotallyBounded s ↔
      ∀ v : A, TotallyBounded ((fun T : A →SL[σ] G => T v) '' s) := by
  simpa only [Subtype.forall, Submodule.mem_top, forall_true_left] using
    (totallyBounded_iff_apply_of_dense_finiteDimensionalₛₗ
      (σ := σ) (⊤ : Submodule K A)
      (by simp) s)

/-- A set of continuous linear maps on a finite-dimensional seminormed domain
is totally bounded for the operator-norm uniformity if and only if its image
under every fixed-vector evaluation is totally bounded. The scalar field may
be incomplete, and the domain and target need not be separated or complete. -/
theorem totallyBounded_iff_apply_of_finiteDimensional
    {K : Type uK} [kK : NontriviallyNormedField K]
    {A : Type uA} [sA : SeminormedAddCommGroup A]
    [nA : @NormedSpace K A kK.toNormedField sA]
    [hA : @FiniteDimensional K A (inferInstance : DivisionRing K)
      sA.toAddCommGroup nA.toModule]
    {G : Type uG} [sG : SeminormedAddCommGroup G]
    [nG : @NormedSpace K G kK.toNormedField sG]
    (s : Set (A →L[K] G)) :
    TotallyBounded s ↔
      ∀ v : A, TotallyBounded ((fun T : A →L[K] G => T v) '' s) := by
  simpa only [Subtype.forall, Submodule.mem_top, forall_true_left] using
    (totallyBounded_iff_apply_of_dense_finiteDimensionalₛₗ
      (σ := RingHom.id K) (⊤ : Submodule K A)
      (by simp) s)

end ContinuousLinearMap
