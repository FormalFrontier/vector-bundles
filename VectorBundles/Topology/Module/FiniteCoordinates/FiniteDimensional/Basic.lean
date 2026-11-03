/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.FiniteCoordinates.OperatorNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import VectorBundles.Analysis.Normed.Module.Completion
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
