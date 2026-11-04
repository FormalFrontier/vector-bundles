/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import Mathlib.Topology.ContinuousMap.Algebra
public import VectorBundles.Topology.VectorBundle.FiniteSum
public import VectorBundles.Topology.VectorBundle.Section
public import VectorBundles.Topology.Bornology.Bounded
public import Mathlib.Data.Finset.Fold
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Addition, positive rescaling and finite averages of supplied Hermitian metrics

`Bundle.HermitianMetric.add` and `Bundle.HermitianMetric.rescale` operate on supplied
metrics on the same indexed family of topological modules. The weights for rescaling
are arbitrary pointwise-positive real functions. No topology on the base is needed.

`Bundle.ContinuousHermitianMetric.add` and `Bundle.ContinuousHermitianMetric.rescale`
retain the given model, fiber and total-space topologies, and the given fiber-bundle and
vector-bundle structures. Continuous rescaling accepts any `ContinuousMapClass` of real
weights and requires pointwise positivity, not a uniform positive lower bound.
Continuity is continuity of the iterated Hom-bundle section, not only of scalar evaluations.
No zero metric or unrestricted scalar action on metrics is introduced.

The finite nonempty averages use an arbitrary input as the seed of a commutative
`Finset.fold`, then rescale by the reciprocal cardinality. Their pointwise formulas
are independent of the seed and enumeration, as for Mathlib's `Finset.expect`.
The continuous average uses the same fiberwise average and continuity of finite
sums of sections of the iterated Hom bundle.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Proposition 1.2 and its
  Hermitian remark, for positive sums of Hermitian forms.
* Sébastien Gouëzel, Mathlib's `Topology.VectorBundle.Riemannian`, for the metric data.
* Heather Macbeth and Floris van Doorn, Mathlib's Hom-bundle topology.
* Moritz Doll, Mathlib's von Neumann boundedness and small-sets characterization.
* Mario Carneiro, Mathlib's `Finset.fold`, and Yaël Dillies and Bhavik Mehta,
  Mathlib's finite expectations, for finite averaging.
-/

@[expose] public section

namespace Bundle

universe uκ uB uE uF uA uι uι'

section Fiberwise

variable {κ : Type uκ} [RCLike κ] {B : Type uB} {E : B → Type uE}
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]

/-- Add two supplied Hermitian metrics on the same topological module family. -/
def HermitianMetric.add (g h : HermitianMetric κ E) : HermitianMetric κ E where
  inner b := g.inner b + h.inner b
  symm := by
    intro b v w
    simp only [add_apply, map_add, g.symm, h.symm]
  pos := by
    intro b v hv
    change 0 < RCLike.re (g.inner b v v + h.inner b v v)
    rw [map_add]
    exact add_pos_of_pos_of_nonneg (g.pos b v hv) (h.re_inner_self_nonneg b v)
  continuousAt := by
    intro b
    exact (g.continuousAt b).add (h.continuousAt b)
  isVonNBounded := by
    intro b
    apply (g.isVonNBounded b).subset
    intro v hv
    change RCLike.re (g.inner b v v + h.inner b v v) < 1 at hv
    rw [map_add] at hv
    exact lt_of_le_of_lt (le_add_of_nonneg_right (h.re_inner_self_nonneg b v)) hv

/-- Rescale a supplied Hermitian metric by any pointwise-positive real function.
The scalar action is the existing κ-action on the sesquilinear forms. -/
def HermitianMetric.rescale (g : HermitianMetric κ E) (a : B → ℝ)
    (ha : ∀ b, 0 < a b) : HermitianMetric κ E where
  inner b := (a b : κ) • g.inner b
  symm := by
    intro b v w
    simp only [smul_apply, smul_eq_mul, map_mul, RCLike.conj_ofReal, g.symm]
  pos := by
    intro b v hv
    simpa only [smul_apply, smul_eq_mul, RCLike.re_ofReal_mul] using
      mul_pos (ha b) (g.pos b v hv)
  continuousAt := by
    intro b
    exact continuousAt_const.mul (g.continuousAt b)
  isVonNBounded := by
    intro b
    have hs : (Real.sqrt (a b) : κ) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (ha b)))
    have hdiag (v : E b) :
        RCLike.re (g.inner b ((Real.sqrt (a b) : κ) • v)
          ((Real.sqrt (a b) : κ) • v)) = a b * RCLike.re (g.inner b v v) := by
      rw [ContinuousLinearMap.map_smulₛₗ₂, ContinuousLinearMap.map_smul]
      simp only [RCLike.conj_ofReal, smul_eq_mul]
      rw [← mul_assoc, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul,
        ← sq, Real.sq_sqrt (ha b).le]
    apply ((g.isVonNBounded b).smul_set (Real.sqrt (a b) : κ)⁻¹).subset
    intro v hv
    refine Set.mem_smul_set.mpr ⟨(Real.sqrt (a b) : κ) • v, ?_, ?_⟩
    · change RCLike.re (g.inner b ((Real.sqrt (a b) : κ) • v)
        ((Real.sqrt (a b) : κ) • v)) < 1
      rw [hdiag]
      change RCLike.re ((a b : κ) * g.inner b v v) < 1 at hv
      rwa [RCLike.re_ofReal_mul] at hv
    · simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The inner form of a sum is the sum of the supplied inner forms. -/
@[simp]
theorem HermitianMetric.add_inner (g h : HermitianMetric κ E) (b : B) :
    (g.add h).inner b = g.inner b + h.inner b := by
  rfl

/-- Evaluation of the sum metric is the sum of the supplied pairings. -/
theorem HermitianMetric.add_inner_apply (g h : HermitianMetric κ E)
    (b : B) (v w : E b) :
    (g.add h).inner b v w = g.inner b v w + h.inner b v w := by
  rfl

/-- The inner form of a rescaled metric is the scalar multiple of the supplied form. -/
@[simp]
theorem HermitianMetric.rescale_inner (g : HermitianMetric κ E) (a : B → ℝ)
    (ha : ∀ b, 0 < a b) (b : B) :
    (g.rescale a ha).inner b = (a b : κ) • g.inner b := by
  rfl

/-- Evaluation of a rescaled metric multiplies the supplied pairing by the real weight. -/
theorem HermitianMetric.rescale_inner_apply (g : HermitianMetric κ E) (a : B → ℝ)
    (ha : ∀ b, 0 < a b) (b : B) (v w : E b) :
    (g.rescale a ha).inner b v w = (a b : κ) * g.inner b v w := by
  rfl

/-- Addition of supplied Hermitian metrics is commutative. -/
theorem HermitianMetric.add_comm (g h : HermitianMetric κ E) : g.add h = h.add g := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.add_inner_apply, _root_.add_comm]

/-- Addition of supplied Hermitian metrics is associative. -/
theorem HermitianMetric.add_assoc (g h k : HermitianMetric κ E) :
    (g.add h).add k = g.add (h.add k) := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.add_inner_apply, _root_.add_assoc]

/-- The constant-one weight leaves a supplied metric unchanged. -/
@[simp]
theorem HermitianMetric.rescale_one (g : HermitianMetric κ E) :
    g.rescale (fun _ ↦ 1) (fun _ ↦ zero_lt_one) = g := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.rescale_inner_apply, RCLike.ofReal_one, one_mul]

/-- Successive rescalings multiply their pointwise weights. -/
theorem HermitianMetric.rescale_rescale (g : HermitianMetric κ E)
    (a d : B → ℝ) (ha : ∀ b, 0 < a b) (hd : ∀ b, 0 < d b) :
    (g.rescale a ha).rescale d hd =
      g.rescale (fun b ↦ d b * a b) (fun b ↦ mul_pos (hd b) (ha b)) := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.rescale_inner_apply, RCLike.ofReal_mul, mul_assoc]

/-- Positive rescaling distributes over addition of metrics. -/
theorem HermitianMetric.rescale_add (g h : HermitianMetric κ E)
    (a : B → ℝ) (ha : ∀ b, 0 < a b) :
    (g.add h).rescale a ha = (g.rescale a ha).add (h.rescale a ha) := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.rescale_inner_apply, HermitianMetric.add_inner_apply, mul_add]


private instance : Std.Commutative (HermitianMetric.add (κ := κ) (E := E)) :=
  ⟨HermitianMetric.add_comm⟩

private instance : Std.Associative (HermitianMetric.add (κ := κ) (E := E)) :=
  ⟨HermitianMetric.add_assoc⟩

private theorem hermitianMetric_fold_inner_apply {ι : Type uι} (s : Finset ι)
    (h : HermitianMetric κ E) (g : ι → HermitianMetric κ E) (b : B) (v w : E b) :
    (s.fold HermitianMetric.add h g).inner b v w =
      (∑ i ∈ s, (g i).inner b v w) + h.inner b v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.fold_empty, Finset.sum_empty, zero_add]
  | @insert i s hi ih =>
    simp only [Finset.fold_insert hi, HermitianMetric.add_inner_apply, ih,
      Finset.sum_insert hi, _root_.add_assoc]

variable {ι : Type uι} [Finite ι] [Nonempty ι]

/-- The uniform average of a finite nonempty family of supplied Hermitian metrics.
The original fiber topologies and scalar actions are unchanged. -/
noncomputable def HermitianMetric.average (g : ι → HermitianMetric κ E) :
    HermitianMetric κ E := by
  classical
  letI := Fintype.ofFinite ι
  letI : Std.Commutative (HermitianMetric.add (κ := κ) (E := E)) :=
    ⟨HermitianMetric.add_comm⟩
  letI : Std.Associative (HermitianMetric.add (κ := κ) (E := E)) :=
    ⟨HermitianMetric.add_assoc⟩
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  exact ((Finset.univ.erase i₀).fold HermitianMetric.add (g i₀) g).rescale
    (fun _ ↦ (Nat.card ι : ℝ)⁻¹)
    (fun _ ↦ inv_pos.mpr (Nat.cast_pos.mpr (Nat.card_pos : 0 < Nat.card ι)))

/-- Evaluation of a finite average is the normalized finite sum of the pairings. -/
theorem HermitianMetric.average_inner_apply (g : ι → HermitianMetric κ E)
    (b : B) (v w : E b) :
    (HermitianMetric.average g).inner b v w =
      ((Nat.card ι : ℝ)⁻¹ : κ) * ∑ᶠ i, (g i).inner b v w := by
  classical
  let _ := Fintype.ofFinite ι
  rw [HermitianMetric.average, HermitianMetric.rescale_inner_apply,
    hermitianMetric_fold_inner_apply,
    Finset.sum_erase_add _ _ (Finset.mem_univ _), finsum_eq_sum_of_fintype,
    RCLike.ofReal_inv]

/-- The inner form of a finite average is the normalized sum of the inner forms. -/
theorem HermitianMetric.average_inner (g : ι → HermitianMetric κ E) (b : B) :
    (HermitianMetric.average g).inner b = ((Nat.card ι : ℝ)⁻¹ : κ) • ∑ᶠ i, (g i).inner b := by
  classical
  let _ := Fintype.ofFinite ι
  ext v w
  simp [HermitianMetric.average_inner_apply, finsum_eq_sum_of_fintype, smul_eq_mul]

/-- Averaging a constant family leaves its metric unchanged. -/
@[simp]
theorem HermitianMetric.average_const (g : HermitianMetric κ E) :
    HermitianMetric.average (fun _ : ι ↦ g) = g := by
  classical
  let _ := Fintype.ofFinite ι
  have hc : (Nat.card ι : κ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card ι ≠ 0)
  apply HermitianMetric.ext
  intro b v w
  rw [HermitianMetric.average_inner_apply, finsum_eq_sum_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, RCLike.ofReal_natCast,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Pointwise equal metric families have equal averages. -/
theorem HermitianMetric.average_congr {g h : ι → HermitianMetric κ E}
    (hgh : ∀ i, g i = h i) :
    HermitianMetric.average g = HermitianMetric.average h := by
  rw [funext hgh]

/-- A finite average is unchanged by equivalence reindexing. -/
theorem HermitianMetric.average_comp_equiv {ι' : Type uι'} [Finite ι'] [Nonempty ι']
    (g : ι' → HermitianMetric κ E) (e : ι ≃ ι') :
    HermitianMetric.average (g ∘ e) = HermitianMetric.average g := by
  apply HermitianMetric.ext
  intro b v w
  simp only [HermitianMetric.average_inner_apply, Function.comp_apply, Nat.card_congr e]
  congr 1
  exact finsum_comp_equiv e (f := fun i ↦ (g i).inner b v w)

end Fiberwise

section Continuous

variable {κ : Type uκ} [RCLike κ] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]
  [FiberBundle F E] [VectorBundle κ F E]

/-- Add two supplied continuous Hermitian metrics using the same bundle structures. -/
def ContinuousHermitianMetric.add (g h : ContinuousHermitianMetric κ F E) :
    ContinuousHermitianMetric κ F E where
  inner b := g.inner b + h.inner b
  symm := (g.toHermitianMetric.add h.toHermitianMetric).symm
  pos := (g.toHermitianMetric.add h.toHermitianMetric).pos
  isVonNBounded := (g.toHermitianMetric.add h.toHermitianMetric).isVonNBounded
  continuous := by
    let s : Bool → ∀ b, E b →L⋆[κ] E b →L[κ] κ :=
      fun i b ↦ if i then g.inner b else h.inner b
    have hs : ∀ i, Continuous (fun b ↦
        TotalSpace.mk' (F →L⋆[κ] F →L[κ] κ) b (s i b)) := by
      intro i
      cases i
      · exact h.continuous
      · exact g.continuous
    simpa [s, finsum_eq_sum_of_fintype, Fintype.sum_bool] using
      (VectorBundle.continuous_finsum_section κ
        (F := F →L⋆[κ] F →L[κ] κ) (s := s) hs (locallyFinite_of_finite _))

/-- Rescale a supplied continuous metric by a continuous pointwise-positive real weight.
No algebraic or topological structure on the type of bundled weights is required. -/
def ContinuousHermitianMetric.rescale {A : Type uA} [FunLike A B ℝ]
    [ContinuousMapClass A B ℝ] (g : ContinuousHermitianMetric κ F E)
    (a : A) (ha : ∀ b, 0 < a b) : ContinuousHermitianMetric κ F E where
  inner b := (a b : κ) • g.inner b
  symm := (g.toHermitianMetric.rescale (a : B → ℝ) ha).symm
  pos := (g.toHermitianMetric.rescale (a : B → ℝ) ha).pos
  isVonNBounded := (g.toHermitianMetric.rescale (a : B → ℝ) ha).isVonNBounded
  continuous := by
    exact VectorBundle.continuous_smul_section (κ := κ)
      (F := F →L⋆[κ] F →L[κ] κ)
      (RCLike.continuous_ofReal.comp (map_continuous a)) g.continuous

/-- The inner form of a continuous sum is the sum of the supplied forms. -/
@[simp]
theorem ContinuousHermitianMetric.add_inner (g h : ContinuousHermitianMetric κ F E) (b : B) :
    (g.add h).inner b = g.inner b + h.inner b := by
  rfl

/-- Evaluation of a continuous sum is the sum of the supplied pairings. -/
theorem ContinuousHermitianMetric.add_inner_apply (g h : ContinuousHermitianMetric κ F E)
    (b : B) (v w : E b) :
    (g.add h).inner b v w = g.inner b v w + h.inner b v w := by
  rfl

/-- Forgetting base continuity commutes with addition. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_add (g h : ContinuousHermitianMetric κ F E) :
    (g.add h).toHermitianMetric = g.toHermitianMetric.add h.toHermitianMetric := by
  apply HermitianMetric.ext
  intro b v w
  rfl

variable {A : Type uA} [FunLike A B ℝ] [ContinuousMapClass A B ℝ]

/-- The inner form of a continuous rescaling is the scalar multiple of the supplied form. -/
@[simp]
theorem ContinuousHermitianMetric.rescale_inner (g : ContinuousHermitianMetric κ F E)
    (a : A) (ha : ∀ b, 0 < a b) (b : B) :
    (g.rescale a ha).inner b = (a b : κ) • g.inner b := by
  rfl

/-- Evaluation of a continuous rescaling multiplies the supplied pairing by the real weight. -/
theorem ContinuousHermitianMetric.rescale_inner_apply (g : ContinuousHermitianMetric κ F E)
    (a : A) (ha : ∀ b, 0 < a b) (b : B) (v w : E b) :
    (g.rescale a ha).inner b v w = (a b : κ) * g.inner b v w := by
  rfl

/-- Forgetting base continuity commutes with positive rescaling. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_rescale (g : ContinuousHermitianMetric κ F E)
    (a : A) (ha : ∀ b, 0 < a b) :
    (g.rescale a ha).toHermitianMetric =
      g.toHermitianMetric.rescale (a : B → ℝ) ha := by
  apply HermitianMetric.ext
  intro b v w
  rfl

/-- Addition of continuous Hermitian metrics is commutative. -/
theorem ContinuousHermitianMetric.add_comm (g h : ContinuousHermitianMetric κ F E) :
    g.add h = h.add g := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  simp only [ContinuousHermitianMetric.add_inner_apply, _root_.add_comm]

/-- Addition of continuous Hermitian metrics is associative. -/
theorem ContinuousHermitianMetric.add_assoc (g h k : ContinuousHermitianMetric κ F E) :
    (g.add h).add k = g.add (h.add k) := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  simp only [ContinuousHermitianMetric.add_inner_apply, _root_.add_assoc]

/-- The constant-one continuous weight leaves a supplied metric unchanged. -/
@[simp]
theorem ContinuousHermitianMetric.rescale_one (g : ContinuousHermitianMetric κ F E) :
    g.rescale (1 : C(B, ℝ)) (fun _ ↦ zero_lt_one) = g := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  simpa only [ContinuousMap.one_apply, RCLike.ofReal_one, one_mul] using
    ContinuousHermitianMetric.rescale_inner_apply g (1 : C(B, ℝ))
      (fun _ ↦ zero_lt_one) b v w

/-- Successive continuous rescalings multiply their pointwise weights. -/
theorem ContinuousHermitianMetric.rescale_rescale (g : ContinuousHermitianMetric κ F E)
    (a d : C(B, ℝ)) (ha : ∀ b, 0 < a b) (hd : ∀ b, 0 < d b) :
    (g.rescale a ha).rescale d hd =
      g.rescale (d * a) (fun b ↦ mul_pos (hd b) (ha b)) := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  simp only [ContinuousHermitianMetric.rescale_inner_apply, ContinuousMap.mul_apply,
    RCLike.ofReal_mul, mul_assoc]

/-- Positive continuous rescaling distributes over addition of metrics. -/
theorem ContinuousHermitianMetric.rescale_add (g h : ContinuousHermitianMetric κ F E)
    (a : A) (ha : ∀ b, 0 < a b) :
    (g.add h).rescale a ha = (g.rescale a ha).add (h.rescale a ha) := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  simp only [ContinuousHermitianMetric.rescale_inner_apply,
    ContinuousHermitianMetric.add_inner_apply, mul_add]


variable {ι : Type uι} [Finite ι] [Nonempty ι]

/-- The uniform average of a finite nonempty family of supplied continuous metrics.
Continuity is in the original iterated Hom bundle. -/
noncomputable def ContinuousHermitianMetric.average
    (g : ι → ContinuousHermitianMetric κ F E) : ContinuousHermitianMetric κ F E where
  inner := (HermitianMetric.average (fun i ↦ (g i).toHermitianMetric)).inner
  symm := (HermitianMetric.average (fun i ↦ (g i).toHermitianMetric)).symm
  pos := (HermitianMetric.average (fun i ↦ (g i).toHermitianMetric)).pos
  isVonNBounded := (HermitianMetric.average (fun i ↦ (g i).toHermitianMetric)).isVonNBounded
  continuous := by
    simp_rw [HermitianMetric.average_inner]
    exact VectorBundle.continuous_smul_section (κ := κ)
      (F := F →L⋆[κ] F →L[κ] κ) continuous_const
      (VectorBundle.continuous_finsum_section κ
        (F := F →L⋆[κ] F →L[κ] κ) (s := fun i b ↦ (g i).inner b)
        (fun i ↦ (g i).continuous) (locallyFinite_of_finite _))

/-- Evaluation of a continuous average is the normalized sum of the pairings. -/
theorem ContinuousHermitianMetric.average_inner_apply
    (g : ι → ContinuousHermitianMetric κ F E) (b : B) (v w : E b) :
    (ContinuousHermitianMetric.average g).inner b v w =
      ((Nat.card ι : ℝ)⁻¹ : κ) * ∑ᶠ i, (g i).inner b v w :=
  HermitianMetric.average_inner_apply (fun i ↦ (g i).toHermitianMetric) b v w

/-- The inner form of a continuous average is the normalized sum of the inner forms. -/
theorem ContinuousHermitianMetric.average_inner
    (g : ι → ContinuousHermitianMetric κ F E) (b : B) :
    (ContinuousHermitianMetric.average g).inner b =
      ((Nat.card ι : ℝ)⁻¹ : κ) • ∑ᶠ i, (g i).inner b :=
  HermitianMetric.average_inner (fun i ↦ (g i).toHermitianMetric) b

/-- Forgetting base continuity commutes with finite averaging. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_average
    (g : ι → ContinuousHermitianMetric κ F E) :
    (ContinuousHermitianMetric.average g).toHermitianMetric =
      HermitianMetric.average (fun i ↦ (g i).toHermitianMetric) := by
  apply HermitianMetric.ext
  intro b v w
  rfl

private theorem continuousHermitianMetric_toHermitianMetric_injective :
    Function.Injective (fun g : ContinuousHermitianMetric κ F E ↦ g.toHermitianMetric) := by
  intro g h hgh
  apply ContinuousHermitianMetric.ext
  intro b v w
  exact congrArg (fun m : HermitianMetric κ E ↦ m.inner b v w) hgh

/-- Averaging a constant continuous metric family leaves the metric unchanged. -/
@[simp]
theorem ContinuousHermitianMetric.average_const (g : ContinuousHermitianMetric κ F E) :
    ContinuousHermitianMetric.average (fun _ : ι ↦ g) = g := by
  apply continuousHermitianMetric_toHermitianMetric_injective
  simpa only [ContinuousHermitianMetric.toHermitianMetric_average] using
    (HermitianMetric.average_const (ι := ι) g.toHermitianMetric)

/-- Pointwise equal continuous metric families have equal averages. -/
theorem ContinuousHermitianMetric.average_congr
    {g h : ι → ContinuousHermitianMetric κ F E} (hgh : ∀ i, g i = h i) :
    ContinuousHermitianMetric.average g = ContinuousHermitianMetric.average h := by
  rw [funext hgh]

/-- A continuous finite average is unchanged by equivalence reindexing. -/
theorem ContinuousHermitianMetric.average_comp_equiv
    {ι' : Type uι'} [Finite ι'] [Nonempty ι']
    (g : ι' → ContinuousHermitianMetric κ F E) (e : ι ≃ ι') :
    ContinuousHermitianMetric.average (g ∘ e) =
      ContinuousHermitianMetric.average g := by
  apply continuousHermitianMetric_toHermitianMetric_injective
  simpa only [ContinuousHermitianMetric.toHermitianMetric_average, Function.comp_def] using
    HermitianMetric.average_comp_equiv (fun i ↦ (g i).toHermitianMetric) e

end Continuous

end Bundle
