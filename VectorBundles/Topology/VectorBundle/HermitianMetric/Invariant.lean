/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.HermitianMetric.Operations
public import VectorBundles.Topology.VectorBundle.MetricPullback
public import VectorBundles.Topology.VectorBundle.MetricComap
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Finite averaging of Hermitian metrics over a moving base

The finite average of the supplied pullback-comap metrics has the normalized sum
of transported pairings. Pairing-preserving input is recovered without action laws.
For compatible actions on the base and total space, right multiplication reindexes
the sum and gives invariance for every supplied input metric.

For continuous metrics the regularity assumption is continuity of the supplied
operators as a section of the canonical norm-Hom bundle into the pullback bundle.
Only the models are normed; the original fiber and total-space structures are retained.
-/

@[expose] public section

namespace Bundle

universe uκ uG uB uF uE

section Fiberwise

variable {κ : Type uκ} [RCLike κ] {G : Type uG} {B : Type uB}
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]

section Formation

variable [SMul G B] [Finite G] [Nonempty G]

/-- The average of pullback-comap metrics is the normalized sum of transported pairings. -/
theorem HermitianMetric.average_smul_inner_apply (m : HermitianMetric κ E)
    (A : ∀ (g : G) (b : B), E b ≃L[κ] E (g • b)) (b : B) (v w : E b) :
    (HermitianMetric.average (fun g : G ↦
      (m.pullback (fun b : B ↦ g • b)).comap
        (fun b ↦ (A g b).toContinuousLinearMap)
        (fun b ↦ (A g b).toHomeomorph.isEmbedding))).inner b v w =
      (Nat.card G : κ)⁻¹ * ∑ᶠ g, m.inner (g • b) (A g b v) (A g b w) := by
  calc
    _ = ((Nat.card G : ℝ)⁻¹ : κ) * ∑ᶠ g : G,
        ((m.pullback (fun b : B ↦ g • b)).comap
          (fun b ↦ (A g b).toContinuousLinearMap)
          (fun b ↦ (A g b).toHomeomorph.isEmbedding)).inner b v w :=
      HermitianMetric.average_inner_apply (fun g : G ↦
        (m.pullback (fun b : B ↦ g • b)).comap
          (fun b ↦ (A g b).toContinuousLinearMap)
          (fun b ↦ (A g b).toHomeomorph.isEmbedding)) b v w
    _ = ((Nat.card G : ℝ)⁻¹ : κ) *
        ∑ᶠ g : G, m.inner (g • b) (A g b v) (A g b w) := by
      apply congrArg (fun z : κ ↦ ((Nat.card G : ℝ)⁻¹ : κ) * z)
      apply finsum_congr
      intro g
      exact (HermitianMetric.comap_inner_apply (m.pullback (fun b : B ↦ g • b))
        (fun b ↦ (A g b).toContinuousLinearMap)
        (fun b ↦ (A g b).toHomeomorph.isEmbedding) b v w).trans
        (HermitianMetric.pullback_inner_apply m (fun b : B ↦ g • b)
          b (A g b v) (A g b w))
    _ = _ := by
      have hcoef : ((Nat.card G : ℝ)⁻¹ : κ) = (Nat.card G : κ)⁻¹ :=
        congrArg (fun c : κ ↦ c⁻¹) (RCLike.ofReal_natCast (K := κ) (Nat.card G))
      exact congrArg (fun c : κ ↦ c *
        ∑ᶠ g : G, m.inner (g • b) (A g b v) (A g b w)) hcoef

/-- Pairing-preserving supplied maps leave a metric unchanged by averaging. -/
theorem HermitianMetric.average_smul_eq_self (m : HermitianMetric κ E)
    (A : ∀ (g : G) (b : B), E b ≃L[κ] E (g • b))
    (hm : ∀ (g : G) (b : B) (v w : E b),
      m.inner (g • b) (A g b v) (A g b w) = m.inner b v w) :
    HermitianMetric.average (fun g : G ↦
      (m.pullback (fun b : B ↦ g • b)).comap
        (fun b ↦ (A g b).toContinuousLinearMap)
        (fun b ↦ (A g b).toHomeomorph.isEmbedding)) = m := by
  have hmetric (g : G) :
      (m.pullback (fun b : B ↦ g • b)).comap
        (fun b ↦ (A g b).toContinuousLinearMap)
        (fun b ↦ (A g b).toHomeomorph.isEmbedding) = m := by
    apply HermitianMetric.ext
    intro b v w
    exact (HermitianMetric.comap_inner_apply (m.pullback (fun b : B ↦ g • b))
      (fun b ↦ (A g b).toContinuousLinearMap)
      (fun b ↦ (A g b).toHomeomorph.isEmbedding) b v w).trans
      ((HermitianMetric.pullback_inner_apply m (fun b : B ↦ g • b)
        b (A g b v) (A g b w)).trans (hm g b v w))
  exact (HermitianMetric.average_congr hmetric).trans
    (HermitianMetric.average_const (ι := G) m)

end Formation

section Invariance

variable [Group G] [Finite G] [MulAction G B]
  {F : Type uF} [MulAction G (TotalSpace F E)]

/-- Compatibility with the base and total-space actions makes the average invariant,
without any invariance assumption on the supplied metric. -/
theorem HermitianMetric.average_smul_invariant (m : HermitianMetric κ E)
    (A : ∀ (g : G) (b : B), E b ≃L[κ] E (g • b))
    (hA : ∀ (g : G) (b : B) (v : E b),
      g • TotalSpace.mk' F b v = TotalSpace.mk' F (g • b) (A g b v))
    (h : G) (b : B) (v w : E b) :
    (HermitianMetric.average (fun g : G ↦
      (m.pullback (fun b : B ↦ g • b)).comap
        (fun b ↦ (A g b).toContinuousLinearMap)
        (fun b ↦ (A g b).toHomeomorph.isEmbedding))).inner
          (h • b) (A h b v) (A h b w) =
      (HermitianMetric.average (fun g : G ↦
        (m.pullback (fun b : B ↦ g • b)).comap
          (fun b ↦ (A g b).toContinuousLinearMap)
          (fun b ↦ (A g b).toHomeomorph.isEmbedding))).inner b v w := by
  have hmul (g h : G) (b : B) (v : E b) :
      TotalSpace.mk' F ((g * h) • b) (A (g * h) b v) =
        TotalSpace.mk' F (g • (h • b)) (A g (h • b) (A h b v)) := by
    calc
      _ = (g * h) • TotalSpace.mk' F b v := (hA (g * h) b v).symm
      _ = g • (h • TotalSpace.mk' F b v) := mul_smul g h _
      _ = g • TotalSpace.mk' F (h • b) (A h b v) :=
        congrArg (fun p : TotalSpace F E ↦ g • p) (hA h b v)
      _ = _ := hA g (h • b) (A h b v)
  have hcast (g h : G) (b : B) (v : E b) :
      cast (congrArg E (mul_smul g h b)) (A (g * h) b v) =
        A g (h • b) (A h b v) := by
    exact (TotalSpace.mk_inj (F := F) (E := E)).mp
      ((TotalSpace.mk_cast (F := F) (E := E)
        (mul_smul g h b) (A (g * h) b v)).trans (hmul g h b v))
  have hpair {b b' : B} (e : b = b') (v w : E b) :
      m.inner b' (cast (congrArg E e) v) (cast (congrArg E e) w) =
        m.inner b v w := by
    cases e
    rfl
  have hstep :
      (∑ᶠ g : G, m.inner (g • (h • b))
        (A g (h • b) (A h b v)) (A g (h • b) (A h b w))) =
      ∑ᶠ g : G, m.inner ((g * h) • b)
        (A (g * h) b v) (A (g * h) b w) := by
    apply finsum_congr
    intro g
    rw [← hcast g h b v, ← hcast g h b w]
    exact hpair (mul_smul g h b) (A (g * h) b v) (A (g * h) b w)
  have hreindex :
      (∑ᶠ g : G, m.inner ((g * h) • b)
        (A (g * h) b v) (A (g * h) b w)) =
      ∑ᶠ g : G, m.inner (g • b) (A g b v) (A g b w) := by
    exact finsum_comp_equiv (Equiv.mulRight h)
      (f := fun g : G ↦ m.inner (g • b) (A g b v) (A g b w))
  rw [HermitianMetric.average_smul_inner_apply,
    HermitianMetric.average_smul_inner_apply]
  exact congrArg (fun z : κ ↦ (Nat.card G : κ)⁻¹ * z)
    (hstep.trans hreindex)

end Invariance

end Fiberwise

section Continuous

variable {κ : Type uκ} [RCLike κ] {G : Type uG}
  {B : Type uB} [tB : TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module κ (E b)]
  [tE : TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle κ F E]

section Formation

variable [SMul G B] [Finite G] [Nonempty G] [ContinuousConstSMul G B]

variable (m : ContinuousHermitianMetric κ F E)
  (A : ∀ (g : G) (b : B), E b ≃L[κ] E (g • b))
  (hNorm : ∀ g : G,
    let f_g : C(B, B) :=
      ContinuousMap.mk (fun b : B ↦ g • b)
        (ContinuousConstSMul.continuous_const_smul g)
    let P_g := (f_g : B → B) *ᵖ E
    @Continuous B
      (TotalSpace (F →L[κ] F) (fun b ↦ E b →L[κ] P_g b))
      tB (@Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
        κ _ κ _ (RingHom.id κ) B F _ _ E _ _ _ F _ _ P_g _ _ _
        _ _ _ _ _ _ _
        (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
          (ContinuousLinearEquiv.toContinuousAddEquiv
            (VectorBundle.continuousLinearEquivAt κ F P_g b)))
        (fun b ↦ ContinuousLinearEquiv.continuousSMul
          (VectorBundle.continuousLinearEquivAt κ F P_g b)) _)
      (fun b ↦ TotalSpace.mk' (F →L[κ] F) b
        ((A g b).toContinuousLinearMap : E b →L[κ] P_g b)))

/-- Forgetting base continuity commutes with the moving-base average. -/
@[simp]
theorem ContinuousHermitianMetric.toHermitianMetric_average_smul :
    (ContinuousHermitianMetric.average (fun g : G ↦
      let f_g : C(B, B) :=
        ContinuousMap.mk (fun b : B ↦ g • b)
          (ContinuousConstSMul.continuous_const_smul g)
      let P_g := (f_g : B → B) *ᵖ E
      (m.pullback f_g).comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (show Topology.IsEmbedding
          ((A g b).toContinuousLinearMap : E b →L[κ] P_g b) from
            (A g b).toHomeomorph.isEmbedding)) (hNorm g))).toHermitianMetric =
      HermitianMetric.average (fun g : G ↦
        (m.toHermitianMetric.pullback (fun b : B ↦ g • b)).comap
          (fun b ↦ (A g b).toContinuousLinearMap)
          (fun b ↦ (A g b).toHomeomorph.isEmbedding)) := by
  rw [ContinuousHermitianMetric.toHermitianMetric_average]
  apply HermitianMetric.average_congr
  intro g
  let f_g : C(B, B) :=
    ContinuousMap.mk (fun b : B ↦ g • b)
      (ContinuousConstSMul.continuous_const_smul g)
  let P_g := (f_g : B → B) *ᵖ E
  calc
    _ = (m.pullback f_g).toHermitianMetric.comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (A g b).toHomeomorph.isEmbedding) :=
      ContinuousHermitianMetric.toHermitianMetric_comap (G := F) (m.pullback f_g)
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (A g b).toHomeomorph.isEmbedding) (hNorm g)
    _ = _ := congrArg
      (fun q : HermitianMetric κ P_g ↦ q.comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (A g b).toHomeomorph.isEmbedding))
      (ContinuousHermitianMetric.toHermitianMetric_pullback m f_g)

/-- The continuous moving-base average has the normalized transported pairing. -/
theorem ContinuousHermitianMetric.average_smul_inner_apply (b : B) (v w : E b) :
    (ContinuousHermitianMetric.average (fun g : G ↦
      let f_g : C(B, B) :=
        ContinuousMap.mk (fun b : B ↦ g • b)
          (ContinuousConstSMul.continuous_const_smul g)
      let P_g := (f_g : B → B) *ᵖ E
      (m.pullback f_g).comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (show Topology.IsEmbedding
          ((A g b).toContinuousLinearMap : E b →L[κ] P_g b) from
            (A g b).toHomeomorph.isEmbedding)) (hNorm g))).inner b v w =
      (Nat.card G : κ)⁻¹ * ∑ᶠ g, m.inner (g • b) (A g b v) (A g b w) := by
  have hpair := congrArg (fun metric : HermitianMetric κ E ↦ metric.inner b v w)
    (ContinuousHermitianMetric.toHermitianMetric_average_smul m A hNorm)
  exact hpair.trans (HermitianMetric.average_smul_inner_apply m.toHermitianMetric A b v w)

/-- Pairing-preserving supplied maps recover the original continuous metric. -/
theorem ContinuousHermitianMetric.average_smul_eq_self
    (hm : ∀ (g : G) (b : B) (v w : E b),
      m.inner (g • b) (A g b v) (A g b w) = m.inner b v w) :
    ContinuousHermitianMetric.average (fun g : G ↦
      let f_g : C(B, B) :=
        ContinuousMap.mk (fun b : B ↦ g • b)
          (ContinuousConstSMul.continuous_const_smul g)
      let P_g := (f_g : B → B) *ᵖ E
      (m.pullback f_g).comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (show Topology.IsEmbedding
          ((A g b).toContinuousLinearMap : E b →L[κ] P_g b) from
            (A g b).toHomeomorph.isEmbedding)) (hNorm g)) = m := by
  apply ContinuousHermitianMetric.ext
  intro b v w
  have heq := HermitianMetric.average_smul_eq_self m.toHermitianMetric A hm
  have hforget := ContinuousHermitianMetric.toHermitianMetric_average_smul m A hNorm
  exact congrArg (fun q : HermitianMetric κ E ↦ q.inner b v w) (hforget.trans heq)

end Formation

section Invariance

variable [Group G] [Finite G] [MulAction G B] [ContinuousConstSMul G B]
  [MulAction G (TotalSpace F E)]

variable (m : ContinuousHermitianMetric κ F E)
  (A : ∀ (g : G) (b : B), E b ≃L[κ] E (g • b))
  (hNorm : ∀ g : G,
    let f_g : C(B, B) :=
      ContinuousMap.mk (fun b : B ↦ g • b)
        (ContinuousConstSMul.continuous_const_smul g)
    let P_g := (f_g : B → B) *ᵖ E
    @Continuous B
      (TotalSpace (F →L[κ] F) (fun b ↦ E b →L[κ] P_g b))
      tB (@Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
        κ _ κ _ (RingHom.id κ) B F _ _ E _ _ _ F _ _ P_g _ _ _
        _ _ _ _ _ _ _
        (fun b ↦ ContinuousAddEquiv.isTopologicalAddGroup
          (ContinuousLinearEquiv.toContinuousAddEquiv
            (VectorBundle.continuousLinearEquivAt κ F P_g b)))
        (fun b ↦ ContinuousLinearEquiv.continuousSMul
          (VectorBundle.continuousLinearEquivAt κ F P_g b)) _)
      (fun b ↦ TotalSpace.mk' (F →L[κ] F) b
        ((A g b).toContinuousLinearMap : E b →L[κ] P_g b)))

/-- The continuous moving-base average is invariant under compatible actions on the
base and total space; norm-Hom regularity is the only additional continuity input. -/
theorem ContinuousHermitianMetric.average_smul_invariant
    (hA : ∀ (g : G) (b : B) (v : E b),
      g • TotalSpace.mk' F b v = TotalSpace.mk' F (g • b) (A g b v))
    (h : G) (b : B) (v w : E b) :
    (ContinuousHermitianMetric.average (fun g : G ↦
      let f_g : C(B, B) :=
        ContinuousMap.mk (fun b : B ↦ g • b)
          (ContinuousConstSMul.continuous_const_smul g)
      let P_g := (f_g : B → B) *ᵖ E
      (m.pullback f_g).comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (show Topology.IsEmbedding
          ((A g b).toContinuousLinearMap : E b →L[κ] P_g b) from
            (A g b).toHomeomorph.isEmbedding)) (hNorm g))).inner
      (h • b) (A h b v) (A h b w) =
      (ContinuousHermitianMetric.average (fun g : G ↦
      let f_g : C(B, B) :=
        ContinuousMap.mk (fun b : B ↦ g • b)
          (ContinuousConstSMul.continuous_const_smul g)
      let P_g := (f_g : B → B) *ᵖ E
      (m.pullback f_g).comap
        (fun b ↦ ((A g b).toContinuousLinearMap : E b →L[κ] P_g b))
        (fun b ↦ (show Topology.IsEmbedding
          ((A g b).toContinuousLinearMap : E b →L[κ] P_g b) from
            (A g b).toHomeomorph.isEmbedding)) (hNorm g))).inner b v w := by
  have hforget := ContinuousHermitianMetric.toHermitianMetric_average_smul m A hNorm
  have hi := HermitianMetric.average_smul_invariant (F := F)
    m.toHermitianMetric A hA h b v w
  have hl := congrArg
    (fun q : HermitianMetric κ E ↦ q.inner (h • b) (A h b v) (A h b w)) hforget
  have hr := congrArg (fun q : HermitianMetric κ E ↦ q.inner b v w) hforget
  exact hl.trans (hi.trans hr.symm)

end Invariance

end Continuous

end Bundle
