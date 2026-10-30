/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.AdjointPair

/-!
# Adjoint pairs with a nonzero radical

The plane with seminorm `‖(z,w)‖ = ‖z‖` has nonzero vectors of norm zero.
Its identity and a shear are distinct adjoint partners of the identity. The first
coordinate remains a genuine complex inner-product space, so the seminorm is not zero.
-/

@[expose] public section

noncomputable section

private def RadicalPlane := ℂ × ℂ

private instance : AddCommGroup RadicalPlane := inferInstanceAs (AddCommGroup (ℂ × ℂ))
private instance : Module ℂ RadicalPlane := inferInstanceAs (Module ℂ (ℂ × ℂ))

private def radicalPoint (z w : ℂ) : RadicalPlane := (z, w)

private def radicalFst : RadicalPlane →ₗ[ℂ] ℂ := LinearMap.fst ℂ ℂ ℂ

private instance : SeminormedAddCommGroup RadicalPlane :=
  SeminormedAddCommGroup.induced _ _ radicalFst.toAddMonoidHom

private instance : NormedSpace ℂ RadicalPlane :=
  NormedSpace.induced ℂ _ _ radicalFst

private instance : InnerProductSpace ℂ RadicalPlane :=
  InnerProductSpace.induced radicalFst

private def radicalShear : RadicalPlane →L[ℂ] RadicalPlane :=
  ({ toFun := fun x => (x.1, x.2 + x.1)
     map_add' := by
       intro x y
       apply Prod.ext
       · rfl
       · change (x.2 + y.2) + (x.1 + y.1) = (x.2 + x.1) + (y.2 + y.1)
         abel
     map_smul' := by
       intro c x
       apply Prod.ext
       · rfl
       · change c • x.2 + c • x.1 = c • (x.2 + x.1)
         exact (smul_add c x.2 x.1).symm } :
    RadicalPlane →ₗ[ℂ] RadicalPlane).mkContinuous 1 (by
      intro x
      change ‖x.1‖ ≤ 1 * ‖x.1‖
      simp)

/-- The nonseparated model still has a vector of positive norm. -/
private theorem radicalPlane_norm_one : ‖radicalPoint 1 0‖ = 1 := by
  change ‖(1 : ℂ)‖ = 1
  norm_num

/-- The radical contains a nonzero vector. -/
private theorem radicalPlane_nonzero_radical :
    radicalPoint 0 1 ≠ 0 ∧ ‖radicalPoint 0 1‖ = 0 := by
  constructor
  · intro h
    have hc := congrArg (fun x : RadicalPlane => x.2) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  · change ‖(0 : ℂ)‖ = 0
    simp

/-- A shear and the identity are adjoint for the given, degenerate complex pairing. -/
private theorem radicalPlane_isAdjointPair :
    Function.IsAdjointPair (inner ℂ) (inner ℂ)
      (ContinuousLinearMap.id ℂ RadicalPlane) radicalShear := by
  intro x y
  rfl

/-- The shear differs from the identity as a function. -/
private theorem radicalShear_ne_id : radicalShear ≠ ContinuousLinearMap.id ℂ RadicalPlane := by
  intro h
  have hc := congrArg (fun f : RadicalPlane →L[ℂ] RadicalPlane => f (1, 0)) h
  have hs := congrArg (fun x : RadicalPlane => x.2) hc
  change (0 : ℂ) + 1 = 0 at hs
  simp at hs

/-- The distinct partners in this model have distance zero. -/
private theorem radicalShear_dist_id :
    dist radicalShear (ContinuousLinearMap.id ℂ RadicalPlane) = 0 := by
  have hid : Function.IsAdjointPair (inner ℂ) (inner ℂ)
      (ContinuousLinearMap.id ℂ RadicalPlane) (ContinuousLinearMap.id ℂ RadicalPlane) :=
    Function.isAdjointPair_id (inner ℂ)
  simpa using (radicalPlane_isAdjointPair.dist_eq hid).symm

/-- The degenerate complex pairing admits the shear as a partner of the identity. -/
theorem Complex.isAdjointPair_degenerate_shear :
    Function.IsAdjointPair
      (fun x y : ℂ × ℂ => inner ℂ x.1 y.1)
      (fun x y : ℂ × ℂ => inner ℂ x.1 y.1)
      id (fun x => (x.1, x.2 + x.1)) := fun _ _ => rfl

/-- The complex conjugate partners have equal operator norms. -/
private theorem complex_I_smul_id_norm_eq :
    ‖Complex.I • ContinuousLinearMap.id ℂ ℂ‖ =
      ‖-Complex.I • ContinuousLinearMap.id ℂ ℂ‖ :=
  Complex.isAdjointPair_I_smul_id.norm_eq

universe u v w

/-- Pairwise-distance transport recovers convergence along an isometric target map. -/
private theorem isometry_tendsto_nhds_iff {X : Type u} {Y : Type v} {Z : Type w}
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {e : Y → Z} (he : Isometry e)
    (f : X → Y) {l : Filter X} {x : X} :
    Filter.Tendsto (e ∘ f) l (nhds (e (f x))) ↔ Filter.Tendsto f l (nhds (f x)) :=
  Metric.tendsto_nhds_iff_of_pairwise_dist_eq fun a b => he.dist_eq (f a) (f b)

-- The bilinear bridge accepts functions without bundled linear-map structures.
example {R : Type*} {E : Type*} {F : Type*}
    [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
    (B₁ : E →ₗ[R] E →ₗ[R] R) (B₂ : F →ₗ[R] F →ₗ[R] R)
    (f : E → F) (g : F → E) :
    LinearMap.IsAdjointPair B₁ B₂ f g ↔
      Function.IsAdjointPair (fun x y => B₁ x y) (fun x y => B₂ x y) f g :=
  LinearMap.isAdjointPair_iff_function B₁ B₂ f g
