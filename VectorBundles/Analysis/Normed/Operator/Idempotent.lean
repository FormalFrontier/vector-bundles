/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Ring.Idempotent
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Transport and rank stability for close idempotent operators

A single normalized unit transports both ranges and kernels when geometric series
are summable in the endomorphism algebra. Cardinal rank stability uses only linear
injections under the norm bound. Thus rank equality and local constancy need no
geometric-summability or completeness hypothesis.
-/

open Filter
open scoped Topology

universe uK uE uX

public section

variable {K : Type uK} {E : Type uE} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Close idempotents admit range and kernel equivalences induced by the same
normalized unit, with its ambient action and inverse action on both submodules. -/
theorem IsIdempotentElem.exists_unit_range_ker_equiv_of_norm_sub_lt_one
    [HasSummableGeomSeries (E →L[K] E)] {p q : E →L[K] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    ∃ u : (E →L[K] E)ˣ,
      (u : E →L[K] E) = q * p + (1 - q) * (1 - p) ∧
      (u : E →L[K] E) * p = q * (u : E →L[K] E) ∧
      (u : E →L[K] E) * p * (↑u⁻¹ : E →L[K] E) = q ∧
      ∃ (R : p.toLinearMap.range ≃L[K] q.toLinearMap.range)
        (N : p.toLinearMap.ker ≃L[K] q.toLinearMap.ker),
        (∀ x : p.toLinearMap.range, (R x : E) = (u : E →L[K] E) (x : E)) ∧
        (∀ y : q.toLinearMap.range,
          (R.symm y : E) = (↑u⁻¹ : E →L[K] E) (y : E)) ∧
        (∀ x : p.toLinearMap.ker, (N x : E) = (u : E →L[K] E) (x : E)) ∧
        (∀ y : q.toLinearMap.ker,
          (N.symm y : E) = (↑u⁻¹ : E →L[K] E) (y : E)) := by
  obtain ⟨u, hu, hcomm, hconj⟩ := hp.exists_unit_conj_eq_of_norm_sub_lt_one hq h
  let w : E →L[K] E := (u : E →L[K] E)
  let v : E →L[K] E := (↑u⁻¹ : E →L[K] E)
  have hwv (x : E) : w (v x) = x := by
    have hx := congrArg (fun f : E →L[K] E => f x)
      (show w * v = 1 by simp [w, v])
    simpa only [mul_apply_eq_comp,
      one_apply_eq_self] using hx
  have hvw (x : E) : v (w x) = x := by
    have hx := congrArg (fun f : E →L[K] E => f x)
      (show v * w = 1 by simp [w, v])
    simpa only [mul_apply_eq_comp,
      one_apply_eq_self] using hx
  have hwp (x : E) : w (p x) = q (w x) := by
    have hx := congrArg (fun f : E →L[K] E => f x) hcomm
    simpa only [mul_apply_eq_comp] using hx
  have hpv (x : E) : p (v x) = v (q x) := by
    calc
      p (v x) = v (w (p (v x))) := (hvw (p (v x))).symm
      _ = v (q (w (v x))) := congrArg v (hwp (v x))
      _ = v (q x) := by rw [hwv x]
  have hwker (x : p.toLinearMap.ker) : q (w (x : E)) = 0 := by
    calc
      q (w (x : E)) = w (p (x : E)) := (hwp (x : E)).symm
      _ = w 0 := congrArg w (show p (x : E) = 0 from x.property)
      _ = 0 := map_zero w
  have hvker (y : q.toLinearMap.ker) : p (v (y : E)) = 0 := by
    calc
      p (v (y : E)) = v (q (y : E)) := hpv (y : E)
      _ = v 0 := congrArg v (show q (y : E) = 0 from y.property)
      _ = 0 := map_zero v
  let N : p.toLinearMap.ker ≃L[K] q.toLinearMap.ker :=
    { toFun := fun x => ⟨w (x : E), hwker x⟩
      invFun := fun y => ⟨v (y : E), hvker y⟩
      left_inv := fun x => Subtype.ext (hvw (x : E))
      right_inv := fun y => Subtype.ext (hwv (y : E))
      map_add' := fun x y => Subtype.ext (map_add w (x : E) (y : E))
      map_smul' := fun a x => Subtype.ext (map_smul w a (x : E))
      continuous_toFun :=
        (w.continuous.comp continuous_subtype_val).subtype_mk hwker
      continuous_invFun :=
        (v.continuous.comp continuous_subtype_val).subtype_mk hvker }
  have forward_mem (x : p.toLinearMap.range) : w (x : E) ∈ q.toLinearMap.range := by
    rcases x.property with ⟨a, ha⟩
    refine ⟨w a, ?_⟩
    exact (hwp a).symm.trans (congrArg w ha)
  have inverse_mem (y : q.toLinearMap.range) : v (y : E) ∈ p.toLinearMap.range := by
    rcases y.property with ⟨a, ha⟩
    refine ⟨v a, ?_⟩
    exact (hpv a).trans (congrArg v ha)
  let R : p.toLinearMap.range ≃L[K] q.toLinearMap.range :=
    { toFun := fun x => ⟨w (x : E), forward_mem x⟩
      invFun := fun y => ⟨v (y : E), inverse_mem y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact hvw (x : E)
      right_inv := by
        intro y
        apply Subtype.ext
        exact hwv (y : E)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add w (x : E) (y : E)
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact map_smul w c (x : E)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact w.continuous.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact v.continuous.comp continuous_subtype_val }
  exact ⟨u, hu, hcomm, hconj, R, N, (fun _ ↦ rfl), (fun _ ↦ rfl),
    (fun _ ↦ rfl), (fun _ ↦ rfl)⟩

private lemma IsIdempotentElem.rank_range_le_of_norm_sub_lt_one
    {K : Type uK} {E : Type uE} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {p q : E →L[K] E} (hp : IsIdempotentElem p) (hpq : ‖p - q‖ < 1) :
    Module.rank K p.toLinearMap.range ≤ Module.rank K q.toLinearMap.range := by
  have hpp : p * p = p := isIdempotentElem_iff.mp hp
  let f : p.toLinearMap.range →ₗ[K] q.toLinearMap.range :=
    { toFun := fun x ↦ ⟨q (x : E), ⟨(x : E), rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact q.map_add (x : E) (y : E)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact q.map_smul a (x : E) }
  have hpfix : ∀ z : p.toLinearMap.range, p (z : E) = (z : E) := by
    intro z
    obtain ⟨w, hw⟩ := z.property
    change p w = (z : E) at hw
    have hppw : p (p w) = p w := congrArg (fun r : E →L[K] E ↦ r w) hpp
    calc
      p (z : E) = p (p w) := congrArg p hw.symm
      _ = p w := hppw
      _ = (z : E) := hw
  apply LinearMap.rank_le_of_injective f
  intro x y hxy
  have hq : q (x : E) = q (y : E) :=
    congrArg (fun z : q.toLinearMap.range ↦ (z : E)) hxy
  have hqxy : q ((x : E) - (y : E)) = 0 := by
    rw [map_sub, hq, sub_self]
  have hdiff : (p - q) ((x : E) - (y : E)) = (x : E) - (y : E) := by
    change p ((x : E) - (y : E)) - q ((x : E) - (y : E)) = (x : E) - (y : E)
    rw [p.map_sub, hpfix x, hpfix y, hqxy, sub_zero]
  have hnorm : ‖(x : E) - (y : E)‖ ≤ ‖p - q‖ * ‖(x : E) - (y : E)‖ := by
    calc
      ‖(x : E) - (y : E)‖ = ‖(p - q) ((x : E) - (y : E))‖ :=
        congrArg norm hdiff.symm
      _ ≤ ‖p - q‖ * ‖(x : E) - (y : E)‖ := (p - q).le_opNorm _
  have hzero : (x : E) - (y : E) = 0 := by
    by_contra hne
    have hpos : 0 < ‖(x : E) - (y : E)‖ := norm_pos_iff.mpr hne
    have hlt : ‖p - q‖ * ‖(x : E) - (y : E)‖ < ‖(x : E) - (y : E)‖ := by
      calc
        _ < 1 * ‖(x : E) - (y : E)‖ := mul_lt_mul_of_pos_right hpq hpos
        _ = _ := one_mul _
    exact (not_lt_of_ge hnorm) hlt
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

private theorem idempotent_complement {p : E →L[K] E} (hp : IsIdempotentElem p) :
    IsIdempotentElem (1 - p) := by
  apply isIdempotentElem_iff.mpr
  have hp2 : p * p = p := isIdempotentElem_iff.mp hp
  rw [sub_mul, one_mul, mul_sub, mul_one, hp2, sub_self, sub_zero]

private theorem idempotent_toLinearMap {p : E →L[K] E} (hp : IsIdempotentElem p) :
    IsIdempotentElem p.toLinearMap := by
  apply isIdempotentElem_iff.mpr
  exact congrArg (fun f : E →L[K] E ↦ f.toLinearMap) (isIdempotentElem_iff.mp hp)

/-- Both cardinal module ranks are stable under a perturbation of norm less than one. -/
theorem IsIdempotentElem.rank_range_ker_eq_of_norm_sub_lt_one
    {p q : E →L[K] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    Module.rank K p.toLinearMap.range = Module.rank K q.toLinearMap.range ∧
      Module.rank K p.toLinearMap.ker = Module.rank K q.toLinearMap.ker := by
  have hrev : ‖q - p‖ < 1 := by
    rw [norm_sub_rev]
    exact h
  constructor
  · exact le_antisymm (hp.rank_range_le_of_norm_sub_lt_one h)
      (hq.rank_range_le_of_norm_sub_lt_one hrev)
  · have hcomp : ‖(1 - p) - (1 - q)‖ < 1 := by
      simpa only [sub_sub_sub_cancel_left] using hrev
    have hcomprev : ‖(1 - q) - (1 - p)‖ < 1 := by
      rw [norm_sub_rev]
      exact hcomp
    have hN := le_antisymm
      ((idempotent_complement hp).rank_range_le_of_norm_sub_lt_one hcomp)
      ((idempotent_complement hq).rank_range_le_of_norm_sub_lt_one hcomprev)
    have hp_rank := congrArg (fun S : Submodule K E ↦ Module.rank K S)
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub (idempotent_toLinearMap hp)).symm
    have hq_rank := congrArg (fun S : Submodule K E ↦ Module.rank K S)
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub (idempotent_toLinearMap hq)).symm
    exact hp_rank.symm.trans (hN.trans hq_rank)

/-- A continuous family of idempotents has locally constant range and kernel cardinal ranks. -/
theorem Continuous.isLocallyConstant_rank_range_ker
    {X : Type uX} [TopologicalSpace X]
    {P : X → (E →L[K] E)} (hP : Continuous P) (hidem : ∀ x, IsIdempotentElem (P x)) :
    IsLocallyConstant (fun x ↦ Module.rank K (P x).toLinearMap.range) ∧
      IsLocallyConstant (fun x ↦ Module.rank K (P x).toLinearMap.ker) := by
  have heq (x : X) : ∀ᶠ y in 𝓝 x,
      Module.rank K (P y).toLinearMap.range = Module.rank K (P x).toLinearMap.range ∧
      Module.rank K (P y).toLinearMap.ker = Module.rank K (P x).toLinearMap.ker := by
    filter_upwards [hP.continuousAt.eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))] with y hy
    have hnorm : ‖P y - P x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    exact (hidem y).rank_range_ker_eq_of_norm_sub_lt_one (hidem x) hnorm
  exact ⟨(IsLocallyConstant.iff_eventually_eq _).2
      (fun x ↦ (heq x).mono fun _ h ↦ h.1),
    (IsLocallyConstant.iff_eventually_eq _).2
      (fun x ↦ (heq x).mono fun _ h ↦ h.2)⟩
