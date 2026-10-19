/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Bounded unit sublevels of positive forms

In finite dimension, the open unit sublevel of a positive-definite inner product is
von Neumann bounded for any vector-space topology. No compatibility with a previously
chosen norm is required. The proof uses Mathlib's norm induced by an
`InnerProductSpace.Core`, the finite-dimensional module topology theorem, and
`Bornology.IsVonNBounded.of_topologicalSpace_le`.

For topological vector spaces presented by a continuous linear equivalence with a normed
model, `ContinuousLinearMap.isVonNBounded_re_unit_sublevel_of_equiv` applies directly to a
positive-definite Hermitian form over an `RCLike` field. In particular, the target need not
carry a norm or a jointly continuous scalar action. The real specialization is
`ContinuousLinearMap.isVonNBounded_unit_sublevel_of_equiv`. Continuity of the diagonal is a
separate issue from boundedness and is not a hypothesis of these results.

## Credits

The norm and topology constructions reused here are from Mathlib's
`Analysis.InnerProductSpace.Defs` and `Topology.Algebra.Module.FiniteDimension`.
-/

@[expose] public section

open Bornology
open scoped ComplexConjugate

namespace InnerProductSpace.Core

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F]
  [tF : TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The open unit sublevel of a positive-definite inner product on a finite-dimensional
vector space is von Neumann bounded in any vector-space topology. Neither Hausdorffness
nor continuity of the given inner product is needed. -/
theorem isVonNBounded_unit_sublevel (c : InnerProductSpace.Core 𝕜 F) :
    IsVonNBounded 𝕜 {v : F | RCLike.re (c.inner v v) < 1} := by
  have ht : moduleTopology 𝕜 F ≤ tF := moduleTopology_le 𝕜 F
  let := c
  let : NormedAddCommGroup F := c.toNormedAddCommGroup
  let : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  let : TopologicalSpace F := c.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  have htop : (inferInstance : TopologicalSpace F) = moduleTopology 𝕜 F := by
    let := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := F)
    exact eq_moduleTopology 𝕜 F
  refine IsVonNBounded.of_topologicalSpace_le (htop.trans_le ht) ?_
  have hball : Metric.ball (0 : F) 1 = {v : F | RCLike.re (c.inner v v) < 1} := by
    ext v
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, Set.mem_ofPred_eq]
    change √(RCLike.re (c.inner v v)) < 1 ↔ RCLike.re (c.inner v v) < 1
    simpa using Real.sqrt_lt_sqrt_iff (InnerProductSpace.Core.inner_self_nonneg
      (𝕜 := 𝕜) (x := v)) (y := (1 : ℝ))
  rw [← hball]
  exact NormedSpace.isVonNBounded_ball 𝕜 F 1

end InnerProductSpace.Core

namespace ContinuousLinearMap

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A positive-definite Hermitian form has a von Neumann bounded open unit sublevel of the
real part of its diagonal whenever its domain is continuously linearly equivalent to a
finite-dimensional normed space. No norm or joint continuity of scalar multiplication on the
domain is assumed. -/
theorem isVonNBounded_re_unit_sublevel_of_equiv (q : F →L⋆[𝕜] F →L[𝕜] 𝕜)
    (hsymm : ∀ v w, conj (q w v) = q v w)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (q v v))
    (e : E ≃L[𝕜] F) : IsVonNBounded 𝕜 {v : F | RCLike.re (q v v) < 1} := by
  let c : InnerProductSpace.Core 𝕜 E :=
    { inner := fun v w => q (e v) (e w)
      conj_inner_symm := fun v w => hsymm (e v) (e w)
      re_inner_nonneg := fun v => by
        by_cases hv : e v = 0
        · simp [hv]
        · exact (hpos (e v) hv).le
      add_left := fun v w x => by simp
      smul_left := fun v w r => by simp
      definite := fun v hv => by
        apply e.injective
        by_contra h
        have hne : e v ≠ 0 := by simpa using h
        have := hpos (e v) hne
        simp only [hv, map_zero, lt_self_iff_false] at this }
  have h := c.isVonNBounded_unit_sublevel.image e.toContinuousLinearMap
  convert h using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change RCLike.re (q (e (e.symm v)) (e (e.symm v))) < 1
    simpa only [e.apply_symm_apply] using hv
  · rintro ⟨w, hw, rfl⟩
    exact hw

/-- The open unit sublevel of the real part of the diagonal of a positive-definite continuous
Hermitian form on a finite-dimensional normed space is von Neumann bounded. The ambient norm
need not be the norm induced by the form. -/
theorem isVonNBounded_re_unit_sublevel_of_posDef (q : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (hsymm : ∀ v w, conj (q w v) = q v w)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (q v v)) :
    IsVonNBounded 𝕜 {v : E | RCLike.re (q v v) < 1} :=
  q.isVonNBounded_re_unit_sublevel_of_equiv hsymm hpos (.refl 𝕜 E)

end RCLike

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A symmetric positive-definite real bilinear form has a von Neumann bounded open unit
sublevel whenever its domain is continuously linearly equivalent to a finite-dimensional
normed space. No norm or joint continuity of scalar multiplication on the domain is assumed. -/
theorem isVonNBounded_unit_sublevel_of_equiv (q : F →L[ℝ] F →L[ℝ] ℝ)
    (hsymm : ∀ v w, q v w = q w v) (hpos : ∀ v, v ≠ 0 → 0 < q v v)
    (e : E ≃L[ℝ] F) : IsVonNBounded ℝ {v : F | q v v < 1} :=
  q.isVonNBounded_re_unit_sublevel_of_equiv (fun v w => hsymm w v) hpos e

/-- The open unit sublevel of a symmetric positive-definite continuous bilinear form on a
finite-dimensional real normed space is von Neumann bounded. The ambient norm need not
be the norm induced by the form. -/
theorem isVonNBounded_unit_sublevel_of_posDef (q : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w, q v w = q w v) (hpos : ∀ v, v ≠ 0 → 0 < q v v) :
    IsVonNBounded ℝ {v : E | q v v < 1} :=
  q.isVonNBounded_re_unit_sublevel_of_posDef (fun v w => hsymm w v) hpos

end Real

end ContinuousLinearMap
