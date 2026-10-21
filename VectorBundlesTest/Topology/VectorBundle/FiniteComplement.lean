/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteComplement
public import Mathlib.Topology.UnitInterval

/-!
# Clients of finite complementary bundles

The positive-rank trivial real line over the unit interval uses the chosen complement's
bundle structures and global linear trivialization. Its complement has a continuous zero
section. The vector `(1, 0)` has nonzero image,
its base point is preserved, and its image recovers the original vector under the inverse
fiberwise linear equivalence. The rank-zero case has zero complementary fibers.

The namespace `VectorBundle.RealLineComplement` provides the chosen bundle structures
and trivialization, with continuity, full-base, nonzero-image and base-preservation laws.
Use `open scoped VectorBundle.RealLineComplement` to activate its four bundle and
linearity instances. The whole-object equality `realLineTrivialization_eq` identifies
the trivialization with the finite-complement construction, including its inverse interface.

The complement is constructed from finite model powers.
-/

noncomputable section

namespace VectorBundle.RealLineComplement

open Bundle

local notation "C" => VectorBundle.finiteComplement.fiber ℝ ℝ (Bundle.Trivial unitInterval ℝ)
local notation "G" => VectorBundle.finiteComplement.model ℝ ℝ (Bundle.Trivial unitInterval ℝ)

/-- The total-space topology of the chosen complement to the real line over the unit interval. -/
public scoped instance realLineComplementTopology : TopologicalSpace (TotalSpace G C) :=
  VectorBundle.finiteComplement.totalSpaceTopology ℝ ℝ (Bundle.Trivial unitInterval ℝ)
attribute [local instance] realLineComplementTopology

/-- The fiber bundle structure of the chosen complement to the real line over the unit interval. -/
public scoped instance realLineComplementFiberBundle : FiberBundle G C :=
  VectorBundle.finiteComplement.fiberBundle ℝ ℝ (Bundle.Trivial unitInterval ℝ)
attribute [local instance] realLineComplementFiberBundle

/-- The real vector bundle structure of the chosen complement over the unit interval. -/
public scoped instance realLineComplementVectorBundle : VectorBundle ℝ G C :=
  VectorBundle.finiteComplement.vectorBundle ℝ ℝ (Bundle.Trivial unitInterval ℝ)
attribute [local instance] realLineComplementVectorBundle

/-- The zero section of the chosen complementary bundle over the unit interval is continuous. -/
public theorem realLineComplement_zeroSection_continuous : Continuous (zeroSection G C) :=
  Bundle.Trivialization.continuous_zeroSection ℝ

/-- The global trivialization of the real line together with its chosen complementary bundle. -/
@[expose] public def realLineTrivialization :
    Trivialization (ℝ × G) (π (ℝ × G) (Bundle.Trivial unitInterval ℝ ×ᵇ C)) :=
  VectorBundle.finiteComplement.trivialization ℝ ℝ (Bundle.Trivial unitInterval ℝ)

/-- The global trivialization of the real line and its complement is fiberwise real-linear. -/
public scoped instance realLineTrivializationIsLinear : realLineTrivialization.IsLinear ℝ :=
  VectorBundle.finiteComplement.trivialization_isLinear ℝ ℝ (Bundle.Trivial unitInterval ℝ)
attribute [local instance] realLineTrivializationIsLinear

/-- The real-line trivialization equals the finite-complement construction's trivialization.

This whole-object equality also identifies its inverse map and partial-equivalence laws. -/
public theorem realLineTrivialization_eq :
    @Eq
      (@Trivialization unitInterval (ℝ × G) _ _ _
        (@FiberBundle.Prod.topologicalSpace unitInterval ℝ
          (Bundle.Trivial unitInterval ℝ) G C
          inferInstance realLineComplementTopology)
        (π (ℝ × G) (Bundle.Trivial unitInterval ℝ ×ᵇ C)))
      realLineTrivialization
      (VectorBundle.finiteComplement.trivialization ℝ ℝ
        (Bundle.Trivial unitInterval ℝ)) := rfl

/-- The trivialization of the real line and its complement is defined over the whole
unit interval. -/
public theorem realLineTrivialization_fullBase : realLineTrivialization.baseSet = Set.univ :=
  VectorBundle.finiteComplement.trivialization_baseSet ℝ ℝ (Bundle.Trivial unitInterval ℝ)

/-- The vector `(1, 0)` has nonzero image in the model of the real line and its complement. -/
public theorem realLine_image_ne_zero (b : unitInterval) :
    (realLineTrivialization ⟨b, (1, 0)⟩).2 ≠ 0 := by
  let e := realLineTrivialization.linearEquivAt ℝ b
    (by simp only [realLineTrivialization_fullBase, Set.mem_univ])
  intro h
  have hz : e (1, 0) = e 0 := by
    simpa only [e, map_zero, Trivialization.linearEquivAt_apply] using h
  have hv := congrArg Prod.fst (e.injective hz)
  exact one_ne_zero hv

/-- The trivialization of the real line and its complement preserves the base point of `(1, 0)`. -/
public theorem realLine_image_base (b : unitInterval) :
    (realLineTrivialization ⟨b, (1, 0)⟩).1 = b :=
  realLineTrivialization.coe_fst' (by simp only [realLineTrivialization_fullBase, Set.mem_univ])

private theorem realLine_image_inverse (b : unitInterval) :
    (realLineTrivialization.linearEquivAt ℝ b
      (by simp only [realLineTrivialization_fullBase, Set.mem_univ])).symm
      (realLineTrivialization ⟨b, (1, 0)⟩).2 = (1, 0) := by
  exact (realLineTrivialization.linearEquivAt ℝ b
    (by simp only [realLineTrivialization_fullBase, Set.mem_univ])).symm_apply_apply (1, 0)

private def rankZeroComplement (b : unitInterval) :
    Submodule ℝ (Fin (VectorBundle.finiteComplement.count ℝ (Fin 0 → ℝ)
      (Bundle.Trivial unitInterval (Fin 0 → ℝ))) → (Fin 0 → ℝ)) :=
  VectorBundle.finiteComplement.submodule ℝ (Fin 0 → ℝ)
    (Bundle.Trivial unitInterval (Fin 0 → ℝ)) b

private theorem rankZeroComplement_eq_bot (b : unitInterval) : rankZeroComplement b = ⊥ :=
  Subsingleton.elim _ _

end VectorBundle.RealLineComplement
