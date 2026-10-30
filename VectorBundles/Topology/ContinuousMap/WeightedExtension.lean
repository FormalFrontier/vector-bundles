/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.ContinuousMap.PairingExtension
public import Mathlib.Topology.Algebra.MulAction

/-!
# Zero extension of weighted maps

A continuous scalar action with zero specializes the constant pairing extension.
`ContinuousMap.smulExtend` extends `w x • g x` by zero from an arbitrary subset
containing the closure of `{x | w x ≠ 0}`. No separation, additive continuity,
boundedness, or openness assumptions are needed.

In particular this applies to real modules with a continuous scalar action,
without a norm on the module. The weighted chart coordinates used in finite
bundle embeddings are a consumer of this construction.
-/

@[expose] public section

open Set

universe uX uR uV

namespace ContinuousMap

variable {X : Type uX} {R : Type uR} {V : Type uV}
variable [TopologicalSpace X] [TopologicalSpace R] [TopologicalSpace V]
variable [Zero R] [Zero V] [SMulWithZero R V] [ContinuousSMul R V]

/-- Extend a weighted map by zero when its weight's closed cozero support lies
in its domain. The domain may be any subset. -/
noncomputable def smulExtend {U : Set X} (w : C(X, R))
    (hsupport : closure {x | w x ≠ 0} ⊆ U) (g : C(U, V)) : C(X, V) :=
  pairingExtend ⟨fun p : R × V ↦ p.1 • p.2, continuous_fst.smul continuous_snd⟩
    0 0 (fun _ ↦ zero_smul R _) w hsupport g

variable {U : Set X} (w : C(X, R)) (hsupport : closure {x | w x ≠ 0} ⊆ U) (g : C(U, V))

/-- On the subset, the zero extension is the weighted map. -/
@[simp] theorem smulExtend_apply_of_mem (x : X) (hx : x ∈ U) :
    w.smulExtend hsupport g x = w x • g ⟨x, hx⟩ := by
  exact pairingExtend_apply_of_mem _ _ _ _ _ _ _ x hx

/-- Away from the subset, the zero extension vanishes. -/
@[simp] theorem smulExtend_apply_of_notMem (x : X) (hx : x ∉ U) :
    w.smulExtend hsupport g x = 0 := by
  exact pairingExtend_apply_of_notMem _ _ _ _ _ _ _ x hx

/-- The extension vanishes wherever the weight vanishes, including inside its domain. -/
theorem smulExtend_apply_of_eq_zero (x : X) (hx : w x = 0) :
    w.smulExtend hsupport g x = 0 := by
  exact pairingExtend_apply_of_eq _ _ _ _ _ _ _ x hx

/-- The on-domain weighted values and off-domain zeros characterize the extension. -/
theorem smulExtend_unique (G : C(X, V))
    (hin : ∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩)
    (hout : ∀ x : X, x ∉ U → G x = 0) : G = w.smulExtend hsupport g := by
  exact pairingExtend_unique _ _ _ _ _ _ _ G hin hout

/-- An extensional characterization of the zero extension by its values on both pieces. -/
theorem eq_smulExtend_iff (G : C(X, V)) :
    G = w.smulExtend hsupport g ↔
      (∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩) ∧
      (∀ x : X, x ∉ U → G x = 0) := by
  exact eq_pairingExtend_iff _ _ _ _ _ _ _ G

include hsupport in
/-- A map weighted by a continuous scalar function extends continuously by zero
from any subset containing the weight's closed cozero support. -/
theorem exists_smul_extension :
    ∃ G : C(X, V),
      (∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩) ∧
      (∀ x : X, x ∉ U → G x = 0) :=
  ⟨w.smulExtend hsupport g, smulExtend_apply_of_mem w hsupport g,
    smulExtend_apply_of_notMem w hsupport g⟩

end ContinuousMap
