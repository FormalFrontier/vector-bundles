/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import VectorBundles.Topology.ContinuousMap.WeightedExtension
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic

/-!
# Weighted maps and pairings on subsets

A continuous scalar weight has its closed cozero support inside a subset carrying
a continuous target-valued map. The propositions retain weighted values on the
subset and zero values off it, and compare a closed scalar zero singleton, a T1
scalar space, and no scalar separation assumption. The source, scalar and target
have independent universes and their supplied topologies.

A real module supplies a scalar action with zero. More generally, a continuous
pairing that is constant at a distinguished first input admits an extension
with that constant value off the subset. The second input and the output may
have different carriers, with independently supplied topologies.
-/

@[expose] public section

open Set

namespace ContinuousMap

universe uX uR uV uW

/-- Closed-set pasting extends a weighted map when the scalar zero singleton is closed. -/
theorem exists_smul_extension_of_isClosed_zero
    {X : Type uX} {R : Type uR} {V : Type uV}
    [TopologicalSpace X] [TopologicalSpace R] [TopologicalSpace V]
    [Zero R] [Zero V] [SMulWithZero R V] [ContinuousSMul R V]
    (hzero : IsClosed ({0} : Set R))
    {U : Set X} (w : C(X, R))
    (hsupport : closure {x : X | w x ≠ 0} ⊆ U) (g : C(U, V)) :
    ∃ G : C(X, V),
      (∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩) ∧
      (∀ x : X, x ∉ U → G x = 0) := by
  classical
  let F : X → V := fun x ↦ if hx : x ∈ U then w x • g ⟨x, hx⟩ else 0
  let C : Set X := closure {x | w x ≠ 0}
  let Z : Set X := w ⁻¹' {0}
  have hC : ContinuousOn F C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous (fun x : C ↦ g ⟨x, hsupport x.property⟩) :=
      g.continuous.comp (continuous_subtype_val.subtype_mk (fun x ↦ hsupport x.property))
    convert (w.continuous.comp continuous_subtype_val).smul hg using 1
    funext x
    simp [F, hsupport x.property]
  have hZ : ContinuousOn F Z := by
    refine (continuousOn_const : ContinuousOn (fun _ : X ↦ (0 : V)) Z).congr ?_
    intro x hx
    have hw : w x = 0 := hx
    by_cases hU : x ∈ U <;> simp [F, hU, hw]
  have cover : C ∪ Z = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hw : w x = 0
    · exact Or.inr hw
    · exact Or.inl (subset_closure hw)
  have hF : Continuous F :=
    continuousOn_univ.mp (cover ▸ hC.union_of_isClosed hZ isClosed_closure
      (hzero.preimage w.continuous))
  refine ⟨⟨F, hF⟩, ?_, ?_⟩
  · intro x hx
    simp [F, hx]
  · intro x hx
    simp [F, hx]

example
    {X : Type uX} {R : Type uR} {V : Type uV}
    [TopologicalSpace X] [TopologicalSpace R] [TopologicalSpace V]
    [Zero R] [Zero V] [SMulWithZero R V] [ContinuousSMul R V]
    [T1Space R]
    {U : Set X} (w : C(X, R))
    (hsupport : closure {x : X | w x ≠ 0} ⊆ U) (g : C(U, V)) :
    ∃ G : C(X, V),
      (∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩) ∧
      (∀ x : X, x ∉ U → G x = 0) :=
  exists_smul_extension_of_isClosed_zero isClosed_singleton w hsupport g

example
    {X : Type uX} {R : Type uR} {V : Type uV}
    [TopologicalSpace X] [TopologicalSpace R] [TopologicalSpace V]
    [Zero R] [Zero V] [SMulWithZero R V] [ContinuousSMul R V]
    {U : Set X} (w : C(X, R))
    (hsupport : closure {x : X | w x ≠ 0} ⊆ U) (g : C(U, V)) :
    ∃ G : C(X, V),
      (∀ (x : X) (hx : x ∈ U), G x = w x • g ⟨x, hx⟩) ∧
      (∀ x : X, x ∉ U → G x = 0) :=
  ContinuousMap.exists_smul_extension w hsupport g

example {V : Type uV} [AddCommMonoid V] [Module ℝ V] : SMulWithZero ℝ V :=
  inferInstance

example
    {X : Type uX} {M : Type uR} {V : Type uV} {W : Type uW}
    [TopologicalSpace X] [TopologicalSpace M]
    [TopologicalSpace V] [TopologicalSpace W]
    (μ : C(M × V, W)) (m₀ : M) (w₀ : W)
    (hμ : ∀ v : V, μ (m₀, v) = w₀)
    {U : Set X} (w : C(X, M))
    (hsupport : closure {x : X | w x ≠ m₀} ⊆ U) (g : C(U, V)) :
    ∃ G : C(X, W),
      (∀ (x : X) (hx : x ∈ U), G x = μ (w x, g ⟨x, hx⟩)) ∧
      (∀ x : X, x ∉ U → G x = w₀) :=
  ContinuousMap.exists_pairing_extension μ m₀ w₀ hμ w hsupport g

end ContinuousMap
