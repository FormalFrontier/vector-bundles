/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Module topologies on retracts

A continuous linear retract of a module with the module topology has the module topology.
The continuous section need not be linear. In particular, the subtype topology on the range
of an idempotent linear endomorphism is the module topology.

The construction uses Mathlib's module-topology universal property and its algebraic
projection and range-restriction APIs.

## Main results

* `IsModuleTopology.of_retract`: descent of the module topology along a continuous linear map
  with a continuous right inverse.
* `LinearMap.IsIdempotentElem.isModuleTopology_range`: the range of an idempotent linear
  endomorphism inherits the module topology.
-/

@[expose] public section

universe uR uA uB

namespace IsModuleTopology

variable {R : Type uR} [Semiring R] [TopologicalSpace R]
variable {A : Type uA} [AddCommMonoid A] [Module R A] [TopologicalSpace A]
variable {B : Type uB} [AddCommMonoid B] [Module R B] [TopologicalSpace B]
variable [IsModuleTopology R A]

/-- A continuous linear retract of a module with the module topology has the module topology.
The right inverse is only required to be continuous, not linear. No continuity assumptions on
the addition or scalar action on the target are needed. -/
theorem of_retract (r : A →L[R] B) (s : B → A) (hs : Continuous s)
    (hrs : Function.RightInverse s r) : IsModuleTopology R B := by
  let : ContinuousAdd A := toContinuousAdd R A
  have hrs' (b : B) : r (s b) = b := hrs b
  -- Freeze the algebraic map before comparing two topologies on its codomain.
  let rₗ : A →ₗ[R] B := r.toLinearMap
  have hrsₗ (b : B) : rₗ (s b) = b := hrs b
  -- Lift the target operations through the section, then apply the retraction.
  let : ContinuousAdd B := ⟨by
    have h : Continuous (fun bc : B × B ↦ r (s bc.1 + s bc.2)) :=
      r.continuous.comp ((hs.comp continuous_fst).add (hs.comp continuous_snd))
    simpa only [r.map_add, hrs'] using h⟩
  let : ContinuousSMul R B := ⟨by
    have h : Continuous (fun ab : R × B ↦ r (ab.1 • s ab.2)) :=
      r.continuous.comp (continuous_fst.smul (hs.comp continuous_snd))
    simpa only [r.map_smul, hrs'] using h⟩
  apply of_continuous_id (R := R) (A := B)
  -- Compare the given target topology with its canonical module topology.
  have hr : @Continuous A B ‹TopologicalSpace A› (moduleTopology R B) rₗ := by
    exact @continuous_of_linearMap R ‹TopologicalSpace R› ‹Semiring R›
      A ‹AddCommMonoid A› ‹Module R A› ‹TopologicalSpace A› ‹IsModuleTopology R A›
      B ‹AddCommMonoid B› ‹Module R B› (moduleTopology R B)
      (ModuleTopology.continuousAdd R B) (ModuleTopology.continuousSMul R B) rₗ
  exact @Continuous.congr B B ‹TopologicalSpace B› (moduleTopology R B)
    (rₗ ∘ s) id
    (@Continuous.comp B A B ‹TopologicalSpace B› ‹TopologicalSpace A›
      (moduleTopology R B) s rₗ hr hs) hrsₗ

end IsModuleTopology

namespace LinearMap

variable {R : Type uR} [Semiring R] [TopologicalSpace R]
variable {A : Type uA} [AddCommMonoid A] [Module R A] [TopologicalSpace A]
variable [IsModuleTopology R A]

/-- The subtype topology on the range of an idempotent linear endomorphism of a module
with the module topology is the module topology. Continuity of the endomorphism follows
from the module topology and is not an additional hypothesis. -/
theorem IsIdempotentElem.isModuleTopology_range {p : A →ₗ[R] A}
    (hp : IsIdempotentElem p) : IsModuleTopology R p.range := by
  let : ContinuousAdd A := IsModuleTopology.toContinuousAdd R A
  let pL : A →L[R] A := ⟨p, IsModuleTopology.continuous_of_linearMap p⟩
  let r : A →L[R] p.range := pL.rangeRestrict
  apply IsModuleTopology.of_retract r (p.range.subtypeL : p.range → A)
    p.range.subtypeL.continuous
  intro x
  apply Subtype.ext
  exact ((LinearMap.isProj_range_iff_isIdempotentElem p).2 hp).map_id x x.property

end LinearMap
