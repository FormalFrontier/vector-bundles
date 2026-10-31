/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.Normed.Ring.Units

/-!
# Inverse continuity within supplied units

In a seminormed ring, convergence of the forward values of supplied units implies
convergence of their inverse values. Consequently ring inversion preserves convergence
to a unit along any filter on which the arguments are eventually units. This asserts
neither openness of the unit locus nor existence of an ambient unit neighborhood.

For a normed ring with summable geometric series, `Units.nhds` supplies the eventual-unit
hypothesis of `Ring.continuousAt_inverse_of_eventually_isUnit`, recovering the conclusion
of `NormedRing.inverse_continuousAt`. The filter statement isolates the seminormed-ring
generality of the inverse-continuity step.
-/

@[expose] public section

noncomputable section

open Filter Topology

universe uR uX

namespace Units

/-- Forward convergence of supplied units suffices for convergence of inverse values. -/
theorem tendsto_coe_inv_of_tendsto_coe {R : Type uR} [SeminormedRing R]
    {X : Type uX} {l : Filter X} {u : X → Rˣ} {u₀ : Rˣ}
    (h : Tendsto (fun x => (u x : R)) l (𝓝 (u₀ : R))) :
    Tendsto (fun x => (((u x)⁻¹ : Rˣ) : R)) l (𝓝 ((u₀⁻¹ : Rˣ) : R)) := by
  have hu : Tendsto u l (𝓝 u₀) :=
    isEmbedding_val_seminormedRing.tendsto_nhds_iff.mpr h
  have hi : Continuous (fun v : Rˣ => ((v⁻¹ : Rˣ) : R)) := by fun_prop
  exact (hi.tendsto u₀).comp hu

end Units

namespace Ring

variable {R : Type uR} [SeminormedRing R]

/-- Inversion preserves convergence to a unit when the arguments are eventually units. -/
theorem tendsto_inverse_of_eventually_isUnit {X : Type uX} {l : Filter X}
    {f : X → R} {a : R} (hf : Tendsto f l (𝓝 a)) (ha : IsUnit a)
    (hunit : ∀ᶠ x in l, IsUnit (f x)) :
    Tendsto (fun x => inverse (f x)) l (𝓝 (inverse a)) := by
  classical
  let u₀ : Rˣ := ha.unit
  let u : X → Rˣ := fun x => if h : IsUnit (f x) then h.unit else u₀
  have hu : (fun x => (u x : R)) =ᶠ[l] f :=
    hunit.mono fun x hx => by simp only [u, dite_eq_left hx, hx.unit_spec]
  have hval : Tendsto (fun x => (u x : R)) l (𝓝 (u₀ : R)) := by
    simpa only [u₀, ha.unit_spec] using hf.congr' hu.symm
  have hinv := Units.tendsto_coe_inv_of_tendsto_coe hval
  have heq : (fun x => inverse (f x)) =ᶠ[l] (fun x => (((u x)⁻¹ : Rˣ) : R)) :=
    hu.mono fun x hx => (congrArg inverse hx).symm.trans (inverse_unit (u x))
  simpa only [← inverse_unit, u₀, ha.unit_spec] using hinv.congr' heq.symm

/-- Ambient continuity of inversion under a supplied eventual-unit hypothesis. -/
theorem continuousAt_inverse_of_eventually_isUnit {a : R} (ha : IsUnit a)
    (hunit : ∀ᶠ x in 𝓝 a, IsUnit x) : ContinuousAt inverse a :=
  tendsto_inverse_of_eventually_isUnit continuousAt_id ha hunit

/-- Ring inversion is continuous at a unit within the unit locus. -/
theorem continuousWithinAt_inverse_units {a : R} (ha : IsUnit a) :
    ContinuousWithinAt inverse {x : R | IsUnit x} a :=
  tendsto_inverse_of_eventually_isUnit continuousWithinAt_id ha self_mem_nhdsWithin

/-- Ring inversion is continuous on the unit locus, without an openness assumption. -/
theorem continuousOn_inverse_units : ContinuousOn (inverse : R → R) {x : R | IsUnit x} :=
  fun _ ha => continuousWithinAt_inverse_units ha

end Ring
