/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import VectorBundles.Analysis.Normed.Ring.CommutingIdempotent
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local constancy of commuting idempotents

A convergent family in a nonunital seminormed ring that is eventually idempotent
and eventually commutes with its limit eventually has difference of seminorm zero
from that limit. The filter may be bottom, and the limit need not be assumed
idempotent. The proof uses uniqueness of real limits for the seminorm of the
idempotence defect, not separation of the ring.

In a nonunital normed ring, separation turns the zero seminorm into equality.
Consequently, a continuous idempotent-valued map is locally constant if each of
its values commutes with nearby values eventually at that point. Pairwise
commutation of all values and separation of the domain are not required.
-/

@[expose] public section

open Filter
open scoped Topology

universe uR uI uX

variable {R : Type uR}

namespace Filter.Tendsto

/-- An eventually idempotent convergent family eventually has difference of
seminorm zero from its limit if it eventually commutes with the limit. Neither
idempotence of the limit nor a nonbottom filter is assumed. -/
theorem eventually_norm_sub_eq_zero_of_eventually_isIdempotentElem
    [NonUnitalSeminormedRing R] {I : Type uI} {L : Filter I} {u : I → R} {p : R}
    (hu : Tendsto u L (𝓝 p))
    (hid : ∀ᶠ i in L, IsIdempotentElem (u i))
    (hcomm : ∀ᶠ i in L, Commute (u i) p) :
    ∀ᶠ i in L, ‖u i - p‖ = 0 := by
  by_cases hL : L = ⊥
  · simp [hL]
  have : L.NeBot := ⟨hL⟩
  have hdefect : Tendsto (fun i => ‖u i * u i - u i‖) L (𝓝 ‖p * p - p‖) :=
    ((hu.mul hu).sub hu).norm
  have hzero : ∀ᶠ i in L, ‖u i * u i - u i‖ = (0 : ℝ) := by
    filter_upwards [hid] with i hi
    rw [show u i * u i = u i from hi, sub_self, norm_zero]
  have hdefect_zero : Tendsto (fun i => ‖u i * u i - u i‖) L (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hzero] with i hi
      exact hi.symm)
  have hpdefect : ‖p * p - p‖ = 0 :=
    tendsto_nhds_unique hdefect hdefect_zero
  have hsub : Tendsto (fun i => u i - p) L (𝓝 (p - p)) :=
    hu.sub tendsto_const_nhds
  have hnorm : Tendsto (fun i => ‖u i - p‖) L (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using hsub.norm
  have hsmall : ∀ᶠ i in L, ‖u i - p‖ < (1 : ℝ) :=
    (tendsto_order.mp hnorm).2 1 zero_lt_one
  filter_upwards [hid, hcomm, hsmall] with i hi hic hismall
  rcases hi.norm_sub_eq_zero_or_one_le_of_norm_mul_self_sub_eq_zero p hic hpdefect with
    hzero | hlarge
  · exact hzero
  · exact False.elim ((not_lt_of_ge hlarge) hismall)

/-- In a nonunital normed ring, an eventually idempotent convergent family is
eventually equal to its limit if it eventually commutes with that limit. -/
theorem eventually_eq_of_eventually_isIdempotentElem
    [NonUnitalNormedRing R] {I : Type uI} {L : Filter I} {u : I → R} {p : R}
    (hu : Tendsto u L (𝓝 p))
    (hid : ∀ᶠ i in L, IsIdempotentElem (u i))
    (hcomm : ∀ᶠ i in L, Commute (u i) p) :
    ∀ᶠ i in L, u i = p := by
  filter_upwards [hu.eventually_norm_sub_eq_zero_of_eventually_isIdempotentElem hid hcomm]
    with i hi
  exact sub_eq_zero.mp (norm_eq_zero.mp hi)

end Filter.Tendsto

/-- Continuity at a point, eventual idempotence near that point, and eventual
commutation with its value imply equality to that value on a neighborhood. -/
theorem ContinuousAt.eventually_eq_of_eventually_isIdempotentElem
    [NonUnitalNormedRing R] {X : Type uX} [TopologicalSpace X] {f : X → R} {x : X}
    (hf : ContinuousAt f x)
    (hid : ∀ᶠ y in 𝓝 x, IsIdempotentElem (f y))
    (hcomm : ∀ᶠ y in 𝓝 x, Commute (f y) (f x)) :
    ∀ᶠ y in 𝓝 x, f y = f x :=
  Filter.Tendsto.eventually_eq_of_eventually_isIdempotentElem hf hid hcomm

/-- A continuous idempotent-valued map into a nonunital normed ring is locally
constant if each value commutes with nearby values eventually at its point. -/
theorem Continuous.isLocallyConstant_of_isIdempotentElem
    [NonUnitalNormedRing R] {X : Type uX} [TopologicalSpace X] {f : X → R}
    (hf : Continuous f) (hid : ∀ x, IsIdempotentElem (f x))
    (hcomm : ∀ x, ∀ᶠ y in 𝓝 x, Commute (f y) (f x)) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).2
  intro x
  exact ContinuousAt.eventually_eq_of_eventually_isIdempotentElem
    hf.continuousAt (Filter.Eventually.of_forall hid) (hcomm x)
