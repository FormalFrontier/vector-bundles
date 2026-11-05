/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Inseparable

/-!
# Homotopies from sections of inducing maps

Let `f : X → Y` induce the topology on `X`, and let `s : Y → X` be a given
right inverse. The section is continuous, and the map which is `x` at time zero
and `s (f x)` at every other time is jointly continuous: its composite with `f`
is the continuous map `(t, x) ↦ f x`.

`Topology.IsInducing.sectionHomotopy` packages this particular map as a
relative homotopy from the identity to `s ∘ f`, relative to `Set.range s`.
After forgetting the relative condition, its endpoint equations are
`ContinuousMap.Homotopy.apply_zero` and `ContinuousMap.Homotopy.apply_one`;
`ContinuousMap.HomotopyRel.eq_fst` gives the all-time fixed-point equation.
The additional evaluation and fiber laws below characterize the chosen homotopy,
not just its homotopy class.
The range has its original subtype topology.

The resulting homotopy equivalence uses exactly `f` and the specified `s`.
In particular it applies to a given section of a separation quotient, even
when the original space is empty. No section is chosen by this construction,
and no separation or nonemptiness assumption is imposed.
-/

@[expose] public section

open scoped unitInterval

universe u v

namespace Topology.IsInducing

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} (hf : IsInducing f) {s : Y → X}
variable (hs : Function.RightInverse s f)

include hf hs in
/-- A given right inverse of an inducing map is continuous. -/
theorem continuous_section : Continuous s := by
  apply hf.continuous_iff.2
  have hcomp : f ∘ s = id := by
    funext y
    exact hs y
  exact hcomp.symm ▸ (continuous_id : Continuous (id : Y → Y))

/-- Retraction onto the range of a given section, with the subtype topology. -/
def sectionRetraction : C(X, Set.range s) where
  toFun x := ⟨s (f x), ⟨f x, rfl⟩⟩
  continuous_toFun := ((hf.continuous_section hs).comp hf.continuous).subtype_mk _

/-- The ambient value of the range retraction is the section after the inducing map. -/
@[simp] theorem coe_sectionRetraction (x : X) :
    (hf.sectionRetraction hs x : X) = s (f x) := rfl

/-- The retraction restricts to the identity on the range of the section. -/
@[simp] theorem sectionRetraction_coe (x : Set.range s) :
    hf.sectionRetraction hs (x : X) = x := by
  apply Subtype.ext
  rw [coe_sectionRetraction]
  obtain ⟨y, hy⟩ := x.property
  rw [← hy, hs]

/-- Retraction followed by the ambient inclusion is the section composite. -/
theorem subtype_val_comp_sectionRetraction :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range s, X)).comp
        (hf.sectionRetraction hs) =
      ⟨s ∘ f, (hf.continuous_section hs).comp hf.continuous⟩ := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The ambient inclusion followed by the retraction is the identity. -/
@[simp] theorem sectionRetraction_comp_subtype_val :
    (hf.sectionRetraction hs).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range s, X)) =
      ContinuousMap.id (Set.range s) := by
  apply ContinuousMap.ext
  intro x
  exact hf.sectionRetraction_coe hs x

/-- The homotopy which stays at the input at time zero and jumps to the
section composite at every other time. It fixes the range of the section
at every time. -/
noncomputable def sectionHomotopy :
    (ContinuousMap.id X).HomotopyRel
      ⟨s ∘ f, (hf.continuous_section hs).comp hf.continuous⟩ (Set.range s) := by
  refine
    { toFun := fun p => if p.1 = 0 then p.2 else s (f p.2)
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · apply hf.continuous_iff.2
    have hcomp :
        f ∘ (fun p : I × X => if p.1 = 0 then p.2 else s (f p.2)) =
          f ∘ Prod.snd := by
      funext p
      dsimp only [Function.comp_def]
      split_ifs
      · rfl
      · exact hs (f p.2)
    rw [hcomp]
    exact hf.continuous.comp continuous_snd
  · intro x
    exact ite_eq_left rfl
  · intro x
    have h10 : (1 : I) ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℝ) ≠ 0) (congrArg Subtype.val h)
    exact ite_eq_right h10
  · intro t x hx
    obtain ⟨y, rfl⟩ := hx
    change (if t = 0 then s y else s (f (s y))) = s y
    split_ifs
    · rfl
    · exact congrArg s (hs y)

/-- Evaluation of the specified relative homotopy, including its time-zero branch. -/
theorem sectionHomotopy_apply (t : I) (x : X) :
    hf.sectionHomotopy hs (t, x) = if t = 0 then x else s (f x) := rfl

/-- At every nonzero time the specified homotopy is the section composite. -/
@[simp] theorem sectionHomotopy_apply_of_ne_zero (t : I) (x : X) (ht : t ≠ 0) :
    hf.sectionHomotopy hs (t, x) = s (f x) := by
  rw [sectionHomotopy_apply, ite_eq_right ht]

/-- The specified relative homotopy remains over the inducing map. -/
theorem map_sectionHomotopy (t : I) (x : X) :
    f (hf.sectionHomotopy hs (t, x)) = f x := by
  rw [sectionHomotopy_apply]
  split_ifs
  · rfl
  · exact hs (f x)

/-- An inducing map with a given section is a homotopy equivalence with exactly
that forward map and inverse map. The left inverse uses the reverse of
`sectionHomotopy`; the right inverse is the constant homotopy supplied by the
right-inverse equation. -/
def homotopyEquivOfSection : ContinuousMap.HomotopyEquiv X Y :=
  ⟨⟨f, hf.continuous⟩, ⟨s, hf.continuous_section hs⟩,
    ⟨(hf.sectionHomotopy hs).toHomotopy.symm⟩,
    ⟨{ toFun := fun p => p.2
       continuous_toFun := continuous_snd
       map_zero_left := fun y => (hs y).symm
       map_one_left := fun _ => rfl }⟩⟩

/-- The forward map is the original inducing map. -/
@[simp] theorem homotopyEquivOfSection_apply (x : X) :
    hf.homotopyEquivOfSection hs x = f x := rfl

/-- The inverse map is the given section. -/
@[simp] theorem homotopyEquivOfSection_symm_apply (y : Y) :
    (hf.homotopyEquivOfSection hs).symm y = s y := rfl

end Topology.IsInducing

namespace SeparationQuotient

variable {X : Type u} [TopologicalSpace X]
variable {s : SeparationQuotient X → X}
variable (hs : Function.RightInverse s (mk : X → SeparationQuotient X))

/-- A specified section of the separation quotient gives a homotopy equivalence
whose forward map is the quotient projection and whose inverse is that section.
This statement includes the empty space and makes no choice of representatives. -/
def homotopyEquivOfSection : ContinuousMap.HomotopyEquiv X (SeparationQuotient X) :=
  (show Topology.IsInducing (mk : X → SeparationQuotient X) from
    isInducing_mk).homotopyEquivOfSection hs

/-- The forward map of the specified equivalence is the quotient projection. -/
@[simp] theorem homotopyEquivOfSection_apply (x : X) :
    homotopyEquivOfSection hs x = mk x := rfl

/-- The inverse map of the specified equivalence is the given section. -/
@[simp] theorem homotopyEquivOfSection_symm_apply (y : SeparationQuotient X) :
    (homotopyEquivOfSection hs).symm y = s y := rfl

end SeparationQuotient
