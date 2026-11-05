/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Inseparable
import Mathlib.Topology.Order
import Mathlib.Topology.Hom.ContinuousEvalConst

/-!
# Compact-open mapping spaces and sections of inducing maps

If `f : E → B` induces the topology on `E` and has a specified right inverse
`g : B → E`, then precomposition by `f` is a homeomorphism from `C(B, Z)` to
`C(E, Z)` for every T₀ space `Z`. Its inverse is precomposition by that very
section `g`, whose continuity follows from the inducing property.

Both spaces of continuous maps carry their compact-open topologies. Continuity
of the two operators is fixed precomposition and requires no local compactness.
The T₀ assumption is used only to identify the values of a continuous map at
`x` and `g (f x)`: these points have the same image under the inducing map and
are therefore inseparable. The construction commutes with continuous
postcomposition in the target.

An indiscrete two-point source mapping to a point gives discrete two-point
mapping spaces for a discrete two-point target. With the same source and
section, an indiscrete two-point target instead admits a nonconstant identity
map outside the image of precomposition.
-/

@[expose] public section

universe u v w w'

namespace Topology.IsInducing

variable {E : Type u} {B : Type v} {Z : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]
variable {f : E → B} (hf : IsInducing f) (g : B → E)
variable (hg : Function.RightInverse g f)

include hf hg in
private theorem continuous_section_of_rightInverse : Continuous g := by
  apply (Topology.IsInducing.continuous_iff (f := g) hf).2
  have hfg : f ∘ g = (id : B → B) := funext (fun b => hg b)
  rw [hfg]
  exact continuous_id

section T0Target

variable [T0Space Z]

include hf hg in
/-- A continuous map to a T₀ space is unchanged by the section composite. -/
@[simp] theorem apply_section_comp (q : C(E, Z)) (x : E) :
    q (g (f x)) = q x := by
  have hi : Inseparable (g (f x)) x := hf.inseparable_iff.1 (by
    simpa only [hg (f x)] using (Inseparable.refl (f x)))
  exact (hi.map q.continuous).eq

/-- Precomposition by an inducing map with a specified section is a
homeomorphism on compact-open mapping spaces into a T₀ target. The inverse
uses the specified section, not a choice of representatives. -/
def precompHomeomorphOfSection : C(B, Z) ≃ₜ C(E, Z) := by
  let F : C(E, B) := ⟨f, hf.continuous⟩
  let G : C(B, E) := ⟨g, by exact continuous_section_of_rightInverse hf g hg⟩
  exact
    { toFun := fun h => h.comp F
      invFun := fun q => q.comp G
      left_inv := fun h => by
        apply ContinuousMap.ext
        intro b
        exact congrArg h (hg b)
      right_inv := fun q => by
        apply ContinuousMap.ext
        intro x
        exact hf.apply_section_comp g hg q x
      continuous_toFun := ContinuousMap.continuous_precomp F
      continuous_invFun := ContinuousMap.continuous_precomp G }

/-- The entire forward function is precomposition by the inducing map. -/
theorem coe_precompHomeomorphOfSection :
    (hf.precompHomeomorphOfSection (Z := Z) g hg : C(B, Z) → C(E, Z)) =
      fun h => h.comp ⟨f, hf.continuous⟩ := rfl

/-- The entire inverse function is precomposition by the given section. -/
theorem coe_precompHomeomorphOfSection_symm :
    ((hf.precompHomeomorphOfSection (Z := Z) g hg).symm : C(E, Z) → C(B, Z)) =
      fun q => q.comp ⟨g, by exact continuous_section_of_rightInverse hf g hg⟩ := rfl

/-- The forward value as a continuous map. -/
@[simp] theorem precompHomeomorphOfSection_apply (h : C(B, Z)) :
    hf.precompHomeomorphOfSection g hg h = h.comp ⟨f, hf.continuous⟩ := rfl

/-- The inverse value as a continuous map. -/
@[simp] theorem precompHomeomorphOfSection_symm_apply (q : C(E, Z)) :
    (hf.precompHomeomorphOfSection g hg).symm q =
      q.comp ⟨g, by exact continuous_section_of_rightInverse hf g hg⟩ := rfl

/-- Evaluation of the forward map. -/
@[simp] theorem precompHomeomorphOfSection_apply_apply (h : C(B, Z)) (x : E) :
    hf.precompHomeomorphOfSection g hg h x = h (f x) := rfl

/-- Evaluation of the inverse map. -/
@[simp] theorem precompHomeomorphOfSection_symm_apply_apply (q : C(E, Z)) (b : B) :
    (hf.precompHomeomorphOfSection g hg).symm q b = q (g b) := rfl

variable {W : Type w'} [TopologicalSpace W] [T0Space W]

/-- Continuous postcomposition commutes with the forward homeomorphism. -/
theorem precompHomeomorphOfSection_postcomp (k : C(Z, W)) (h : C(B, Z)) :
    hf.precompHomeomorphOfSection g hg (k.comp h) =
      k.comp (hf.precompHomeomorphOfSection g hg h) := rfl

/-- Continuous postcomposition commutes with the inverse homeomorphism. -/
theorem precompHomeomorphOfSection_symm_postcomp (k : C(Z, W)) (q : C(E, Z)) :
    (hf.precompHomeomorphOfSection g hg).symm (k.comp q) =
      k.comp ((hf.precompHomeomorphOfSection g hg).symm q) := rfl

omit [T0Space Z] in
/-- Evaluation of forward naturality in the target. -/
theorem precompHomeomorphOfSection_postcomp_apply
    (k : C(Z, W)) (h : C(B, Z)) (x : E) :
    hf.precompHomeomorphOfSection g hg (k.comp h) x = k (h (f x)) := rfl

omit [T0Space Z] in
/-- Evaluation of inverse naturality in the target. -/
theorem precompHomeomorphOfSection_symm_postcomp_apply
    (k : C(Z, W)) (q : C(E, Z)) (b : B) :
    (hf.precompHomeomorphOfSection g hg).symm (k.comp q) b = k (q (g b)) := rfl

end T0Target

end Topology.IsInducing

namespace CompactOpenSection

private def IndiscretePair := Bool
private def DiscretePair := Bool

private instance : TopologicalSpace IndiscretePair := ⊤
private instance : TopologicalSpace DiscretePair := ⊥
private instance : DiscreteTopology DiscretePair := ⟨rfl⟩

private def collapse (_ : IndiscretePair) : Unit := ()
private def chooseFalse (_ : Unit) : IndiscretePair := false

private theorem collapse_inducing : Topology.IsInducing collapse := by
  refine ⟨?_⟩
  change (⊤ : TopologicalSpace IndiscretePair) =
    TopologicalSpace.induced (fun _ : IndiscretePair => (() : Unit))
      (inferInstance : TopologicalSpace Unit)
  exact induced_const.symm

private theorem collapse_section : Function.RightInverse chooseFalse collapse := by
  intro b
  cases b
  rfl

/- Both original compact-open mapping spaces are discrete and have exactly two
points. The chosen homeomorphism carries the two distinct constant maps to
two distinct maps, and these exhaust the target mapping space. -/
example :
    DiscreteTopology C(Unit, DiscretePair) ∧
    DiscreteTopology C(IndiscretePair, DiscretePair) ∧
    ∃ h₀ h₁ : C(Unit, DiscretePair), h₀ ≠ h₁ ∧
      collapse_inducing.precompHomeomorphOfSection chooseFalse collapse_section h₀ ≠
        collapse_inducing.precompHomeomorphOfSection chooseFalse collapse_section h₁ ∧
      (∀ h : C(Unit, DiscretePair), h = h₀ ∨ h = h₁) ∧
      (∀ q : C(IndiscretePair, DiscretePair),
        q = collapse_inducing.precompHomeomorphOfSection chooseFalse collapse_section h₀ ∨
        q = collapse_inducing.precompHomeomorphOfSection chooseFalse collapse_section h₁) := by
  have base_inj : Function.Injective (fun h : C(Unit, DiscretePair) => h ()) := by
    intro h k he
    apply ContinuousMap.ext
    intro b
    cases b
    exact he
  have pair_inj : Function.Injective
      (fun q : C(IndiscretePair, DiscretePair) => q false) := by
    intro q r he
    apply ContinuousMap.ext
    intro x
    calc
      q x = q false :=
        (collapse_inducing.apply_section_comp chooseFalse collapse_section q x).symm
      _ = r false := he
      _ = r x := collapse_inducing.apply_section_comp chooseFalse collapse_section r x
  have base_discrete : DiscreteTopology C(Unit, DiscretePair) :=
    DiscreteTopology.of_continuous_injective
      (ContinuousEvalConst.continuous_eval_const () :
        Continuous (fun h : C(Unit, DiscretePair) => h ())) base_inj
  have pair_discrete : DiscreteTopology C(IndiscretePair, DiscretePair) :=
    DiscreteTopology.of_continuous_injective
      (ContinuousEvalConst.continuous_eval_const (false : IndiscretePair) :
        Continuous (fun q : C(IndiscretePair, DiscretePair) => q false)) pair_inj
  have base_two (h : C(Unit, DiscretePair)) :
      h = ContinuousMap.const Unit (false : DiscretePair) ∨
        h = ContinuousMap.const Unit (true : DiscretePair) := by
    cases hv : h () with
    | false =>
      left
      apply ContinuousMap.ext
      intro b
      cases b
      exact hv
    | true =>
      right
      apply ContinuousMap.ext
      intro b
      cases b
      exact hv
  refine ⟨base_discrete, pair_discrete,
    ContinuousMap.const Unit (false : DiscretePair),
    ContinuousMap.const Unit (true : DiscretePair), ?_, ?_, base_two, ?_⟩
  · intro he
    have hv := congrArg (fun h : C(Unit, DiscretePair) => h ()) he
    change (false : Bool) = true at hv
    cases hv
  · intro he
    have hv := congrArg (fun q : C(IndiscretePair, DiscretePair) => q false) he
    change (false : Bool) = true at hv
    cases hv
  · intro q
    let Φ := collapse_inducing.precompHomeomorphOfSection
      (Z := DiscretePair) chooseFalse collapse_section
    rcases base_two (Φ.symm q) with h | h
    · left
      exact (Φ.apply_symm_apply q).symm.trans (congrArg Φ h)
    · right
      exact (Φ.apply_symm_apply q).symm.trans (congrArg Φ h)

/- Changing only the target to the same indiscrete pair admits a nonconstant
identity map. Every precomposition from the point is constant, so that
identity is outside the image. -/
example :
    ContinuousMap.id IndiscretePair ∉
      Set.range (fun h : C(Unit, IndiscretePair) =>
        h.comp (⟨collapse, collapse_inducing.continuous⟩ : C(IndiscretePair, Unit))) := by
  rintro ⟨h, he⟩
  have hfalse := congrArg (fun q : C(IndiscretePair, IndiscretePair) => q false) he
  have htrue := congrArg (fun q : C(IndiscretePair, IndiscretePair) => q true) he
  change h () = (false : IndiscretePair) at hfalse
  change h () = (true : IndiscretePair) at htrue
  have hft : (false : Bool) = true := hfalse.symm.trans htrue
  cases hft

end CompactOpenSection
