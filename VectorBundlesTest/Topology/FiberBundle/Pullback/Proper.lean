/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order
public import VectorBundles.Topology.FiberBundle.Pullback.Proper

/-!
# Proper pullback lifts over a two-sheeted base and empty original fibers

The projection `ℝ × Fin 2 → ℝ` gives a proper, noninjective base map whose lift to the
trivial real-line family is also noninjective. Properness of the base projection
follows from compactness of `Fin 2`. The original trivial-bundle projection is
continuous in its product topology. The distinct points on the two sheets have the
same image under both the base map and the pullback lift.

Empty original fibers give a boundary case without a nonemptiness hypothesis.
Both examples use `Bundle.Pullback.isProperMap_lift` on the original total-space
topologies and obtain its proper-base and projection-continuity hypotheses independently.

## References

* Mathlib's `Mathlib.Topology.Maps.Proper.Basic`, by Anatole Dedecker and Etienne Marion,
  supplies properness of the first projection with compact second factor.
* Mathlib's `Mathlib.Topology.FiberBundle.Constructions`, by Nicolò Cavalleri,
  Sébastien Gouëzel, Heather Macbeth and Floris van Doorn, supplies the original trivial
  and pullback topologies and `Bundle.Trivial.homeomorphProd`.
-/

@[expose] public section

open Bundle

example :
    IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) ∧
      ¬ Function.Injective (Prod.fst : ℝ × Fin 2 → ℝ) ∧
      Continuous (π ℝ (Trivial ℝ ℝ)) ∧
      IsProperMap (@Bundle.Pullback.lift ℝ ℝ (Trivial ℝ ℝ) (ℝ × Fin 2) Prod.fst) ∧
      ¬ Function.Injective
        (@Bundle.Pullback.lift ℝ ℝ (Trivial ℝ ℝ) (ℝ × Fin 2) Prod.fst) := by
  have hf : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hnotinj : ¬ Function.Injective (Prod.fst : ℝ × Fin 2 → ℝ) := by
    intro h
    have hp : ((0 : ℝ), (0 : Fin 2)) = (0, 1) := h rfl
    exact Nat.zero_ne_one (congrArg (fun p : ℝ × Fin 2 ↦ p.2.val) hp)
  have hπ : Continuous (π ℝ (Trivial ℝ ℝ)) :=
    continuous_fst.comp (Trivial.homeomorphProd ℝ ℝ).continuous
  refine ⟨hf, hnotinj, hπ,
    Bundle.Pullback.isProperMap_lift ℝ (Trivial ℝ ℝ) Prod.fst hf hπ, ?_⟩
  intro h
  have hz :
      (⟨((0 : ℝ), (0 : Fin 2)), (0 : ℝ)⟩ :
        TotalSpace ℝ ((Prod.fst : ℝ × Fin 2 → ℝ) *ᵖ (Trivial ℝ ℝ))) =
      ⟨((0 : ℝ), (1 : Fin 2)), (0 : ℝ)⟩ := h rfl
  exact Nat.zero_ne_one
    (congrArg
      (fun z : TotalSpace ℝ ((Prod.fst : ℝ × Fin 2 → ℝ) *ᵖ (Trivial ℝ ℝ)) ↦
        z.proj.2.val) hz)

example :
    IsEmpty (TotalSpace Empty (Trivial ℝ Empty)) ∧
      IsProperMap
        (@Bundle.Pullback.lift ℝ Empty (Trivial ℝ Empty) (ℝ × Fin 2) Prod.fst) := by
  have hf : IsProperMap (Prod.fst : ℝ × Fin 2 → ℝ) :=
    isProperMap_fst_of_compactSpace
  have hπ : Continuous (π Empty (Trivial ℝ Empty)) :=
    continuous_fst.comp (Trivial.homeomorphProd ℝ Empty).continuous
  refine ⟨⟨fun z ↦ z.snd.elim⟩, ?_⟩
  exact Bundle.Pullback.isProperMap_lift Empty (Trivial ℝ Empty) Prod.fst hf hπ
