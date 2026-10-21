/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Prod
public import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Tactic.NormNum

/-!
# Examples for symmetry and associativity of fiberwise products

Unequal trivial real fibers make the coordinate permutations nontrivial. Their forward and inverse
values, base coordinates, and restrictions to a fiber use the public characteristic API. Empty
bases require no topologies on the base or models and no fiber structure. A zero-dimensional real
summand gives a distinct boundary case with inhabited fibers.
-/

@[expose] public section

-- Coordinate permutation theorems are public; boundary and pullback examples remain private.

open Bundle

universe uB uF₁ uF₂ uF₃ uE₁ uE₂ uE₃

namespace FiberBundle.Prod

/-- Swapping a real line and a real plane gives the coordinate permutation, its inverse,
preserves the base point, and acts fiberwise as `LinearEquiv.prodComm`. -/
public theorem real_comm_coordinates (b : ℝ) (v : ℝ × (ℝ × ℝ)) :
    @FiberBundle.Prod.homeomorphComm ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (TotalSpace.mk' (ℝ × (ℝ × ℝ)) b (1, (2, 3))) =
      TotalSpace.mk' ((ℝ × ℝ) × ℝ) b ((2, 3), 1) ∧
    (@Homeomorph.symm _ _
        (@FiberBundle.Prod.topologicalSpace ℝ ℝ (Trivial ℝ ℝ)
          (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
          (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance))
        (@FiberBundle.Prod.topologicalSpace ℝ (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
          ℝ (Trivial ℝ ℝ)
          (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance))
        (@FiberBundle.Prod.homeomorphComm ℝ ℝ (Trivial ℝ ℝ)
          (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
          (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)))
        (TotalSpace.mk' ((ℝ × ℝ) × ℝ) b ((2, 3), 1)) =
      TotalSpace.mk' (ℝ × (ℝ × ℝ)) b (1, (2, 3)) ∧
    (@FiberBundle.Prod.homeomorphComm ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (TotalSpace.mk' (ℝ × (ℝ × ℝ)) b v)).proj = b ∧
    @FiberBundle.Prod.homeomorphComm ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (TotalSpace.mk' (ℝ × (ℝ × ℝ)) b v) =
      TotalSpace.mk' ((ℝ × ℝ) × ℝ) b (LinearEquiv.prodComm ℝ ℝ (ℝ × ℝ) v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FiberBundle.Prod.homeomorphComm_apply]
  · rw [FiberBundle.Prod.homeomorphComm_symm_apply]
  · rw [FiberBundle.Prod.homeomorphComm_apply_proj]
  · exact FiberBundle.Prod.homeomorphComm_apply_mk ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      ℝ b v

/-- Reassociating real line, plane, and line fibers gives the coordinate permutation, its inverse,
preserves the base point, and acts fiberwise as `LinearEquiv.prodAssoc`. -/
public theorem real_assoc_coordinates (b : ℝ) (v : (ℝ × (ℝ × ℝ)) × ℝ) :
    @FiberBundle.Prod.homeomorphAssoc ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (Trivial ℝ ℝ)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (TotalSpace.mk' ((ℝ × (ℝ × ℝ)) × ℝ) b ((1, (2, 3)), 4)) =
      TotalSpace.mk' (ℝ × ((ℝ × ℝ) × ℝ)) b (1, ((2, 3), 4)) ∧
    (@Homeomorph.symm _ _
        (@FiberBundle.Prod.topologicalSpace ℝ (ℝ × (ℝ × ℝ))
          ((Trivial ℝ ℝ) ×ᵇ (Trivial ℝ (ℝ × ℝ))) ℝ (Trivial ℝ ℝ)
          (@FiberBundle.Prod.topologicalSpace ℝ ℝ (Trivial ℝ ℝ)
            (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
            (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
            (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance))
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance))
        (@FiberBundle.Prod.topologicalSpace ℝ ℝ (Trivial ℝ ℝ)
          ((ℝ × ℝ) × ℝ) ((Trivial ℝ (ℝ × ℝ)) ×ᵇ (Trivial ℝ ℝ))
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
          (@FiberBundle.Prod.topologicalSpace ℝ (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
            ℝ (Trivial ℝ ℝ)
            (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
            (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)))
        (@FiberBundle.Prod.homeomorphAssoc ℝ ℝ (Trivial ℝ ℝ)
          (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (Trivial ℝ ℝ)
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
          (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
          (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)))
        (TotalSpace.mk' (ℝ × ((ℝ × ℝ) × ℝ)) b (1, ((2, 3), 4))) =
      TotalSpace.mk' ((ℝ × (ℝ × ℝ)) × ℝ) b ((1, (2, 3)), 4) ∧
    (@FiberBundle.Prod.homeomorphAssoc ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (Trivial ℝ ℝ)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (TotalSpace.mk' ((ℝ × (ℝ × ℝ)) × ℝ) b v)).proj = b ∧
    @FiberBundle.Prod.homeomorphAssoc ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (Trivial ℝ ℝ)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (TotalSpace.mk' ((ℝ × (ℝ × ℝ)) × ℝ) b v) =
      TotalSpace.mk' (ℝ × ((ℝ × ℝ) × ℝ)) b (LinearEquiv.prodAssoc ℝ ℝ (ℝ × ℝ) ℝ v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FiberBundle.Prod.homeomorphAssoc_apply]
  · rw [FiberBundle.Prod.homeomorphAssoc_symm_apply]
  · rw [FiberBundle.Prod.homeomorphAssoc_apply_proj]
  · exact FiberBundle.Prod.homeomorphAssoc_apply_mk ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (Trivial ℝ ℝ)
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      (t₃ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      ℝ b v

private theorem empty_base_ranges {B : Type uB} [IsEmpty B]
    (F₁ : Type uF₁) (E₁ : B → Type uE₁) (F₂ : Type uF₂) (E₂ : B → Type uE₂)
    (F₃ : Type uF₃) (E₃ : B → Type uE₃)
    [t₁ : TopologicalSpace (TotalSpace F₁ E₁)] [t₂ : TopologicalSpace (TotalSpace F₂ E₂)]
    [t₃ : TopologicalSpace (TotalSpace F₃ E₃)] :
    Set.range (@FiberBundle.Prod.homeomorphComm B F₁ E₁ F₂ E₂ t₁ t₂) = ∅ ∧
      Set.range (@FiberBundle.Prod.homeomorphAssoc B F₁ E₁ F₂ E₂ F₃ E₃ t₁ t₂ t₃) = ∅ := by
  constructor
  · ext p
    exact isEmptyElim p.proj
  · ext p
    exact isEmptyElim p.proj

private theorem real_rankZero_coordinates (b x y : ℝ) :
    @FiberBundle.Prod.homeomorphComm ℝ (Fin 0 → ℝ) (Trivial ℝ (Fin 0 → ℝ))
        ℝ (Trivial ℝ ℝ)
        (@Bundle.Trivial.topologicalSpace ℝ (Fin 0 → ℝ) inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (TotalSpace.mk' ((Fin 0 → ℝ) × ℝ) b (0, x)) =
      TotalSpace.mk' (ℝ × (Fin 0 → ℝ)) b (x, 0) ∧
    @FiberBundle.Prod.homeomorphAssoc ℝ (Fin 0 → ℝ) (Trivial ℝ (Fin 0 → ℝ))
        ℝ (Trivial ℝ ℝ) ℝ (Trivial ℝ ℝ)
        (@Bundle.Trivial.topologicalSpace ℝ (Fin 0 → ℝ) inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (TotalSpace.mk' (((Fin 0 → ℝ) × ℝ) × ℝ) b ((0, x), y)) =
      TotalSpace.mk' ((Fin 0 → ℝ) × (ℝ × ℝ)) b (0, (x, y)) := by
  constructor
  · rw [FiberBundle.Prod.homeomorphComm_apply]
  · rw [FiberBundle.Prod.homeomorphAssoc_apply]

end FiberBundle.Prod


namespace FiberBundle.Prod

-- The original trivial real line and plane, pulled back along the same square map.
-- The original nonzero line coordinate and all module data are independent of the comparison.
private theorem real_square_pullback_coordinates :
    let tL := @pullbackTopology ℝ (ℝ × (ℝ × ℝ))
      ((Trivial ℝ ℝ) ×ᵇ (Trivial ℝ (ℝ × ℝ))) ℝ (fun x : ℝ ↦ x ^ (2 : ℕ)) inferInstance
      (@FiberBundle.Prod.topologicalSpace ℝ ℝ (Trivial ℝ ℝ)
        (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ))
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance))
    let tR := @FiberBundle.Prod.topologicalSpace ℝ ℝ
      ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ ℝ)) (ℝ × ℝ)
      ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ (ℝ × ℝ)))
      (@pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (fun x : ℝ ↦ x ^ (2 : ℕ)) inferInstance
        (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance))
      (@pullbackTopology ℝ (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (fun x : ℝ ↦ x ^ (2 : ℕ))
        inferInstance
        (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance))
    let h := @FiberBundle.Prod.homeomorphPullback ℝ ℝ ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ)) inferInstance
      (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
    let hsym := @Homeomorph.symm _ _ tL tR h
    let zL : TotalSpace (ℝ × (ℝ × ℝ))
        ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ ((Trivial ℝ ℝ) ×ᵇ (Trivial ℝ (ℝ × ℝ)))) :=
      TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))
    let zR : TotalSpace (ℝ × (ℝ × ℝ))
        (((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ ℝ)) ×ᵇ
          ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ (ℝ × ℝ)))) :=
      TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))
    h zL = zR ∧ hsym zR = zL ∧
      (h zL).proj = (2 : ℝ) ∧ (hsym zR).proj = (2 : ℝ) ∧
      (@Bundle.Pullback.lift ℝ ℝ (Trivial ℝ ℝ) ℝ (fun x : ℝ ↦ x ^ (2 : ℕ))
          (TotalSpace.mk' ℝ (h zL).proj (h zL).snd.1),
        @Bundle.Pullback.lift ℝ (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) ℝ (fun x : ℝ ↦ x ^ (2 : ℕ))
          (TotalSpace.mk' (ℝ × ℝ) (h zL).proj (h zL).snd.2)) =
        ((TotalSpace.mk' ℝ (4 : ℝ) (1 : ℝ) : TotalSpace ℝ (Trivial ℝ ℝ)),
          (TotalSpace.mk' (ℝ × ℝ) (4 : ℝ) ((2 : ℝ), (3 : ℝ)) :
            TotalSpace (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)))) ∧
      h zL = (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ)
        (LinearEquiv.refl ℝ (ℝ × (ℝ × ℝ)) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))) :
          TotalSpace (ℝ × (ℝ × ℝ))
            (((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ ℝ)) ×ᵇ
              ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ (ℝ × ℝ))))) ∧
      hsym zR = (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ)
        (LinearEquiv.refl ℝ (ℝ × (ℝ × ℝ)) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))) :
          TotalSpace (ℝ × (ℝ × ℝ))
            ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ ((Trivial ℝ ℝ) ×ᵇ (Trivial ℝ (ℝ × ℝ))))) ∧
      (1 : ℝ) ≠ (0 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, one_ne_zero⟩
  · exact FiberBundle.Prod.homeomorphPullback_apply ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ))))
  · exact FiberBundle.Prod.homeomorphPullback_symm_apply ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ))))
  · exact FiberBundle.Prod.homeomorphPullback_apply_proj ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ))))
  · exact FiberBundle.Prod.homeomorphPullback_symm_apply_proj ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      (TotalSpace.mk' (ℝ × (ℝ × ℝ)) (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ))))
  · rw [FiberBundle.Prod.lift_pair_homeomorphPullback]
    norm_num [Bundle.Pullback.lift, TotalSpace.mk']
  · exact FiberBundle.Prod.homeomorphPullback_apply_mk ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      ℝ (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))
  · exact FiberBundle.Prod.homeomorphPullback_symm_apply_mk ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) (fun x : ℝ ↦ x ^ (2 : ℕ))
      (t₁ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (t₂ := @Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)
      ℝ (2 : ℝ) ((1 : ℝ), ((2 : ℝ), (3 : ℝ)))

-- Restricting the same original pair to the empty source gives an empty range.
private theorem real_pullback_empty_range (f : Empty → ℝ) :
    Set.range (@FiberBundle.Prod.homeomorphPullback Empty ℝ ℝ (Trivial ℝ ℝ)
      (ℝ × ℝ) (Trivial ℝ (ℝ × ℝ)) f inferInstance
      (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (@Bundle.Trivial.topologicalSpace ℝ (ℝ × ℝ) inferInstance inferInstance)) = ∅ := by
  ext z
  exact z.proj.elim

-- The existing rank-zero summand stays inhabited after the same square pullback.
private theorem real_square_pullback_rankZero :
    @FiberBundle.Prod.homeomorphPullback ℝ ℝ (Fin 0 → ℝ) (Trivial ℝ (Fin 0 → ℝ))
      ℝ (Trivial ℝ ℝ) (fun x : ℝ ↦ x ^ (2 : ℕ)) inferInstance
      (@Bundle.Trivial.topologicalSpace ℝ (Fin 0 → ℝ) inferInstance inferInstance)
      (@Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
      (TotalSpace.mk' ((Fin 0 → ℝ) × ℝ) (2 : ℝ) ((0 : Fin 0 → ℝ), (1 : ℝ))) =
        (TotalSpace.mk' ((Fin 0 → ℝ) × ℝ) (2 : ℝ) ((0 : Fin 0 → ℝ), (1 : ℝ)) :
          TotalSpace ((Fin 0 → ℝ) × ℝ)
            (((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ (Fin 0 → ℝ))) ×ᵇ
              ((fun x : ℝ ↦ x ^ (2 : ℕ)) *ᵖ (Trivial ℝ ℝ)))) := by
  exact FiberBundle.Prod.homeomorphPullback_apply (Fin 0 → ℝ) (Trivial ℝ (Fin 0 → ℝ))
    ℝ (Trivial ℝ ℝ) (fun x : ℝ ↦ x ^ (2 : ℕ))
    (t₁ := @Bundle.Trivial.topologicalSpace ℝ (Fin 0 → ℝ) inferInstance inferInstance)
    (t₂ := @Bundle.Trivial.topologicalSpace ℝ ℝ inferInstance inferInstance)
    (TotalSpace.mk' ((Fin 0 → ℝ) × ℝ) (2 : ℝ) ((0 : Fin 0 → ℝ), (1 : ℝ)))

end FiberBundle.Prod
