/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.Pullback
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Tactic.NormNum

/-!
# Examples for pullback total spaces

The identity comparison and an iterated square map illustrate pullback coherence
for the trivial real-line bundle. The square map also gives a nonlinear universal
map. The original trivial topology gives product coordinates for this pullback,
and the inverse comparison recovers that same universal map. Constant pullbacks
of the same real line give the same original point over a specified square.
Empty bases and rank-zero real vector bundles give distinct boundary cases:
a rank-zero fiber has one element, rather than being empty. Finite two-point
counterexamples show that the continuity conditions for identity and composition
cannot be dropped.
-/

@[expose] public section

open Bundle

universe uB uF uE

noncomputable section

namespace IncubatorTest.Pullback

private def squareBase : C(ℝ, ℝ) where
  toFun x := x ^ 2
  continuous_toFun := continuous_id.pow 2

private def baseProjection : C(ℝ × ℝ, ℝ) where
  toFun p := p.1
  continuous_toFun := continuous_fst

private def squareTotalMap : C(ℝ × ℝ, TotalSpace ℝ (Trivial ℝ ℝ)) where
  toFun p := ⟨p.1 ^ 2, p.2⟩
  continuous_toFun := (Bundle.Trivial.homeomorphProd ℝ ℝ).symm.continuous.comp
    ((continuous_fst.pow 2).prodMk continuous_snd)

private theorem square_compatible (p : ℝ × ℝ) :
    squareBase (baseProjection p) = (squareTotalMap p).proj := by
  rfl

-- The universal map recovers the input base and fiber coordinates, even though
-- the square base map is neither injective nor surjective.
private theorem liftMap_square_apply (p : ℝ × ℝ) :
    Bundle.Pullback.liftMap ℝ (Trivial ℝ ℝ) (squareBase : ℝ → ℝ)
      baseProjection squareTotalMap square_compatible p =
        TotalSpace.mk' ℝ p.1 p.2 := by
  apply (Bundle.Pullback.homeomorphProdSubtype ℝ (Trivial ℝ ℝ)
    (squareBase : ℝ → ℝ)).injective
  apply Subtype.ext
  simp only [Bundle.Pullback.homeomorphProdSubtype_apply_val,
    Bundle.Pullback.liftMap_proj, Bundle.Pullback.lift_liftMap]
  rfl

-- The identity equivalence is packaged only after comparing the pullback topology
-- with the original trivial topology. The stock product chart alone does not
-- establish this comparison. Its inverse agrees with the existing universal map,
-- and its original lift at (2, 3) has coordinates (4, 3).
private theorem square_original_trivial_comparison :
    ∃ e : @Homeomorph
        (TotalSpace ℝ ((squareBase : ℝ → ℝ) *ᵖ (Trivial ℝ ℝ))) (ℝ × ℝ)
        (@pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (squareBase : ℝ → ℝ)
          inferInstance (Trivial.topologicalSpace ℝ ℝ)) inferInstance,
      (∀ p : ℝ × ℝ, e.symm p =
        Bundle.Pullback.liftMap ℝ (Trivial ℝ ℝ) (squareBase : ℝ → ℝ)
          baseProjection squareTotalMap square_compatible p) ∧
      (∀ p : ℝ × ℝ,
        Bundle.Pullback.lift (squareBase : ℝ → ℝ) (e.symm p) = squareTotalMap p) ∧
      Bundle.Pullback.lift (squareBase : ℝ → ℝ) (e.symm (2, 3)) =
        TotalSpace.mk' ℝ (4 : ℝ) (3 : ℝ) := by
  have ht :
      @pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (squareBase : ℝ → ℝ)
          inferInstance (Trivial.topologicalSpace ℝ ℝ) =
        Trivial.topologicalSpace ℝ ℝ :=
    (Bundle.Pullback.pullbackTopology_trivial_eq_iff ℝ (squareBase : ℝ → ℝ)).2
      (squareBase.continuous.comp (FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ)))
  let e : @Homeomorph
      (TotalSpace ℝ ((squareBase : ℝ → ℝ) *ᵖ (Trivial ℝ ℝ)))
      (TotalSpace ℝ (Trivial ℝ ℝ))
      (@pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (squareBase : ℝ → ℝ)
        inferInstance (Trivial.topologicalSpace ℝ ℝ)) (Trivial.topologicalSpace ℝ ℝ) :=
    @Equiv.toHomeomorphOfIsInducing _ _
      (@pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (squareBase : ℝ → ℝ)
        inferInstance (Trivial.topologicalSpace ℝ ℝ)) (Trivial.topologicalSpace ℝ ℝ)
      (Equiv.refl _) ⟨by
        change @pullbackTopology ℝ ℝ (Trivial ℝ ℝ) ℝ (squareBase : ℝ → ℝ)
            inferInstance (Trivial.topologicalSpace ℝ ℝ) =
          TopologicalSpace.induced id (Trivial.topologicalSpace ℝ ℝ)
        rw [induced_id]
        exact ht⟩
  have h_inv (p : ℝ × ℝ) :
      (e.trans (Trivial.homeomorphProd ℝ ℝ)).symm p =
        Bundle.Pullback.liftMap ℝ (Trivial ℝ ℝ) (squareBase : ℝ → ℝ)
          baseProjection squareTotalMap square_compatible p := by
    rw [liftMap_square_apply]
    rfl
  refine ⟨e.trans (Trivial.homeomorphProd ℝ ℝ), h_inv, ?_, ?_⟩
  · intro p
    rw [h_inv]
    exact Bundle.Pullback.lift_liftMap ℝ (Trivial ℝ ℝ) (squareBase : ℝ → ℝ)
      baseProjection squareTotalMap square_compatible p
  · rw [h_inv, Bundle.Pullback.lift_liftMap]
    change TotalSpace.mk' (E := Trivial ℝ ℝ) ℝ ((2 : ℝ) ^ 2) (3 : ℝ) =
      TotalSpace.mk' (E := Trivial ℝ ℝ) ℝ (4 : ℝ) (3 : ℝ)
    norm_num

-- For each input, the constant pullback at its square and the square pullback
-- have the same image in the original real line. The constant comparison uses
-- the original fiber inclusion, supplied directly by the stock bundle theorem.
private theorem const_square_original_lift (p : ℝ × ℝ) :
    Bundle.Pullback.lift (fun _ : ℝ ↦ squareBase p.1)
      ((Bundle.Pullback.homeomorphConst ℝ (Trivial ℝ ℝ) (squareBase p.1)
        (FiberBundle.totalSpaceMk_isInducing ℝ (Trivial ℝ ℝ) (squareBase p.1))).symm p) =
      Bundle.Pullback.lift (squareBase : ℝ → ℝ)
        (Bundle.Pullback.liftMap ℝ (Trivial ℝ ℝ) (squareBase : ℝ → ℝ)
          baseProjection squareTotalMap square_compatible p) := by
  rw [Bundle.Pullback.lift_homeomorphConst_symm, Bundle.Pullback.lift_liftMap]
  rfl

/-- The empty-base boundary uses no topology on the original base or model-fiber parameter,
and no nonemptiness of the fibers. -/
theorem range_homeomorphProdSubtype_empty {B : Type uB} (F : Type uF) (E : B → Type uE)
    [TopologicalSpace (TotalSpace F E)] (f : Empty → B) :
    Set.range (Bundle.Pullback.homeomorphProdSubtype F E f) = ∅ := by
  ext p
  exact p.val.1.elim

-- Local triviality here is the existing vector-bundle pullback construction.
-- No nonzero-rank hypothesis is needed.
private theorem vectorBundle_square_pullback_zero :
    VectorBundle ℝ (Fin 0 → ℝ)
      ((squareBase : ℝ → ℝ) *ᵖ (Trivial ℝ (Fin 0 → ℝ))) := by
  exact VectorBundle.pullback ℝ squareBase

-- The original projection of a trivial bundle is continuous, so the identity
-- comparison recovers the same base and fiber coordinates.
private theorem homeomorphId_trivial_apply (x y : ℝ) :
    Bundle.Pullback.homeomorphId ℝ (Trivial ℝ ℝ)
      (FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ)) (TotalSpace.mk' ℝ x y) =
        TotalSpace.mk' ℝ x y := by
  rw [Bundle.Pullback.homeomorphId_apply]
  rfl

-- Two nonlinear pullbacks flatten to the fourth-power pullback; the lift to the
-- original bundle has base coordinate (x²)² and the unchanged fiber coordinate.
private theorem lift_homeomorphComp_square_apply (x y : ℝ) :
    Bundle.Pullback.lift ((squareBase : ℝ → ℝ) ∘ (squareBase : ℝ → ℝ))
      (Bundle.Pullback.homeomorphComp ℝ (Trivial ℝ ℝ)
        (squareBase : ℝ → ℝ) (squareBase : ℝ → ℝ)
        (squareBase.continuous.comp
          (_root_.Pullback.continuous_proj ℝ (Trivial ℝ ℝ)
            ((squareBase : ℝ → ℝ) ∘ (squareBase : ℝ → ℝ))))
        (TotalSpace.mk' ℝ x y)) =
          TotalSpace.mk' ℝ ((x ^ 2) ^ 2) y := by
  rw [Bundle.Pullback.lift_homeomorphComp]
  rfl

-- An indiscrete two-point total space cannot project continuously onto a
-- discrete base. The point fibers make this a finite, nonempty counterexample.
private theorem not_continuous_bool_proj :
    ¬ @Continuous (TotalSpace Unit (fun _ : Bool ↦ Unit)) Bool ⊤ ⊥
      (π Unit (fun _ : Bool ↦ Unit)) := by
  intro h
  have hs := @Continuous.isOpen_preimage
    (TotalSpace Unit (fun _ : Bool ↦ Unit)) Bool ⊤ ⊥
    (π Unit (fun _ : Bool ↦ Unit)) h {false} (by trivial)
  rcases (TopologicalSpace.isOpen_top_iff _).mp hs with hs | hs
  · have he := Set.ext_iff.mp hs (TotalSpace.mk' Unit false ())
    simp at he
  · have he := Set.ext_iff.mp hs (TotalSpace.mk' Unit true ())
    simp at he

-- With discrete Bool base and indiscrete original total space, the identity
-- pullback topology is not the original one. Continuity of the original
-- projection in `homeomorphId` therefore cannot be dropped.
private theorem pullbackTopology_bool_id_ne_top :
    @pullbackTopology Bool Unit (fun _ : Bool ↦ Unit) Bool id ⊥ ⊤ ≠ ⊤ := by
  intro he
  exact not_continuous_bool_proj
    ((@Bundle.Pullback.pullbackTopology_id_eq_iff Bool Unit
      (fun _ : Bool ↦ Unit) ⊥ ⊤).1 he)

-- Here the first Bool base is indiscrete, the intermediate Bool base is
-- discrete, and the original base is a point. The composite topology is
-- indiscrete, but the iterated topology records the discrete Bool coordinate.
private theorem pullbackTopology_bool_comp_ne :
    @pullbackTopology Bool Unit ((fun _ : Bool ↦ ()) *ᵖ (fun _ : Unit ↦ Unit))
        Bool id ⊤ (@pullbackTopology Unit Unit (fun _ : Unit ↦ Unit)
          Bool (fun _ ↦ ()) ⊥ ⊤) ≠
      @pullbackTopology Unit Unit (fun _ : Unit ↦ Unit)
        Bool ((fun _ : Bool ↦ ()) ∘ id) ⊤ ⊤ := by
  intro he
  have hc := (@Bundle.Pullback.pullbackTopology_comp_eq_iff Bool Bool Unit Unit
    (fun _ : Unit ↦ Unit) (fun _ : Bool ↦ ()) id ⊤ ⊥ ⊤).1 he
  simp only [continuous_iff_le_induced, pullbackTopology_def, induced_top, inf_idem] at hc
  apply not_continuous_bool_proj
  exact continuous_iff_le_induced.2 hc

end IncubatorTest.Pullback
