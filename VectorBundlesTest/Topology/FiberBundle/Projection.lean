/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.FiberBundle.Projection
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Projection clients on the stock trivial bundle

One substantive zero-model client uses the stock `Bundle.Trivial.topologicalSpace` and
`Bundle.Trivial.fiberBundle` on the nontrivial base `ℝ`. The fibers `Fin 0 → ℝ` have their
pointwise real module structure and zeros. The inverse API recovers the whole original
point from its projection and proves continuity of the given zero section, rather than
assuming continuity of that section or installing new bundle data.

The two boundary examples separate fiberwise criteria from model converses.
-/

open Bundle

-- Both headlines and the canonical inverse API feed a genuine recovery/continuity argument.
example :
    Topology.IsOpenEmbedding
      (TotalSpace.proj (F := Fin 0 → ℝ) (E := Bundle.Trivial ℝ (Fin 0 → ℝ))) ∧
    (∃ h : TotalSpace (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) ≃ₜ ℝ,
      ∀ x, h x = x.proj) ∧
    (∀ x : TotalSpace (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)),
      x = Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) x.proj) ∧
    Continuous (Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ))) ∧
    Function.RightInverse
      (Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)))
      (TotalSpace.proj (F := Fin 0 → ℝ) (E := Bundle.Trivial ℝ (Fin 0 → ℝ))) := by
  let hS : ∀ b : ℝ, Subsingleton (Bundle.Trivial ℝ (Fin 0 → ℝ) b) :=
    fun _ ↦ inferInstance
  let hE : ∀ b : ℝ,
      Nonempty (Bundle.Trivial ℝ (Fin 0 → ℝ) b) ∧
        Subsingleton (Bundle.Trivial ℝ (Fin 0 → ℝ) b) := fun b ↦ ⟨⟨0⟩, hS b⟩
  let h := FiberBundle.homeomorphProj (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) hE
  have hz (b : ℝ) :
      h.symm b = Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) b :=
    FiberBundle.homeomorphProj_symm_apply_zeroSection
      (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) hS b
  have hp (b : ℝ) : h.symm b = TotalSpace.mk b (0 : Fin 0 → ℝ) :=
    FiberBundle.homeomorphProj_symm_apply_eq
      (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) hE b 0
  refine ⟨(FiberBundle.isOpenEmbedding_proj_iff _ _).2 (fun b ↦ hS b),
    (FiberBundle.exists_homeomorph_proj_iff _ _).2 hE, ?_, ?_, ?_⟩
  · intro x
    calc
      x = h.symm (h x) := (h.symm_apply_apply x).symm
      _ = h.symm x.proj := congrArg h.symm
        (FiberBundle.homeomorphProj_apply _ _ hE x)
      _ = TotalSpace.mk x.proj (0 : Fin 0 → ℝ) := hp x.proj
      _ = Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) x.proj := rfl
  · have heq : (fun b ↦ h.symm b) =
        Bundle.zeroSection (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ)) := funext hz
    exact heq ▸ h.symm.continuous
  · intro b
    rw [← hz b]
    exact FiberBundle.homeomorphProj_symm_apply_proj _ _ hE b

-- An empty model over a nonempty base gives an open embedding, but no homeomorphism.
example :
    Topology.IsOpenEmbedding
      (TotalSpace.proj (F := Empty) (E := Bundle.Trivial ℝ Empty)) ∧
    ¬ Nonempty (TotalSpace Empty (Bundle.Trivial ℝ Empty) ≃ₜ ℝ) := by
  refine ⟨FiberBundle.isOpenEmbedding_proj_of_subsingleton _ _, ?_⟩
  rintro ⟨h⟩
  exact Empty.elim (h.symm 0).snd

-- The sharp criterion is vacuous on an empty base, for every model, not just a singleton.
example (F : Type*) [TopologicalSpace F] :
    ∃ h : TotalSpace F (Bundle.Trivial Empty F) ≃ₜ Empty, ∀ x, h x = x.proj := by
  apply (FiberBundle.exists_homeomorph_proj_iff F (Bundle.Trivial Empty F)).2
  intro b
  exact Empty.elim b
