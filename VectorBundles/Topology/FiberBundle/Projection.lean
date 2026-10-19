/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Characteristic projection of a fiber bundle

The projection of a fiber bundle is an open embedding exactly when every fiber is
subsingleton. It is the forward map of a homeomorphism exactly when every fiber is
also nonempty. These are fiberwise criteria: an empty base imposes no condition on the model.
The given base, model, fiber and total-space topologies and the given `FiberBundle` are retained.

The canonical homeomorphism uses `Equiv.ofBijective` and
`Equiv.toHomeomorphOfContinuousOpen`, not a new bundle or topology construction. Its hypothesis
is the minimal fiberwise existence-and-uniqueness proposition, rather than additional chosen
points or model assumptions. Its inverse is characterized as an equality of dependent pairs.
The zero-section formula uses the given fiber zeros, with no vector-bundle hypothesis.
-/

@[expose] public section

universe uB uF uE

open Bundle

namespace FiberBundle

private theorem injective_proj_iff_subsingleton {B : Type uB} (F : Type uF)
    (E : B → Type uE) :
    Function.Injective (TotalSpace.proj (F := F) (E := E)) ↔
      ∀ b, Subsingleton (E b) := by
  constructor
  · intro h b
    refine ⟨fun e e' ↦ ?_⟩
    exact TotalSpace.mk_injective b
      (h (a₁ := TotalSpace.mk b e) (a₂ := TotalSpace.mk b e') rfl)
  · intro h x y hxy
    rcases x with ⟨b, e⟩
    rcases y with ⟨b', e'⟩
    change b = b' at hxy
    subst b'
    exact congrArg (TotalSpace.mk b) (@Subsingleton.elim (E b) (h b) e e')

variable {B : Type uB} (F : Type uF) (E : B → Type uE)
  [tB : TopologicalSpace B] [tF : TopologicalSpace F]
  [tE : ∀ b, TopologicalSpace (E b)] [tTotal : TopologicalSpace (TotalSpace F E)]
  [fb : FiberBundle F E]

/-- The projection is an open embedding exactly when each fiber has at most one point. -/
theorem isOpenEmbedding_proj_iff :
    Topology.IsOpenEmbedding (TotalSpace.proj (F := F) (E := E)) ↔
      ∀ b, Subsingleton (E b) := by
  constructor
  · intro h
    exact (injective_proj_iff_subsingleton F E).1 h.injective
  · intro h
    exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_proj F E) ((injective_proj_iff_subsingleton F E).2 h)
      (isOpenMap_proj F E)

/-- A subsingleton model suffices, including an empty model. -/
theorem isOpenEmbedding_proj_of_subsingleton [Subsingleton F] :
    Topology.IsOpenEmbedding (TotalSpace.proj (F := F) (E := E)) := by
  apply (isOpenEmbedding_proj_iff F E).2
  intro b
  exact (homeomorphAt F E b).toEquiv.subsingleton

/-- The criterion concerns homeomorphisms whose forward map is the given projection,
not arbitrary homeomorphisms between the two spaces. -/
theorem exists_homeomorph_proj_iff :
    (∃ h : TotalSpace F E ≃ₜ B, ∀ x, h x = x.proj) ↔
      ∀ b, Nonempty (E b) ∧ Subsingleton (E b) := by
  constructor
  · rintro ⟨h, hh⟩ b
    have hproj : Function.Injective (TotalSpace.proj (F := F) (E := E)) := by
      intro x y hxy
      apply h.injective
      rw [hh x, hh y]
      exact hxy
    refine ⟨?_, (injective_proj_iff_subsingleton F E).1 hproj b⟩
    obtain ⟨x, hx⟩ := h.surjective b
    have hx' : x.proj = b := (hh x).symm.trans hx
    exact ⟨hx' ▸ x.snd⟩
  · intro hE
    refine ⟨Equiv.toHomeomorphOfContinuousOpen
      (Equiv.ofBijective (TotalSpace.proj (F := F) (E := E))
        ⟨(injective_proj_iff_subsingleton F E).2 (fun b ↦ (hE b).2), ?_⟩)
      (continuous_proj F E) (isOpenMap_proj F E), ?_⟩
    · intro b
      rcases (hE b).1 with ⟨e⟩
      exact ⟨TotalSpace.mk b e, rfl⟩
    · intro x
      rfl

/-- A nonempty subsingleton model suffices for a projection homeomorphism.
No converse about the model is asserted on an empty base. -/
theorem exists_homeomorph_proj_of_nonempty_subsingleton [Nonempty F] [Subsingleton F] :
    ∃ h : TotalSpace F E ≃ₜ B, ∀ x, h x = x.proj := by
  apply (exists_homeomorph_proj_iff F E).2
  intro b
  exact ⟨(homeomorphAt F E b).toEquiv.nonempty,
    (homeomorphAt F E b).toEquiv.subsingleton⟩

/-- The canonical projection homeomorphism on the original bundle data.
Bijectivity concerns the dependent total-space carrier;
continuity and openness are the existing fiber-bundle API. -/
noncomputable def homeomorphProj (hE : ∀ b, Nonempty (E b) ∧ Subsingleton (E b)) :
    TotalSpace F E ≃ₜ B :=
  (Equiv.ofBijective (TotalSpace.proj (F := F) (E := E)) (by
    refine ⟨(injective_proj_iff_subsingleton F E).2 (fun b ↦ (hE b).2), ?_⟩
    intro b
    rcases (hE b).1 with ⟨e⟩
    exact ⟨TotalSpace.mk b e, rfl⟩)).toHomeomorphOfContinuousOpen
      (continuous_proj F E) (isOpenMap_proj F E)

/-- The forward map of the canonical homeomorphism is definitionally the projection. -/
@[simp] theorem homeomorphProj_apply
    (hE : ∀ b, Nonempty (E b) ∧ Subsingleton (E b)) (x : TotalSpace F E) :
    homeomorphProj F E hE x = x.proj := rfl

/-- The inverse lies over the specified base point. -/
@[simp] theorem homeomorphProj_symm_apply_proj
    (hE : ∀ b, Nonempty (E b) ∧ Subsingleton (E b)) (b : B) :
    ((homeomorphProj F E hE).symm b).proj = b := by
  simpa only [homeomorphProj_apply] using (homeomorphProj F E hE).apply_symm_apply b

/-- Every point of the specified fiber gives the same inverse dependent pair.
No untransported equality between differently indexed fiber coordinates is used. -/
theorem homeomorphProj_symm_apply_eq
    (hE : ∀ b, Nonempty (E b) ∧ Subsingleton (E b)) (b : B) (e : E b) :
    (homeomorphProj F E hE).symm b = TotalSpace.mk b e := by
  apply (homeomorphProj F E hE).injective
  exact ((homeomorphProj F E hE).apply_symm_apply b).trans
    (homeomorphProj_apply F E hE (TotalSpace.mk b e)).symm

/-- The given zeros supply existence and identify the inverse with the given zero
section. No norm, scalar, continuity assumption on the section, or `VectorBundle` is needed. -/
theorem homeomorphProj_symm_apply_zeroSection [∀ b, Zero (E b)]
    (hS : ∀ b, Subsingleton (E b)) (b : B) :
    (homeomorphProj F E (fun b ↦ ⟨⟨0⟩, hS b⟩)).symm b = Bundle.zeroSection F E b := by
  exact homeomorphProj_symm_apply_eq F E (fun b ↦ ⟨⟨0⟩, hS b⟩) b 0

end FiberBundle
