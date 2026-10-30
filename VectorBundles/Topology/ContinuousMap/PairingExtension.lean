/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Constant extension of supported pairings

Let `μ : C(M × V, W)` satisfy `μ (m₀, v) = w₀`. If the closure of
`{x | w x ≠ m₀}` is contained in an arbitrary subset `U`, then the pairing of
`w : C(X, M)` with `g : C(U, V)` extends continuously by `w₀` outside `U`.
`ContinuousMap.pairingExtend` constructs this extension; its values on and off
`U` characterize it uniquely.

No openness of `U`, separation axiom, or inhabitant of `V` is required. At a point
`p ∈ U`, extend `g` temporarily by `g p`; this auxiliary function is continuous
at `p`, even when `U` is not open. Outside `U`, the complement of the closed
cozero support is a neighborhood where the extension is constant.
-/

@[expose] public section

open Set Filter Topology

universe uX uM uV uW

namespace ContinuousMap

variable {X : Type uX} {M : Type uM} {V : Type uV} {W : Type uW}
variable [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace V] [TopologicalSpace W]

private noncomputable def extendValue {U : Set X} (g : C(U, V)) (v : V) (x : X) : V := by
  classical
  exact if hx : x ∈ U then g ⟨x, hx⟩ else v

private theorem continuousAt_extendValue {U : Set X} (g : C(U, V)) (p : U) :
    ContinuousAt (extendValue g (g p)) p.val := by
  classical
  have hp : extendValue g (g p) p.val = g p := by simp [extendValue]
  rw [ContinuousAt, hp, tendsto_def]
  intro s hs
  have hgs : g ⁻¹' s ∈ 𝓝 p := g.continuous.continuousAt.eventually hs
  obtain ⟨t, ht, hts⟩ := (mem_nhds_induced Subtype.val p (g ⁻¹' s)).mp hgs
  apply mem_of_superset ht
  intro x hx
  by_cases h : x ∈ U
  · simpa [extendValue, h] using hts (show (⟨x, h⟩ : U) ∈ Subtype.val ⁻¹' t from hx)
  · simpa [extendValue, h] using mem_of_mem_nhds hs

private noncomputable def pairingValue (μ : C(M × V, W)) (w₀ : W)
    {U : Set X} (w : C(X, M)) (g : C(U, V)) (x : X) : W := by
  classical
  exact if hx : x ∈ U then μ (w x, g ⟨x, hx⟩) else w₀

private theorem continuous_pairingValue (μ : C(M × V, W)) (m₀ : M) (w₀ : W)
    (hμ : ∀ v, μ (m₀, v) = w₀) {U : Set X} (w : C(X, M))
    (hsupport : closure {x | w x ≠ m₀} ⊆ U) (g : C(U, V)) :
    Continuous (pairingValue μ w₀ w g) := by
  classical
  have weight_off {x : X} (hx : x ∉ U) : w x = m₀ := by
    by_contra h
    exact hx (hsupport (subset_closure h))
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ U
  · have heq : pairingValue μ w₀ w g = fun x ↦ μ (w x, extendValue g (g ⟨p, hp⟩) x) := by
      funext x
      by_cases hx : x ∈ U
      · simp [pairingValue, extendValue, hx]
      · simp [pairingValue, extendValue, hx, weight_off hx, hμ]
    rw [heq]
    exact μ.continuous.continuousAt.comp
      (w.continuous.continuousAt.prodMk (continuousAt_extendValue g ⟨p, hp⟩))
  · have hpC : p ∉ closure {x | w x ≠ m₀} := fun h ↦ hp (hsupport h)
    have hn : (closure {x | w x ≠ m₀})ᶜ ∈ 𝓝 p := isClosed_closure.isOpen_compl.mem_nhds hpC
    have heq : pairingValue μ w₀ w g =ᶠ[𝓝 p] fun _ ↦ w₀ := by
      filter_upwards [hn] with x hx
      have hw : w x = m₀ := by
        by_contra h
        exact hx (subset_closure h)
      by_cases hU : x ∈ U
      · simp [pairingValue, hU, hw, hμ]
      · simp [pairingValue, hU]
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- Extend a pairing by its distinguished constant value outside an arbitrary subset.
The closure of the nonconstant locus of the first input must lie inside the subset. -/
noncomputable def pairingExtend (μ : C(M × V, W)) (m₀ : M) (w₀ : W)
    (hμ : ∀ v, μ (m₀, v) = w₀) {U : Set X} (w : C(X, M))
    (hsupport : closure {x | w x ≠ m₀} ⊆ U) (g : C(U, V)) : C(X, W) := by
  classical
  exact {
    toFun := fun x ↦ if hx : x ∈ U then μ (w x, g ⟨x, hx⟩) else w₀
    continuous_toFun := by exact continuous_pairingValue μ m₀ w₀ hμ w hsupport g }

variable (μ : C(M × V, W)) (m₀ : M) (w₀ : W) (hμ : ∀ v, μ (m₀, v) = w₀)
variable {U : Set X} (w : C(X, M)) (hsupport : closure {x | w x ≠ m₀} ⊆ U) (g : C(U, V))

/-- On the subset, the extension is the given pairing. -/
@[simp] theorem pairingExtend_apply_of_mem (x : X) (hx : x ∈ U) :
    μ.pairingExtend m₀ w₀ hμ w hsupport g x = μ (w x, g ⟨x, hx⟩) := by
  classical
  simp [pairingExtend, hx]

/-- Off the subset, the extension takes the distinguished constant value. -/
@[simp] theorem pairingExtend_apply_of_notMem (x : X) (hx : x ∉ U) :
    μ.pairingExtend m₀ w₀ hμ w hsupport g x = w₀ := by
  classical
  simp [pairingExtend, hx]

/-- Wherever the weight is distinguished, the extension takes the constant value. -/
theorem pairingExtend_apply_of_eq (x : X) (hx : w x = m₀) :
    μ.pairingExtend m₀ w₀ hμ w hsupport g x = w₀ := by
  by_cases hU : x ∈ U
  · rw [pairingExtend_apply_of_mem μ m₀ w₀ hμ w hsupport g x hU, hx, hμ]
  · exact pairingExtend_apply_of_notMem μ m₀ w₀ hμ w hsupport g x hU

/-- The formulas on and off the subset uniquely determine the continuous extension. -/
theorem pairingExtend_unique (G : C(X, W))
    (hin : ∀ (x : X) (hx : x ∈ U), G x = μ (w x, g ⟨x, hx⟩))
    (hout : ∀ x : X, x ∉ U → G x = w₀) :
    G = μ.pairingExtend m₀ w₀ hμ w hsupport g := by
  ext x
  by_cases hx : x ∈ U
  · rw [hin x hx, pairingExtend_apply_of_mem μ m₀ w₀ hμ w hsupport g x hx]
  · rw [hout x hx, pairingExtend_apply_of_notMem μ m₀ w₀ hμ w hsupport g x hx]

/-- An extensional characterization of the extension by its values on both pieces. -/
theorem eq_pairingExtend_iff (G : C(X, W)) :
    G = μ.pairingExtend m₀ w₀ hμ w hsupport g ↔
      (∀ (x : X) (hx : x ∈ U), G x = μ (w x, g ⟨x, hx⟩)) ∧
      (∀ x : X, x ∉ U → G x = w₀) := by
  constructor
  · rintro rfl
    exact ⟨pairingExtend_apply_of_mem μ m₀ w₀ hμ w hsupport g,
      pairingExtend_apply_of_notMem μ m₀ w₀ hμ w hsupport g⟩
  · rintro ⟨hin, hout⟩
    exact pairingExtend_unique μ m₀ w₀ hμ w hsupport g G hin hout

include hμ hsupport in
/-- A continuous pairing constant at a distinguished first input has a continuous
constant extension whenever the closed cozero support of the weight lies in the domain. -/
theorem exists_pairing_extension :
    ∃ G : C(X, W),
      (∀ (x : X) (hx : x ∈ U), G x = μ (w x, g ⟨x, hx⟩)) ∧
      (∀ x : X, x ∉ U → G x = w₀) :=
  ⟨μ.pairingExtend m₀ w₀ hμ w hsupport g,
    pairingExtend_apply_of_mem μ m₀ w₀ hμ w hsupport g,
    pairingExtend_apply_of_notMem μ m₀ w₀ hμ w hsupport g⟩

end ContinuousMap
