module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

import VectorBundles.Algebra.Ring.Units
import VectorBundles.Topology.Algebra.Monoid.Units
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Unit loci for two nonseparated real rings

Each section gives its ring only the topology induced by its map to the usual
real line. These are the seminorm topologies for `p (a, b) = |a|` and
`p (a + b ε) = |a|`, not the usual product topology. Distinct points in each
map fibre are topologically indistinguishable, so neither topology is T₀.

The product has a strictly larger open inverse image of target units than its
unit locus. For the dual numbers, the square-zero unit criterion reflects
units; when `a ≠ 0`, the inverse is `(a⁻¹, -b / a²)`.
-/

-- These anonymous examples intentionally provide no public API.
set_option linter.privateModule false

section RealProduct

local instance : TopologicalSpace (ℝ × ℝ) :=
  TopologicalSpace.induced (Prod.fst : ℝ × ℝ → ℝ) inferInstance

example :
    Function.Surjective (RingHom.fst ℝ ℝ) ∧
    Topology.IsInducing (RingHom.fst ℝ ℝ) ∧
    ¬Function.Injective (RingHom.fst ℝ ℝ) ∧
    (∀ x : ℝ × ℝ, IsUnit x ↔ x.1 ≠ 0 ∧ x.2 ≠ 0) ∧
    ¬IsLocalHom (RingHom.fst ℝ ℝ) ∧
    IsOpen {r : ℝ | IsUnit r} ∧
    IsOpen {x : ℝ × ℝ | x.1 ≠ 0} ∧
    {x : ℝ × ℝ | IsUnit x} ⊂ {x : ℝ × ℝ | x.1 ≠ 0} ∧
    ¬IsOpen {x : ℝ × ℝ | IsUnit x} := by
  have hsurj : Function.Surjective (RingHom.fst ℝ ℝ) :=
    fun r => ⟨(r, 0), rfl⟩
  have hq : Topology.IsInducing (RingHom.fst ℝ ℝ) := ⟨rfl⟩
  have hinj : ¬Function.Injective (RingHom.fst ℝ ℝ) := by
    intro h
    have heq : ((1, 1) : ℝ × ℝ) = (1, 0) := h rfl
    exact one_ne_zero (congrArg Prod.snd heq)
  have hcoords : ∀ x : ℝ × ℝ, IsUnit x ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 := by
    intro x
    constructor
    · intro hx
      exact ⟨(hx.map (RingHom.fst ℝ ℝ)).ne_zero,
        (hx.map (RingHom.snd ℝ ℝ)).ne_zero⟩
    · intro hx
      refine ⟨⟨x, (x.1⁻¹, x.2⁻¹), ?_, ?_⟩, rfl⟩
      · ext <;> simp [hx.1, hx.2]
      · ext <;> simp [hx.1, hx.2]
  have hbad : ¬IsUnit ((1, 0) : ℝ × ℝ) := by
    intro h
    exact ((hcoords _).mp h).2 rfl
  have hlocal : ¬IsLocalHom (RingHom.fst ℝ ℝ) := by
    intro h
    have := h
    exact hbad ((isUnit_map_iff (RingHom.fst ℝ ℝ) (1, 0)).mp (by simp))
  have hopen : IsOpen {r : ℝ | IsUnit r} := by
    simpa only [isUnit_iff_ne_zero] using
      (isOpen_ne : IsOpen {r : ℝ | r ≠ 0})
  have hpre : IsOpen {x : ℝ × ℝ | x.1 ≠ 0} := by
    exact (isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).preimage hq.continuous
  refine ⟨hsurj, hq, hinj, hcoords, hlocal, hopen, hpre, ?_, ?_⟩
  · exact ⟨fun x hx => ((hcoords x).mp hx).1, fun h => hbad (h (by simp))⟩
  · intro h
    exact hlocal ((hq.isOpen_setOf_isUnit_iff hsurj).mp h).1

end RealProduct

section RealDualNumbers

local instance : TopologicalSpace (TrivSqZeroExt ℝ ℝ) :=
  TopologicalSpace.induced (TrivSqZeroExt.fstHom ℝ ℝ ℝ) inferInstance

example :
    Function.Surjective (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ∧
    Topology.IsInducing (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ∧
    ¬Function.Injective (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ∧
    (∀ z w : TrivSqZeroExt ℝ ℝ, z.fst = 0 → w.fst = 0 → z * w = 0) ∧
    (∀ z : TrivSqZeroExt ℝ ℝ, IsUnit z ↔ z.fst ≠ 0) ∧
    IsLocalHom (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ∧
    {z : TrivSqZeroExt ℝ ℝ | IsUnit z} =
      (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ⁻¹' {r : ℝ | IsUnit r} ∧
    IsOpen {r : ℝ | IsUnit r} ∧
    IsOpen {z : TrivSqZeroExt ℝ ℝ | IsUnit z} := by
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom ℝ ℝ ℝ) :=
    fun r => ⟨⟨r, 0⟩, rfl⟩
  have hq : Topology.IsInducing (TrivSqZeroExt.fstHom ℝ ℝ ℝ) := ⟨rfl⟩
  have hinj : ¬Function.Injective (TrivSqZeroExt.fstHom ℝ ℝ ℝ) := by
    intro h
    have heq : (⟨0, 1⟩ : TrivSqZeroExt ℝ ℝ) = 0 := h rfl
    exact one_ne_zero (congrArg TrivSqZeroExt.snd heq)
  have hsq : ∀ z w : TrivSqZeroExt ℝ ℝ, z.fst = 0 → w.fst = 0 → z * w = 0 := by
    intro z w hz hw
    ext <;> simp [hz, hw]
  have hnil : ∀ z : TrivSqZeroExt ℝ ℝ,
      (TrivSqZeroExt.fstHom ℝ ℝ ℝ) z = 0 → IsNilpotent z := by
    intro z hz
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact hsq z z hz hz
  have hlocal : IsLocalHom (TrivSqZeroExt.fstHom ℝ ℝ ℝ) :=
    IsLocalHom.of_surjective_of_isNilpotent_ker
      (TrivSqZeroExt.fstHom ℝ ℝ ℝ) hsurj hnil
  have hreflect : ∀ z : TrivSqZeroExt ℝ ℝ,
      IsUnit ((TrivSqZeroExt.fstHom ℝ ℝ ℝ) z) → IsUnit z := by
    have := hlocal
    intro z hz
    exact (isUnit_map_iff (TrivSqZeroExt.fstHom ℝ ℝ ℝ) z).mp hz
  have hcoords : ∀ z : TrivSqZeroExt ℝ ℝ, IsUnit z ↔ z.fst ≠ 0 := by
    intro z
    exact ⟨fun hz => (hz.map (TrivSqZeroExt.fstHom ℝ ℝ ℝ)).ne_zero,
      fun hz => hreflect z (isUnit_iff_ne_zero.mpr hz)⟩
  have hpre : {z : TrivSqZeroExt ℝ ℝ | IsUnit z} =
      (TrivSqZeroExt.fstHom ℝ ℝ ℝ) ⁻¹' {r : ℝ | IsUnit r} := by
    ext z
    exact ⟨fun hz => hz.map (TrivSqZeroExt.fstHom ℝ ℝ ℝ), hreflect z⟩
  have hopen : IsOpen {r : ℝ | IsUnit r} := by
    simpa only [isUnit_iff_ne_zero] using
      (isOpen_ne : IsOpen {r : ℝ | r ≠ 0})
  exact ⟨hsurj, hq, hinj, hsq, hcoords, hlocal, hpre, hopen,
    (hq.isOpen_setOf_isUnit_iff hsurj).mpr ⟨hlocal, hopen⟩⟩

end RealDualNumbers
