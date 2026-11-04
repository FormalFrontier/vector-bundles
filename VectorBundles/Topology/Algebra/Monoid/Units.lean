module

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Topology.Maps.Basic

/-!
# Open unit loci and inducing homomorphisms

For a surjective inducing monoid homomorphism, openness of the source unit locus
is equivalent to unit reflection together with openness of the target unit locus.
No compatibility between multiplication and the topologies is required.
-/

@[expose] public section

universe u v w

namespace Topology

variable {M : Type u} {N : Type v} {F : Type w}
  [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
  [FunLike F M N] [MonoidHomClass F M N] {q : F}

/-- For a surjective inducing monoid homomorphism, the source unit locus is open
if and only if the homomorphism is local and the target unit locus is open.
The monoids and their topologies are arbitrary. -/
theorem IsInducing.isOpen_setOf_isUnit_iff
    (hq : IsInducing (q : M → N)) (hsurj : Function.Surjective q) :
    IsOpen {m : M | IsUnit m} ↔ IsLocalHom q ∧ IsOpen {n : N | IsUnit n} := by
  classical
  constructor
  · intro hopen
    obtain ⟨V, hV, hpre⟩ := hq.isOpen_iff.mp hopen
    have hmem (a : M) : IsUnit a ↔ q a ∈ V := by
      change a ∈ {m : M | IsUnit m} ↔ a ∈ q ⁻¹' V
      rw [hpre]
    have hfiber (a : M) (ha : q a = 1) : IsUnit a := by
      apply (hmem a).mpr
      have h1 := (hmem (1 : M)).mp isUnit_one
      simpa only [map_one, ha] using h1
    have hreflect (a : M) (ha : IsUnit (q a)) : IsUnit a := by
      obtain ⟨u, hu⟩ := ha
      obtain ⟨b, hb⟩ := hsurj (↑(u⁻¹) : N)
      obtain ⟨v, hv⟩ := hfiber (a * b) (by simp [map_mul, ← hu, hb])
      obtain ⟨w, hw⟩ := hfiber (b * a) (by simp [map_mul, ← hu, hb])
      have hr : a * (b * ↑(v⁻¹)) = 1 := by
        rw [← mul_assoc, ← hv]
        exact v.val_inv
      have hl : (↑(w⁻¹) * b) * a = 1 := by
        rw [mul_assoc, ← hw]
        exact w.inv_val
      have hinv : (↑(w⁻¹) : M) * b = b * ↑(v⁻¹) := by
        calc
          (↑(w⁻¹) : M) * b =
              ((↑(w⁻¹) : M) * b) * (a * (b * ↑(v⁻¹))) := by rw [hr, mul_one]
          _ = (((↑(w⁻¹) : M) * b) * a) * (b * ↑(v⁻¹)) :=
            (mul_assoc _ _ _).symm
          _ = b * ↑(v⁻¹) := by rw [hl, one_mul]
      refine ⟨⟨a, b * ↑(v⁻¹), hr, ?_⟩, rfl⟩
      rw [← hinv]
      exact hl
    have hlocal : IsLocalHom q := by
      constructor
      intro a
      simpa only [not_imp_not] using hreflect a
    refine ⟨hlocal, ?_⟩
    have htarget : V = {n : N | IsUnit n} := by
      ext n
      obtain ⟨a, rfl⟩ := hsurj n
      exact ⟨fun ha => ((hmem a).mpr ha).map q,
        fun ha => (hmem a).mp (hreflect a ha)⟩
    simpa only [htarget] using hV
  · rintro ⟨hlocal, hopen⟩
    have := hlocal
    have hpre : q ⁻¹' {n : N | IsUnit n} = {m : M | IsUnit m} := by
      ext a
      exact isUnit_map_iff q a
    rw [← hpre]
    exact hopen.preimage hq.continuous

end Topology
