/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import VectorBundles.Topology.FiberBundle.ClosedCylinder

/-!
# Linear coordinates on the original fibers of a closed cylinder

For a projection `p : Z → X × T`, suppose each original fiber `{z // p z = b}`
has a given module structure over a semiring `R`. The two closed-piece charts
may have different models `F` and `G`. Given linear equivalences from the
original fibers to those models, compatible with the supplied chart
coordinates, `glueClosedCylinderFiberLinearEquiv` gives linear coordinates
for the raw glued homeomorphism.

The construction retains the given linear equivalence on every left fiber,
including the seam. On the right it composes the given right equivalence
with the linear coordinate change through the original seam fiber at the
same `X` coordinate. The forward and inverse coordinate theorems identify
these equivalences with the existing raw homeomorphism; there is no second
topological gluing construction.

## Implementation notes

The module structures on the original projection fibers are inputs, not
structures transported from the glued homeomorphism. The scalar semiring
need not be commutative and has no topology. No continuity of addition or
scalar multiplication, separation property, rank, or nonemptiness hypothesis
is imposed. The result is an algebraic refinement of the two-piece raw
closed-cylinder construction, not a homotopy theorem.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
  The topological construction is in `ClosedCylinder`; here only its
  original-fiber linear refinement is constructed.
-/

@[expose] public section

universe uX uT uZ uF uG uR

namespace Bundle.Trivialization

variable {X : Type uX} {T : Type uT} {Z : Type uZ}
  {F : Type uF} {G : Type uG} {R : Type uR}
  [LinearOrder T] [Semiring R]
  [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
  (c : T) (p : Z → X × T)
  [∀ b : X × T, AddCommMonoid {z : Z // p z = b}]
  [∀ b : X × T, Module R {z : Z // p z = b}]
  (L₁ : ∀ (b : X × T), b.2 ≤ c → {z : Z // p z = b} ≃ₗ[R] F)
  (L₂ : ∀ (b : X × T), c ≤ b.2 → {z : Z // p z = b} ≃ₗ[R] G)

/-- The linear change from right to left coordinates through the original
fiber at `(x, c)`. -/
def closedCylinderCoordChangeLinearEquiv (x : X) : G ≃ₗ[R] F :=
  (L₂ (x, c) le_rfl).symm.trans (L₁ (x, c) le_rfl)

/-- The seam linear coordinate change is the composition through the given
right seam equivalence and the given left seam equivalence. -/
@[simp] theorem closedCylinderCoordChangeLinearEquiv_apply (x : X) (g : G) :
    closedCylinderCoordChangeLinearEquiv c p L₁ L₂ x g =
      L₁ (x, c) le_rfl ((L₂ (x, c) le_rfl).symm g) :=
  rfl

/-- Linear coordinates on each original projection fiber of a closed cylinder.

Every left fiber keeps its supplied equivalence. A right fiber first uses
its supplied right coordinates, then the seam change at the same `X` coordinate.
The original fiber module structures are unchanged. -/
def glueClosedCylinderFiberLinearEquiv (b : X × T) : {z : Z // p z = b} ≃ₗ[R] F :=
  if hb : b.2 ≤ c then L₁ b hb
  else (L₂ b (le_of_not_ge hb)).trans
    (closedCylinderCoordChangeLinearEquiv c p L₁ L₂ b.1)

/-- The linear refinement retains the supplied equivalence on the whole left
prefix, not only at the seam. -/
theorem glueClosedCylinderFiberLinearEquiv_left (b : X × T) (hb : b.2 ≤ c) :
    glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b = L₁ b hb := by
  simp only [glueClosedCylinderFiberLinearEquiv, dite_eq_left hb]

/-- Off the left prefix, the linear refinement uses the right coordinates
followed by the seam change at the same `X` coordinate. -/
theorem glueClosedCylinderFiberLinearEquiv_of_not_le (b : X × T) (hb : ¬ b.2 ≤ c) :
    glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b =
      (L₂ b (le_of_not_ge hb)).trans
        (closedCylinderCoordChangeLinearEquiv c p L₁ L₂ b.1) := by
  simp only [glueClosedCylinderFiberLinearEquiv, dite_eq_right hb]

section Topology

variable [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
  [TopologicalSpace F] [TopologicalSpace G]
  (h₁ : (p ⁻¹' {b : X × T | b.2 ≤ c}) ≃ₜ {b : X × T | b.2 ≤ c} × F)
  (h₂ : (p ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × G)
  (hp₁ : ∀ z : p ⁻¹' {b : X × T | b.2 ≤ c}, (h₁ z).1.val = p z.val)
  (hp₂ : ∀ z : p ⁻¹' {b : X × T | c ≤ b.2}, (h₂ z).1.val = p z.val)
  (hL₁ : ∀ (b : X × T) (hb : b.2 ≤ c) (v : {z : Z // p z = b}),
    L₁ b hb v =
      (h₁ ⟨v.val, Eq.mpr (congrArg (fun a : X × T ↦ a.2 ≤ c) v.property) hb⟩).2)
  (hL₂ : ∀ (b : X × T) (hb : c ≤ b.2) (v : {z : Z // p z = b}),
    L₂ b hb v =
      (h₂ ⟨v.val, Eq.mpr (congrArg (fun a : X × T ↦ c ≤ a.2) v.property) hb⟩).2)

include hL₁ hL₂

/-- The given seam linear equivalences realize the public topological seam
coordinate change on every right coordinate. -/
theorem closedCylinderCoordChangeLinearEquiv_apply_eq (x : X) (g : G) :
    closedCylinderCoordChangeLinearEquiv c p L₁ L₂ x g =
      closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ x g := by
  let v : {z : Z // p z = (x, c)} := (L₂ (x, c) le_rfl).symm g
  have hs := closedCylinderCoordChange_apply c p h₁ h₂ hp₁ hp₂ x v.val v.property
  have hr :
      (h₂ ⟨v.val,
        Eq.mpr (congrArg (fun a : X × T ↦ c ≤ a.2) v.property) le_rfl⟩).2 = g :=
    (hL₂ (x, c) le_rfl v).symm.trans ((L₂ (x, c) le_rfl).apply_symm_apply g)
  change L₁ (x, c) le_rfl v = _
  calc
    L₁ (x, c) le_rfl v =
        (h₁ ⟨v.val,
          Eq.mpr (congrArg (fun a : X × T ↦ a.2 ≤ c) v.property) le_rfl⟩).2 :=
      hL₁ (x, c) le_rfl v
    _ = closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ x
        (h₂ ⟨v.val,
          Eq.mpr (congrArg (fun a : X × T ↦ c ≤ a.2) v.property) le_rfl⟩).2 :=
      hs.symm
    _ = closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ x g :=
      congrArg (closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ x) hr

variable [ClosedIicTopology T] [ClosedIciTopology T] (hπ : Continuous p)

/-- On an original projection fiber, the linear coordinates are exactly the
second coordinates of the raw glued homeomorphism. -/
theorem glueClosedCylinderFiberLinearEquiv_apply (b : X × T) (v : {z : Z // p z = b}) :
    glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b v =
      (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ v.val).2 := by
  by_cases hb : b.2 ≤ c
  · rw [glueClosedCylinderFiberLinearEquiv_left c p L₁ L₂ b hb, hL₁ b hb v]
    exact (congrArg Prod.snd
      (glueClosedCylinderHomeomorph_apply_left c p h₁ h₂ hp₁ hp₂ hπ v.val
        (Eq.mpr (congrArg (fun a : X × T ↦ a.2 ≤ c) v.property) hb))).symm
  · rw [glueClosedCylinderFiberLinearEquiv_of_not_le c p L₁ L₂ b hb,
      LinearEquiv.trans_apply,
      closedCylinderCoordChangeLinearEquiv_apply_eq c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂,
      hL₂ b (le_of_not_ge hb) v]
    have hr := congrArg Prod.snd
      (glueClosedCylinderHomeomorph_apply_right c p h₁ h₂ hp₁ hp₂ hπ v.val
        (Eq.mpr (congrArg (fun a : X × T ↦ c ≤ a.2) v.property) (le_of_not_ge hb)))
    have hbase : (p v.val).1 = b.1 := congrArg Prod.fst v.property
    rw [hbase] at hr
    exact hr.symm

/-- The full raw glued chart on an original fiber is its original base point
paired with the constructed linear coordinates. -/
theorem glueClosedCylinderHomeomorph_apply_fiber (b : X × T)
    (v : {z : Z // p z = b}) :
    glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ v.val =
      (b, glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b v) := by
  apply Prod.ext
  · exact (glueClosedCylinderHomeomorph_proj c p h₁ h₂ hp₁ hp₂ hπ v.val).trans v.property
  · exact (glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂
      hL₁ hL₂ hπ b v).symm

/-- The inverse raw glued chart is the inverse linear coordinate map in the
original fiber. This uses no extension or globally chosen zero section. -/
theorem glueClosedCylinderHomeomorph_symm_apply_fiber (b : X × T) (w : F) :
    (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ).symm (b, w) =
      ((glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b).symm w).val := by
  let e := glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ
  apply e.injective
  change e (e.symm (b, w)) = e _
  rw [e.apply_symm_apply]
  have h := glueClosedCylinderHomeomorph_apply_fiber c p L₁ L₂ h₁ h₂ hp₁ hp₂
    hL₁ hL₂ hπ b ((glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The second coordinate of the glued chart preserves the given zero of each
original projection fiber. -/
theorem glueClosedCylinderHomeomorph_snd_zero (b : X × T) :
    (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ
      (0 : {z : Z // p z = b}).val).2 = 0 := by
  rw [← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b
    (0 : {z : Z // p z = b})]
  exact (glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b).toLinearMap.map_zero

/-- The second coordinate of the glued chart preserves addition in each given
original projection fiber. -/
theorem glueClosedCylinderHomeomorph_snd_add (b : X × T)
    (v w : {z : Z // p z = b}) :
    (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ (v + w).val).2 =
      (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ v.val).2 +
        (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ w.val).2 := by
  rw [← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b
      (v + w),
    ← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b v,
    ← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b w]
  exact (glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b).toLinearMap.map_add v w

/-- The second coordinate of the glued chart preserves scalar multiplication
in each given original projection fiber, over an arbitrary semiring. -/
theorem glueClosedCylinderHomeomorph_snd_smul (b : X × T) (r : R)
    (v : {z : Z // p z = b}) :
    (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ (r • v).val).2 =
      r • (glueClosedCylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ v.val).2 := by
  rw [← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b
      (r • v),
    ← glueClosedCylinderFiberLinearEquiv_apply c p L₁ L₂ h₁ h₂ hp₁ hp₂ hL₁ hL₂ hπ b v]
  exact (glueClosedCylinderFiberLinearEquiv c p L₁ L₂ b).toLinearMap.map_smul r v

end Topology

end Bundle.Trivialization
