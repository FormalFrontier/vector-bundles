/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.UnitInterval
public import VectorBundles.Topology.FiberBundle.Pullback
public import VectorBundles.Topology.FiberBundle.SupportedTransport

/-!
# Finite ordered transport over a cylinder

Given charts indexed by `Fin n` covering cylinders `U j × I` and continuous real
weights in `[0, 1]` summing to one, with `closure {x | w j x ≠ 0} ⊆ U j`,
transport from zero time by applying the supported chart steps in increasing
index order. Chart models and their topologies may vary with the index,
independently of the unstructured dummy parameter `P` of the total space.

`Bundle.Trivialization.finiteCylinderTransport` starts at the iterated standard
pullback of the entire original zero-time restriction, not at a weight-dependent
stage, and ends at the same given total space with its original topology. The
sets `U j` must cover `X`. The comparisons at the first and last stages use
`Pullback.homeomorphComp` and `Pullback.homeomorphId`, with transport along
equalities of base maps. Continuity of the original projection is derived locally
from the covering charts. Both directions preserve the whole cylinder base point
and fix every bottom point, including points in the closed supports: consecutive
clocks agree there, and the chart lift of a point to its own base is that point.

`Bundle.Trivialization.cylinderPrefixMap` describes each prefix clock.
`Bundle.Trivialization.finiteCylinderPrefixTransport` exposes the ordered
prefixes with the same fixed source. Its lifted zero and successor formulas
specify the chart-coordinate change on each closed support and the unchanged
original point off that support. The full transport is the canonical lift of the
last prefix; each lifted prefix fixes every original bottom point.

Given modules over a possibly noncommutative semiring `R` on the original fibers
and on every chart model, and linear coordinate equivalences agreeing with the
charts, `finiteCylinderTransport_isLinearMap_of_coordinates` proves linearity
from `E (x, 0)` to `E (x, t)` for this same ordered transport. Real weights change
time only; no topology on `R` or continuity of module operations is required.

`Bundle.Trivialization.finiteCylinderEndpointTransport` independently composes
the supported chart steps on `X`, from the standard zero-time pullback to the
standard one-time pullback, without a separate cover or projection-continuity
assumption. The top-slice formula for cylinder transport follows
from the naturality of each supported step and an ordered induction.

## Limitations

The weighted construction needs neither normality of `X` nor openness of the
auxiliary sets `U j`. It uses given weights with the bounds, sum and closed-cozero
subordination above. No common model, rank, finite-dimensionality, scalar field,
separation or nonempty-fiber hypothesis is required. These family constructions
do not themselves choose weights or compare an arbitrary space with the total
space of the fibers of its projection; those are supplied by the `Existence` and
`Projection` modules. There is no assertion of independence from weights or chart
order, or of homotopy invariance for arbitrary bundles.

## References

- Mathlib's `Mathlib.Data.Bundle`, `Mathlib.Topology.FiberBundle.Trivialization`
  and `Mathlib.Topology.FiberBundle.Constructions` supply the dependent families,
  chart lifts and pullback topologies. The standard pullback comparisons use
  `Bundle.Pullback.homeomorphComp` and `Bundle.Pullback.homeomorphId` from
  `VectorBundles.Topology.FiberBundle.Pullback`; supported chart steps use
  `VectorBundles.Topology.FiberBundle.SupportedTransport`.
- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.7, is a motivating comparison problem only. The discussion on
  printed p. 20 (PDF p. 24) motivates subordinate weights. Here finitely many
  ordered cylinder charts and weights are given, while the fiberwise algebra
  allows arbitrary semirings and varying chart models; this is not the full
  proposition.
-/

@[expose] public section

open Bundle Set
open scoped BigOperators unitInterval

namespace Bundle.Trivialization

universe uX uP uF uE

section Prefixes

variable {X : Type uX} [TopologicalSpace X] {n : ℕ}

private noncomputable def timePrefix (w : Fin n → C(X, ℝ)) (k : ℕ) (x : X) : ℝ :=
  ∑ i : Fin n, if i.val < k then w i x else 0

private theorem timePrefix_continuous (w : Fin n → C(X, ℝ)) (k : ℕ) :
    Continuous (timePrefix w k) := by
  classical
  apply continuous_finsetSum
  intro i _
  by_cases hi : i.val < k
  · simpa only [ite_eq_left hi] using (w i).continuous
  · simpa only [ite_eq_right hi] using (continuous_const : Continuous (fun _ : X ↦ (0 : ℝ)))

private theorem timePrefix_mem (w : Fin n → C(X, ℝ))
    (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) (hsum : ∀ x, ∑ i, w i x = 1)
    (k : ℕ) (x : X) : timePrefix w k x ∈ I := by
  classical
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ by
      split_ifs
      · exact (hw i x).1
      · exact le_rfl
  · calc
      timePrefix w k x ≤ ∑ i, w i x := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact le_rfl
        · exact (hw i x).1
      _ = 1 := hsum x

/-- The clock that has used exactly the weights with index less than `k`.
Every natural `k` is allowed; at `0` this is zero time and at `n` it is the
identity. The finite transport uses only the stages from `0` through `n`. -/
noncomputable def cylinderPrefixMap (w : Fin n → C(X, ℝ))
    (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) (hsum : ∀ x, ∑ i, w i x = 1)
    (k : ℕ) : C(X × I, X × I) where
  toFun := private_decl% (show X × I → X × I from fun b ↦
    (b.1, ⟨(b.2 : ℝ) * timePrefix w k b.1,
      unitInterval.mul_mem b.2.property (timePrefix_mem w hw hsum k b.1)⟩))
  continuous_toFun := by
    exact continuous_fst.prodMk
      (((continuous_subtype_val.comp continuous_snd).mul
        ((timePrefix_continuous w k).comp continuous_fst)).subtype_mk
          (fun b ↦ unitInterval.mul_mem b.2.property (timePrefix_mem w hw hsum k b.1)))

variable (w : Fin n → C(X, ℝ)) (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1)
  (hsum : ∀ x, ∑ i, w i x = 1)

/-- Prefix clocks preserve the spatial coordinate. -/
@[simp] theorem cylinderPrefixMap_fst (k : ℕ) (b : X × I) :
    (cylinderPrefixMap w hw hsum k b).1 = b.1 := by
  rfl

/-- The prefix time is the original time multiplied by the partial weight sum. -/
theorem cylinderPrefixMap_snd_coe (k : ℕ) (b : X × I) :
    ((cylinderPrefixMap w hw hsum k b).2 : ℝ) =
      (b.2 : ℝ) * ∑ j : Fin n, if j.val < k then w j b.1 else 0 := by
  rfl

/-- The first clock is the zero-time retraction. -/
@[simp] theorem cylinderPrefixMap_zero_apply (b : X × I) :
    cylinderPrefixMap w hw hsum 0 b = (b.1, 0) := by
  apply Prod.ext
  · exact cylinderPrefixMap_fst w hw hsum 0 b
  · apply Subtype.ext
    change (b.2 : ℝ) * timePrefix w 0 b.1 = 0
    simp [timePrefix]

/-- After all weights have been used, the clock is the original time. -/
@[simp] theorem cylinderPrefixMap_last_apply (b : X × I) :
    cylinderPrefixMap w hw hsum n b = b := by
  apply Prod.ext
  · exact cylinderPrefixMap_fst w hw hsum n b
  · apply Subtype.ext
    change (b.2 : ℝ) * timePrefix w n b.1 = (b.2 : ℝ)
    simp [timePrefix, hsum]

/-- Every prefix clock fixes zero time, regardless of the supports. -/
@[simp] theorem cylinderPrefixMap_apply_bottom (k : ℕ) (x : X) :
    cylinderPrefixMap w hw hsum k (x, 0) = (x, 0) := by
  apply Prod.ext
  · exact cylinderPrefixMap_fst w hw hsum k (x, 0)
  · apply Subtype.ext
    change (0 : ℝ) * timePrefix w k x = 0
    exact zero_mul _

private theorem timePrefix_succ_of_zero (j : Fin n) (x : X) (hx : w j x = 0) :
    timePrefix w j.val x = timePrefix w (j.val + 1) x := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < j.val
  · simp only [ite_eq_left hi, ite_eq_left (Nat.lt_succ_of_lt hi)]
  · by_cases hi' : i.val < j.val + 1
    · have hij : i = j := Fin.ext (Nat.eq_of_lt_succ_of_not_lt hi' hi)
      subst i
      simp [hx]
    · simp only [ite_eq_right hi, ite_eq_right hi']

private theorem cylinderPrefixMap_eqOn (j : Fin n) :
    EqOn (cylinderPrefixMap w hw hsum j.val : X × I → X × I)
      (cylinderPrefixMap w hw hsum (j.val + 1))
      (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))ᶜ := by
  intro b hb
  have hx : w j b.1 = 0 := by
    by_contra h
    exact hb ⟨subset_closure h, mem_univ _⟩
  apply Prod.ext
  · rw [cylinderPrefixMap_fst, cylinderPrefixMap_fst]
  · apply Subtype.ext
    exact congrArg (fun r : ℝ ↦ (b.2 : ℝ) * r) (timePrefix_succ_of_zero w j b.1 hx)

end Prefixes

/-! Equality of base maps transports both the family and its standard pullback
 topology. These comparisons are not identifications of arbitrary topologies. -/

private def pullbackCongr {A B : Type*} [TopologicalSpace A]
    (P : Type uP) (E : B → Type uE) [TopologicalSpace (TotalSpace P E)]
    (f g : A → B) (h : f = g) : TotalSpace P (f *ᵖ E) ≃ₜ TotalSpace P (g *ᵖ E) := by
  subst g
  exact Homeomorph.refl _

private theorem pullbackCongr_proj {A B : Type*} [TopologicalSpace A]
    (P : Type uP) (E : B → Type uE) [TopologicalSpace (TotalSpace P E)]
    (f g : A → B) (h : f = g) (z : TotalSpace P (f *ᵖ E)) :
    (pullbackCongr P E f g h z).proj = z.proj := by
  subst g
  rfl

private theorem pullbackCongr_lift {A B : Type*} [TopologicalSpace A]
    (P : Type uP) (E : B → Type uE) [TopologicalSpace (TotalSpace P E)]
    (f g : A → B) (h : f = g) (z : TotalSpace P (f *ᵖ E)) :
    Pullback.lift g (pullbackCongr P E f g h z) = Pullback.lift f z := by
  subst g
  rfl

/-- Compose a finite chain of homeomorphisms in increasing index order. -/
private noncomputable def orderedHomeomorphChain {n : ℕ} (Y : ℕ → Type*)
    [∀ k, TopologicalSpace (Y k)] (step : ∀ j : Fin n, Y j.val ≃ₜ Y (j.val + 1)) :
    (k : ℕ) → (hk : k ≤ n) → Y 0 ≃ₜ Y k
  | 0, _ => Homeomorph.refl _
  | k + 1, hk =>
      (orderedHomeomorphChain Y step k (Nat.le_of_succ_le hk)).trans (step ⟨k, hk⟩)

section Assembly

variable {X : Type uX} [TopologicalSpace X] {P : Type uP} {n : ℕ}
  {F : Fin n → Type uF} {E : X × I → Type uE}
  [∀ j, TopologicalSpace (F j)] [TopologicalSpace (TotalSpace P E)]

variable (e : ∀ j, Trivialization (F j) (π P E)) (U : Fin n → Set X)
  (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
  (w : Fin n → C(X, ℝ)) (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1)
  (hsum : ∀ x, ∑ i, w i x = 1)
  (hsupport : ∀ j, closure {x | w j x ≠ 0} ⊆ U j)

local notation "q" => cylinderPrefixMap w hw hsum

include hchart hsupport in
private theorem cylinderPrefixMap_mapsTo (j : Fin n) (k : ℕ) :
    MapsTo (q k) (closure {x | w j x ≠ 0} ×ˢ (univ : Set I)) (e j).baseSet := by
  intro b hb
  exact hchart j ⟨hsupport j hb.1, mem_univ _⟩

private noncomputable def cylinderStep (j : Fin n) :
    TotalSpace P ((q j.val : X × I → X × I) *ᵖ E) ≃ₜ
      TotalSpace P ((q (j.val + 1) : X × I → X × I) *ᵖ E) :=
  (e j).supportedPullbackHomeomorph (q j.val) (q (j.val + 1))
    (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
    (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1))

private theorem cylinderStep_proj (j : Fin n)
    (z : TotalSpace P ((q j.val : X × I → X × I) *ᵖ E)) :
    (cylinderStep e U hchart w hw hsum hsupport j z).proj = z.proj := by
  exact (e j).supportedPullbackHomeomorph_proj (q j.val) (q (j.val + 1))
    (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
    (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1)) z

private theorem cylinderStep_lift_bottom (j : Fin n)
    (z : TotalSpace P ((q j.val : X × I → X × I) *ᵖ E)) (hz : z.proj.2 = 0) :
    Pullback.lift (q (j.val + 1)) (cylinderStep e U hchart w hw hsum hsupport j z) =
      Pullback.lift (q j.val) z := by
  let K := closure {x | w j x ≠ 0} ×ˢ (univ : Set I)
  have h₀ := cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val
  have h₁ := cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1)
  change Pullback.lift (q (j.val + 1))
    ((e j).supportedPullbackHomeomorph (q j.val) (q (j.val + 1)) K
      (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j) h₀ h₁ z) = _
  by_cases h : z.proj ∈ K
  · rw [(e j).supportedPullbackHomeomorph_lift_of_mem (q j.val) (q (j.val + 1)) K
      (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
      h₀ h₁ z ⟨h₀ h, h₁ h⟩]
    have hb : z.proj = (z.proj.1, 0) := Prod.ext rfl hz
    have heq : q (j.val + 1) z.proj = q j.val z.proj := by
      rw [hb, cylinderPrefixMap_apply_bottom, cylinderPrefixMap_apply_bottom]
    rw [heq]
    exact Trivialization.lift_self (T := e j) (z := Pullback.lift (q j.val) z) (h₀ h)
  · exact (e j).supportedPullbackHomeomorph_lift_of_notMem (q j.val) (q (j.val + 1)) K
      (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j) h₀ h₁ z h

/-- The recursion appends the `k`-th step on the right; no chart steps are reordered. -/
private noncomputable def cylinderStages : (k : ℕ) → (hk : k ≤ n) →
    TotalSpace P ((q 0 : X × I → X × I) *ᵖ E) ≃ₜ
      TotalSpace P ((q k : X × I → X × I) *ᵖ E) :=
  orderedHomeomorphChain (fun k ↦ TotalSpace P ((q k : X × I → X × I) *ᵖ E))
    (cylinderStep e U hchart w hw hsum hsupport)

private theorem cylinderStages_proj : ∀ (k : ℕ) (hk : k ≤ n)
    (z : TotalSpace P ((q 0 : X × I → X × I) *ᵖ E)),
    (cylinderStages e U hchart w hw hsum hsupport k hk z).proj = z.proj := by
  intro k
  induction k with
  | zero => intro hk z; rfl
  | succ k ih =>
      intro hk z
      change (cylinderStep e U hchart w hw hsum hsupport ⟨k, hk⟩
        (cylinderStages e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk) z)).proj = _
      rw [cylinderStep_proj]
      exact ih (Nat.le_of_succ_le hk) z

private theorem cylinderStages_lift_bottom : ∀ (k : ℕ) (hk : k ≤ n)
    (z : TotalSpace P ((q 0 : X × I → X × I) *ᵖ E)), z.proj.2 = 0 →
    Pullback.lift (q k) (cylinderStages e U hchart w hw hsum hsupport k hk z) =
      Pullback.lift (q 0) z := by
  intro k
  induction k with
  | zero => intro hk z hz; rfl
  | succ k ih =>
      intro hk z hz
      change Pullback.lift (q (k + 1))
        (cylinderStep e U hchart w hw hsum hsupport ⟨k, hk⟩
          (cylinderStages e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk) z)) = _
      rw [cylinderStep_lift_bottom e U hchart w hw hsum hsupport ⟨k, hk⟩
        (cylinderStages e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk) z)
        (by simpa only [cylinderStages_proj] using hz)]
      exact ih (Nat.le_of_succ_le hk) z hz

private noncomputable def cylinderZeroComparison :
    TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
      TotalSpace P ((q 0 : X × I → X × I) *ᵖ E) :=
  (Pullback.homeomorphComp P E (fun x : X ↦ (x, (0 : I))) (Prod.fst : X × I → X)
    (continuous_fst.comp (Pullback.continuous_proj P E
      ((fun x : X ↦ (x, (0 : I))) ∘ (Prod.fst : X × I → X))))).trans
    (pullbackCongr P E ((fun x : X ↦ (x, (0 : I))) ∘ (Prod.fst : X × I → X)) (q 0)
      (by funext b; exact (cylinderPrefixMap_zero_apply w hw hsum b).symm))

private theorem cylinderZeroComparison_proj
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    (cylinderZeroComparison (P := P) (E := E) w hw hsum z).proj = z.proj := by
  simp only [cylinderZeroComparison, Homeomorph.trans_apply, pullbackCongr_proj,
    Pullback.homeomorphComp_apply_proj]

private theorem cylinderZeroComparison_lift
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    Pullback.lift (q 0) (cylinderZeroComparison (P := P) (E := E) w hw hsum z) =
      Pullback.lift (fun x : X ↦ (x, (0 : I))) (Pullback.lift Prod.fst z) := by
  simp only [cylinderZeroComparison, Homeomorph.trans_apply, pullbackCongr_lift,
    Pullback.lift_homeomorphComp]

include hchart in
private theorem continuous_proj_of_cylinder_cover (hcover : (⋃ j, U j) = univ) :
    Continuous (π P E) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hz : z.proj.1 ∈ ⋃ j, U j := by rw [hcover]; exact mem_univ _
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  exact (e j).continuousAt_proj ((e j).mem_source.mpr (hchart j ⟨hj, mem_univ _⟩))

private noncomputable def cylinderLastComparison (hπ : Continuous (π P E)) :
    TotalSpace P ((q n : X × I → X × I) *ᵖ E) ≃ₜ TotalSpace P E :=
  (pullbackCongr P E (q n) id
    (by funext b; exact cylinderPrefixMap_last_apply w hw hsum b)).trans
    (Pullback.homeomorphId P E hπ)

private theorem cylinderLastComparison_proj (hπ : Continuous (π P E))
    (z : TotalSpace P ((q n : X × I → X × I) *ᵖ E)) :
    (cylinderLastComparison (P := P) (E := E) w hw hsum hπ z).proj = z.proj := by
  simp only [cylinderLastComparison, Homeomorph.trans_apply, Pullback.homeomorphId_apply_proj,
    pullbackCongr_proj]

private theorem cylinderLastComparison_lift (hπ : Continuous (π P E))
    (z : TotalSpace P ((q n : X × I → X × I) *ᵖ E)) :
    cylinderLastComparison (P := P) (E := E) w hw hsum hπ z = Pullback.lift (q n) z := by
  simp only [cylinderLastComparison, Homeomorph.trans_apply, Pullback.homeomorphId_apply,
    pullbackCongr_lift]

/-- The first `k` supported cylinder steps, in increasing chart-index order.

The source is the fixed iterated standard pullback of the original zero-time
restriction. The target is the standard pullback along the `k`-th prefix clock.
The equality comparison at zero time is the same for every prefix. -/
noncomputable def finiteCylinderPrefixTransport (k : ℕ) (hk : k ≤ n) :
    TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
      TotalSpace P ((q k : X × I → X × I) *ᵖ E) := private_decl% (show
    TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
      TotalSpace P ((q k : X × I → X × I) *ᵖ E) from
  (cylinderZeroComparison (P := P) (E := E) w hw hsum).trans
    (cylinderStages e U hchart w hw hsum hsupport k hk))

/-- Every prefix preserves the entire cylinder base point. -/
@[simp] theorem finiteCylinderPrefixTransport_proj (k : ℕ) (hk : k ≤ n)
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport k hk z).proj =
      z.proj := by
  change (cylinderStages e U hchart w hw hsum hsupport k hk
    (cylinderZeroComparison (P := P) (E := E) w hw hsum z)).proj = z.proj
  rw [cylinderStages_proj, cylinderZeroComparison_proj]

/-- Before any chart step, lifting a prefix is the canonical lift from the
iterated zero-time pullback to the original total space. -/
@[simp] theorem finiteCylinderPrefixTransport_lift_zero
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    Pullback.lift (q 0)
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport 0 (Nat.zero_le n) z) =
      Pullback.lift (fun x : X ↦ (x, (0 : I))) (Pullback.lift Prod.fst z) := by
  change Pullback.lift (q 0)
    (cylinderZeroComparison (P := P) (E := E) w hw hsum z) = _
  exact cylinderZeroComparison_lift (P := P) (E := E) w hw hsum z

/-- On the closed support of weight `j`, the next prefix retains chart `j`'s
fiber coordinate of the preceding lifted point and changes its clock. -/
theorem finiteCylinderPrefixTransport_lift_succ_of_mem (j : Fin n)
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))
    (hz : z.proj.1 ∈ closure {x | w j x ≠ 0}) :
    Pullback.lift (q (j.val + 1))
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
          (j.val + 1) j.isLt z) =
      (e j).lift
        (Pullback.lift (q j.val)
          (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
            j.val (Nat.le_of_lt j.isLt) z))
        (q (j.val + 1) z.proj) := by
  have hzK : (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
      j.val (Nat.le_of_lt j.isLt) z).proj ∈
        closure {x | w j x ≠ 0} ×ˢ (univ : Set I) := by
    rw [finiteCylinderPrefixTransport_proj]
    exact ⟨hz, mem_univ _⟩
  change Pullback.lift (q (j.val + 1))
    (cylinderStep e U hchart w hw hsum hsupport j
      (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
        j.val (Nat.le_of_lt j.isLt) z)) = _
  have h := (e j).supportedPullbackHomeomorph_lift_of_mem (q j.val) (q (j.val + 1))
    (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
    (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1))
    (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
      j.val (Nat.le_of_lt j.isLt) z)
    ⟨cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val hzK,
      cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1) hzK⟩
  simpa only [cylinderStep, finiteCylinderPrefixTransport_proj] using h

/-- Off the closed support of weight `j`, the next prefix leaves the preceding
point of the original total space unchanged. -/
theorem finiteCylinderPrefixTransport_lift_succ_of_notMem (j : Fin n)
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))
    (hz : z.proj.1 ∉ closure {x | w j x ≠ 0}) :
    Pullback.lift (q (j.val + 1))
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
          (j.val + 1) j.isLt z) =
      Pullback.lift (q j.val)
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
          j.val (Nat.le_of_lt j.isLt) z) := by
  have hzK : (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
      j.val (Nat.le_of_lt j.isLt) z).proj ∉
        closure {x | w j x ≠ 0} ×ˢ (univ : Set I) := by
    rw [finiteCylinderPrefixTransport_proj]
    exact fun h ↦ hz h.1
  change Pullback.lift (q (j.val + 1))
    (cylinderStep e U hchart w hw hsum hsupport j
      (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
        j.val (Nat.le_of_lt j.isLt) z)) = _
  exact (e j).supportedPullbackHomeomorph_lift_of_notMem (q j.val) (q (j.val + 1))
    (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
    (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1))
    (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport
      j.val (Nat.le_of_lt j.isLt) z) hzK

/-- Every lifted prefix fixes the original bottom point, including points in the
closed supports of the weights. -/
@[simp] theorem finiteCylinderPrefixTransport_lift_bottom (k : ℕ) (hk : k ≤ n)
    (x : X) (v : E (x, (0 : I))) :
    Pullback.lift (q k)
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport k hk
          (⟨(x, 0), v⟩ : TotalSpace P
            ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))) =
      (⟨(x, 0), v⟩ : TotalSpace P E) := by
  change Pullback.lift (q k)
    (cylinderStages e U hchart w hw hsum hsupport k hk
      (cylinderZeroComparison (P := P) (E := E) w hw hsum ⟨(x, 0), v⟩)) = _
  rw [cylinderStages_lift_bottom e U hchart w hw hsum hsupport k hk
      (cylinderZeroComparison (P := P) (E := E) w hw hsum ⟨(x, 0), v⟩)
      (by rw [cylinderZeroComparison_proj]), cylinderZeroComparison_lift]
  rfl

/-- Weighted finite cylinder transport, in increasing chart-index order.

The source is the iterated standard pullback of the original zero restriction;
the target is the same given original total space. The dummy `P` needs no
structure, and the chart models `F j` may vary. No normality, nonempty-fiber
premise, or separately assumed continuity of the original projection is used. -/
noncomputable def finiteCylinderTransport (hcover : (⋃ j, U j) = univ) :
    TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
      TotalSpace P E := private_decl% (show
    TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
      TotalSpace P E from
  (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport n le_rfl).trans
    (cylinderLastComparison (P := P) (E := E) w hw hsum
      (continuous_proj_of_cylinder_cover e U hchart hcover)))

variable (hcover : (⋃ j, U j) = univ)

/-- The complete cylinder transport is the canonical lift of its last ordered
prefix into the original total space. -/
theorem finiteCylinderTransport_apply_eq_lift_prefix
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    finiteCylinderTransport e U hchart w hw hsum hsupport hcover z =
      Pullback.lift (q n)
        (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport n le_rfl z) := by
  change cylinderLastComparison (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover)
      (finiteCylinderPrefixTransport e U hchart w hw hsum hsupport n le_rfl z) = _
  exact cylinderLastComparison_lift (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover) _

/-- Finite cylinder transport preserves the entire cylinder base point. -/
@[simp] theorem finiteCylinderTransport_proj
    (z : TotalSpace P ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) :
    (finiteCylinderTransport e U hchart w hw hsum hsupport hcover z).proj = z.proj := by
  change (cylinderLastComparison (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover)
      (cylinderStages e U hchart w hw hsum hsupport n le_rfl
        (cylinderZeroComparison (P := P) (E := E) w hw hsum z))).proj = z.proj
  rw [cylinderLastComparison_proj, cylinderStages_proj, cylinderZeroComparison_proj]

/-- The inverse also preserves the entire cylinder base point. -/
@[simp] theorem finiteCylinderTransport_symm_proj (z : TotalSpace P E) :
    ((finiteCylinderTransport e U hchart w hw hsum hsupport hcover).symm z).proj = z.proj := by
  have h := finiteCylinderTransport_proj e U hchart w hw hsum hsupport hcover
    ((finiteCylinderTransport e U hchart w hw hsum hsupport hcover).symm z)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

/-- Every original bottom point is fixed, not merely points off the supports. -/
@[simp] theorem finiteCylinderTransport_apply_bottom (x : X) (v : E (x, (0 : I))) :
    finiteCylinderTransport e U hchart w hw hsum hsupport hcover
      (⟨(x, 0), v⟩ : TotalSpace P
        ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) =
      (⟨(x, 0), v⟩ : TotalSpace P E) := by
  change cylinderLastComparison (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover)
      (cylinderStages e U hchart w hw hsum hsupport n le_rfl
        (cylinderZeroComparison (P := P) (E := E) w hw hsum ⟨(x, 0), v⟩)) = _
  rw [cylinderLastComparison_lift,
    cylinderStages_lift_bottom e U hchart w hw hsum hsupport n le_rfl
      (cylinderZeroComparison (P := P) (E := E) w hw hsum ⟨(x, 0), v⟩)
      (by rw [cylinderZeroComparison_proj]), cylinderZeroComparison_lift]
  rfl

/-- The inverse fixes the same bottom points. -/
@[simp] theorem finiteCylinderTransport_symm_apply_bottom (x : X) (v : E (x, (0 : I))) :
    (finiteCylinderTransport e U hchart w hw hsum hsupport hcover).symm
      (⟨(x, 0), v⟩ : TotalSpace P E) =
      (⟨(x, 0), v⟩ : TotalSpace P
        ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) := by
  apply (finiteCylinderTransport e U hchart w hw hsum hsupport hcover).injective
  rw [Homeomorph.apply_symm_apply, finiteCylinderTransport_apply_bottom]

section Endpoint

private def cylinderTopMap : C(X, X × I) :=
  ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩

private noncomputable def cylinderEndpointPrefixMap (k : ℕ) : C(X, X × I) :=
  (q k).comp (cylinderTopMap (X := X))

local notation "f" => cylinderEndpointPrefixMap w hw hsum

private theorem cylinderEndpointPrefixMap_eqOn (j : Fin n) :
    EqOn (f j.val : X → X × I) (f (j.val + 1)) (closure {x | w j x ≠ 0})ᶜ := by
  intro x hx
  exact cylinderPrefixMap_eqOn w hw hsum j (x := (x, (1 : I))) (fun h ↦ hx h.1)

include hchart hsupport in
private theorem cylinderEndpointPrefixMap_mapsTo (j : Fin n) (k : ℕ) :
    MapsTo (f k) (closure {x | w j x ≠ 0}) (e j).baseSet := by
  intro x hx
  exact hchart j ⟨hsupport j hx, mem_univ _⟩

private noncomputable def cylinderEndpointStep (j : Fin n) :
    TotalSpace P ((f j.val : X → X × I) *ᵖ E) ≃ₜ
      TotalSpace P ((f (j.val + 1) : X → X × I) *ᵖ E) :=
  (e j).supportedPullbackHomeomorph (f j.val) (f (j.val + 1))
    (closure {x | w j x ≠ 0}) isClosed_closure
    (cylinderEndpointPrefixMap_eqOn w hw hsum j)
    (cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1))

private theorem cylinderEndpointStep_proj (j : Fin n)
    (z : TotalSpace P ((f j.val : X → X × I) *ᵖ E)) :
    (cylinderEndpointStep e U hchart w hw hsum hsupport j z).proj = z.proj := by
  exact (e j).supportedPullbackHomeomorph_proj (f j.val) (f (j.val + 1))
    (closure {x | w j x ≠ 0}) isClosed_closure
    (cylinderEndpointPrefixMap_eqOn w hw hsum j)
    (cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1)) z

private noncomputable def cylinderEndpointStages : (k : ℕ) → (hk : k ≤ n) →
    TotalSpace P ((f 0 : X → X × I) *ᵖ E) ≃ₜ
      TotalSpace P ((f k : X → X × I) *ᵖ E) :=
  orderedHomeomorphChain (fun k ↦ TotalSpace P ((f k : X → X × I) *ᵖ E))
    (cylinderEndpointStep e U hchart w hw hsum hsupport)

private theorem cylinderEndpointStages_proj : ∀ (k : ℕ) (hk : k ≤ n)
    (z : TotalSpace P ((f 0 : X → X × I) *ᵖ E)),
    (cylinderEndpointStages e U hchart w hw hsum hsupport k hk z).proj = z.proj := by
  intro k
  induction k with
  | zero => intro hk z; rfl
  | succ k ih =>
      intro hk z
      change (cylinderEndpointStep e U hchart w hw hsum hsupport ⟨k, hk⟩
        (cylinderEndpointStages e U hchart w hw hsum hsupport k
          (Nat.le_of_succ_le hk) z)).proj = _
      rw [cylinderEndpointStep_proj]
      exact ih (Nat.le_of_succ_le hk) z

private noncomputable def cylinderEndpointZeroComparison :
    TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E) ≃ₜ
      TotalSpace P ((f 0 : X → X × I) *ᵖ E) :=
  pullbackCongr P E (fun x : X ↦ (x, (0 : I))) (f 0)
    (by funext x; exact (cylinderPrefixMap_zero_apply w hw hsum (x, 1)).symm)

private theorem cylinderEndpointZeroComparison_proj
    (z : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) :
    (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z).proj = z.proj := by
  simp only [cylinderEndpointZeroComparison, pullbackCongr_proj]

private theorem cylinderEndpointZeroComparison_lift
    (z : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) :
    Pullback.lift (f 0) (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z) =
      Pullback.lift (fun x : X ↦ (x, (0 : I))) z := by
  simp only [cylinderEndpointZeroComparison, pullbackCongr_lift]

private noncomputable def cylinderEndpointLastComparison :
    TotalSpace P ((f n : X → X × I) *ᵖ E) ≃ₜ
      TotalSpace P ((fun x : X ↦ (x, (1 : I))) *ᵖ E) :=
  pullbackCongr P E (f n) (fun x : X ↦ (x, (1 : I)))
    (by funext x; exact cylinderPrefixMap_last_apply w hw hsum (x, 1))

private theorem cylinderEndpointLastComparison_proj
    (z : TotalSpace P ((f n : X → X × I) *ᵖ E)) :
    (cylinderEndpointLastComparison (P := P) (E := E) w hw hsum z).proj = z.proj := by
  simp only [cylinderEndpointLastComparison, pullbackCongr_proj]

private theorem cylinderEndpointLastComparison_lift
    (z : TotalSpace P ((f n : X → X × I) *ᵖ E)) :
    Pullback.lift (fun x : X ↦ (x, (1 : I)))
        (cylinderEndpointLastComparison (P := P) (E := E) w hw hsum z) =
      Pullback.lift (f n) z := by
  simp only [cylinderEndpointLastComparison, pullbackCongr_lift]

/-- Ordered transport from the zero-time restriction to the one-time restriction.

Each step is the original chart's supported pullback homeomorphism on `X`,
supported in the closed support of its weight. The steps are composed in
increasing index order, independently of cylinder transport, with equality
comparisons at both ends to the standard endpoint pullbacks. The dummy `P`
needs no structure, and the chart models may vary. No cover or separate
continuity assumption on the original projection is needed. -/
noncomputable def finiteCylinderEndpointTransport :
    TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E) ≃ₜ
      TotalSpace P ((fun x : X ↦ (x, (1 : I))) *ᵖ E) := private_decl% (show
    TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E) ≃ₜ
      TotalSpace P ((fun x : X ↦ (x, (1 : I))) *ᵖ E) from
  ((cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum).trans
    (cylinderEndpointStages e U hchart w hw hsum hsupport n le_rfl)).trans
    (cylinderEndpointLastComparison (P := P) (E := E) w hw hsum))

/-- Endpoint transport preserves the spatial base point. -/
@[simp] theorem finiteCylinderEndpointTransport_proj
    (z : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) :
    (finiteCylinderEndpointTransport e U hchart w hw hsum hsupport z).proj = z.proj := by
  change (cylinderEndpointLastComparison (P := P) (E := E) w hw hsum
    (cylinderEndpointStages e U hchart w hw hsum hsupport n le_rfl
      (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z))).proj = z.proj
  rw [cylinderEndpointLastComparison_proj, cylinderEndpointStages_proj,
    cylinderEndpointZeroComparison_proj]

/-- The inverse endpoint transport also preserves the spatial base point. -/
@[simp] theorem finiteCylinderEndpointTransport_symm_proj
    (z : TotalSpace P ((fun x : X ↦ (x, (1 : I))) *ᵖ E)) :
    ((finiteCylinderEndpointTransport e U hchart w hw hsum hsupport).symm z).proj =
      z.proj := by
  have h := finiteCylinderEndpointTransport_proj e U hchart w hw hsum hsupport
    ((finiteCylinderEndpointTransport e U hchart w hw hsum hsupport).symm z)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

private def cylinderEndpointLift (k : ℕ)
    (z : TotalSpace P ((f k : X → X × I) *ᵖ E)) :
    TotalSpace P ((q k : X × I → X × I) *ᵖ E) :=
  ⟨(z.proj, 1), z.snd⟩

omit [TopologicalSpace (TotalSpace P E)] in
private theorem cylinderEndpointLift_proj (k : ℕ)
    (z : TotalSpace P ((f k : X → X × I) *ᵖ E)) :
    (cylinderEndpointLift (P := P) (E := E) w hw hsum k z).proj = (z.proj, 1) := by
  rfl

private theorem cylinderEndpointStep_lift (j : Fin n)
    (z : TotalSpace P ((f j.val : X → X × I) *ᵖ E)) :
    Pullback.lift (f (j.val + 1)) (cylinderEndpointStep e U hchart w hw hsum hsupport j z) =
      Pullback.lift (q (j.val + 1))
        (cylinderStep e U hchart w hw hsum hsupport j
          (cylinderEndpointLift (P := P) (E := E) w hw hsum j.val z)) := by
  let z' := cylinderEndpointLift (P := P) (E := E) w hw hsum j.val z
  have h₀ := cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val
  have h₁ := cylinderEndpointPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1)
  have h₀' := cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val
  have h₁' := cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1)
  -- Compare lifted points, without changing the supports inside the supported maps.
  by_cases hz : z.proj ∈ closure {x | w j x ≠ 0}
  · have hzK : z'.proj ∈ closure {x | w j x ≠ 0} ×ˢ (univ : Set I) := by
      change (z.proj, (1 : I)) ∈ closure {x | w j x ≠ 0} ×ˢ (univ : Set I)
      exact ⟨hz, mem_univ _⟩
    calc
      _ = (e j).lift (Pullback.lift (f j.val) z) (f (j.val + 1) z.proj) :=
        (e j).supportedPullbackHomeomorph_lift_of_mem (f j.val) (f (j.val + 1))
          (closure {x | w j x ≠ 0}) isClosed_closure
          (cylinderEndpointPrefixMap_eqOn w hw hsum j) h₀ h₁ z ⟨h₀ hz, h₁ hz⟩
      _ = (e j).lift (Pullback.lift (q j.val) z') (q (j.val + 1) z'.proj) := by rfl
      _ = _ :=
        ((e j).supportedPullbackHomeomorph_lift_of_mem (q j.val) (q (j.val + 1))
          (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
          (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
          h₀' h₁' z' ⟨h₀' hzK, h₁' hzK⟩).symm
  · have hzK : z'.proj ∉ closure {x | w j x ≠ 0} ×ˢ (univ : Set I) := by
      change (z.proj, (1 : I)) ∉ closure {x | w j x ≠ 0} ×ˢ (univ : Set I)
      exact fun h ↦ hz h.1
    calc
      _ = Pullback.lift (f j.val) z :=
        (e j).supportedPullbackHomeomorph_lift_of_notMem (f j.val) (f (j.val + 1))
          (closure {x | w j x ≠ 0}) isClosed_closure
          (cylinderEndpointPrefixMap_eqOn w hw hsum j) h₀ h₁ z hz
      _ = Pullback.lift (q j.val) z' := by rfl
      _ = _ :=
        ((e j).supportedPullbackHomeomorph_lift_of_notMem (q j.val) (q (j.val + 1))
          (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
          (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
          h₀' h₁' z' hzK).symm

private theorem cylinderEndpointStep_comm (j : Fin n)
    (z : TotalSpace P ((f j.val : X → X × I) *ᵖ E)) :
    cylinderStep e U hchart w hw hsum hsupport j
        (cylinderEndpointLift (P := P) (E := E) w hw hsum j.val z) =
      cylinderEndpointLift (P := P) (E := E) w hw hsum (j.val + 1)
        (cylinderEndpointStep e U hchart w hw hsum hsupport j z) := by
  apply (Pullback.homeomorphProdSubtype P E (q (j.val + 1))).injective
  apply Subtype.ext
  apply Prod.ext
  · change (cylinderStep e U hchart w hw hsum hsupport j
      (cylinderEndpointLift (P := P) (E := E) w hw hsum j.val z)).proj =
        ((cylinderEndpointStep e U hchart w hw hsum hsupport j z).proj, 1)
    rw [cylinderStep_proj, cylinderEndpointLift_proj, cylinderEndpointStep_proj]
  · exact (cylinderEndpointStep_lift e U hchart w hw hsum hsupport j z).symm

private theorem cylinderStages_top : ∀ (k : ℕ) (hk : k ≤ n)
    (z : TotalSpace P ((f 0 : X → X × I) *ᵖ E)),
    cylinderStages e U hchart w hw hsum hsupport k hk
        (cylinderEndpointLift (P := P) (E := E) w hw hsum 0 z) =
      cylinderEndpointLift (P := P) (E := E) w hw hsum k
        (cylinderEndpointStages e U hchart w hw hsum hsupport k hk z) := by
  intro k
  induction k with
  | zero => intro hk z; rfl
  | succ k ih =>
      intro hk z
      change cylinderStep e U hchart w hw hsum hsupport ⟨k, hk⟩
        (cylinderStages e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk)
          (cylinderEndpointLift (P := P) (E := E) w hw hsum 0 z)) =
        cylinderEndpointLift (P := P) (E := E) w hw hsum (k + 1)
          (cylinderEndpointStep e U hchart w hw hsum hsupport ⟨k, hk⟩
            (cylinderEndpointStages e U hchart w hw hsum hsupport k
              (Nat.le_of_succ_le hk) z))
      rw [ih (Nat.le_of_succ_le hk) z, cylinderEndpointStep_comm]

private theorem cylinderZeroComparison_top
    (z : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) :
    cylinderZeroComparison (P := P) (E := E) w hw hsum
        (⟨(z.proj, 1), z.snd⟩ : TotalSpace P
          ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) =
      cylinderEndpointLift (P := P) (E := E) w hw hsum 0
        (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z) := by
  apply (Pullback.homeomorphProdSubtype P E (q 0)).injective
  apply Subtype.ext
  apply Prod.ext
  · change (cylinderZeroComparison (P := P) (E := E) w hw hsum
      (⟨(z.proj, 1), z.snd⟩ : TotalSpace P
        ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))).proj =
      ((cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z).proj, 1)
    rw [cylinderZeroComparison_proj, cylinderEndpointZeroComparison_proj]
  · change Pullback.lift (q 0)
      (cylinderZeroComparison (P := P) (E := E) w hw hsum
        (⟨(z.proj, 1), z.snd⟩ : TotalSpace P
          ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))) =
      Pullback.lift (f 0)
        (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum z)
    rw [cylinderZeroComparison_lift, cylinderEndpointZeroComparison_lift]
    rfl

/-- On the top slice, cylinder transport is the lift of the independently
composed ordered endpoint transport. -/
theorem finiteCylinderTransport_apply_top (x : X) (v : E (x, (0 : I))) :
    finiteCylinderTransport e U hchart w hw hsum hsupport hcover
        (⟨(x, 1), v⟩ : TotalSpace P
          ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) =
      Pullback.lift (fun x : X ↦ (x, (1 : I)))
        (finiteCylinderEndpointTransport e U hchart w hw hsum hsupport
          (⟨x, v⟩ : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) := by
  change cylinderLastComparison (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover)
      (cylinderStages e U hchart w hw hsum hsupport n le_rfl
        (cylinderZeroComparison (P := P) (E := E) w hw hsum ⟨(x, 1), v⟩)) =
      Pullback.lift (fun x : X ↦ (x, (1 : I)))
        (cylinderEndpointLastComparison (P := P) (E := E) w hw hsum
          (cylinderEndpointStages e U hchart w hw hsum hsupport n le_rfl
            (cylinderEndpointZeroComparison (P := P) (E := E) w hw hsum ⟨x, v⟩)))
  rw [cylinderLastComparison_lift,
    cylinderZeroComparison_top (P := P) (E := E) w hw hsum
      (⟨x, v⟩ : TotalSpace P ((fun x : X ↦ (x, (0 : I))) *ᵖ E)),
    cylinderStages_top, cylinderEndpointLastComparison_lift]; rfl

end Endpoint

end Assembly

section Linear

universe uR

/-! Fiber extraction uses the projection equality of the given total-space map.
Composition is proved by comparing the corresponding total-space points. -/

private def transportFiberMap {A : Type*} {G H : A → Type*} (P : Type*)
    (f : TotalSpace P G → TotalSpace P H) (hf : ∀ z, (f z).proj = z.proj)
    (a : A) (v : G a) : H a :=
  cast (congrArg H (hf ⟨a, v⟩)) (f ⟨a, v⟩).2

private theorem transportFiberMap_point {A : Type*} {G H : A → Type*} (P : Type*)
    (f : TotalSpace P G → TotalSpace P H) (hf : ∀ z, (f z).proj = z.proj)
    (a : A) (v : G a) :
    (⟨a, transportFiberMap P f hf a v⟩ : TotalSpace P H) = f ⟨a, v⟩ :=
  TotalSpace.mk_cast (hf ⟨a, v⟩) _

private theorem transportFiberMap_comp_isLinearMap
    {A : Type*} {G H K : A → Type*} {R : Type*} [Semiring R]
    [∀ a, AddCommMonoid (G a)] [∀ a, Module R (G a)]
    [∀ a, AddCommMonoid (H a)] [∀ a, Module R (H a)]
    [∀ a, AddCommMonoid (K a)] [∀ a, Module R (K a)] (P : Type*)
    (f : TotalSpace P G → TotalSpace P H) (g : TotalSpace P H → TotalSpace P K)
    (hf : ∀ z, (f z).proj = z.proj) (hg : ∀ z, (g z).proj = z.proj)
    (hgf : ∀ z, (g (f z)).proj = z.proj) (a : A)
    (hlinf : IsLinearMap R (transportFiberMap P f hf a))
    (hling : IsLinearMap R (transportFiberMap P g hg a)) :
    IsLinearMap R (transportFiberMap P (fun z ↦ g (f z)) hgf a) := by
  let φ : G a →ₗ[R] K a :=
    (IsLinearMap.mk' _ hling).comp (IsLinearMap.mk' _ hlinf)
  have heq : transportFiberMap P (fun z ↦ g (f z)) hgf a = φ := by
    funext v
    apply (TotalSpace.mk_inj (F := P) (E := K) (b := a)).mp
    calc
      (⟨a, transportFiberMap P (fun z ↦ g (f z)) hgf a v⟩ : TotalSpace P K) =
          g (f ⟨a, v⟩) := transportFiberMap_point P _ hgf a v
      _ = g ⟨a, transportFiberMap P f hf a v⟩ :=
        congrArg g (transportFiberMap_point P f hf a v).symm
      _ = ⟨a, φ v⟩ := (transportFiberMap_point P g hg a _).symm
  rw [heq]
  exact φ.isLinear

/-! For the first and last comparisons, equality of lifted original points
identifies the fiber map with Mathlib's linear equality cast. -/

private theorem transportFiberMap_isLinearMap_of_lift
    {A B : Type*} {E : B → Type*} {R : Type*} [Semiring R]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] (P : Type*)
    (f g : A → B) (hfg : f = g)
    (H : TotalSpace P (f *ᵖ E) → TotalSpace P (g *ᵖ E))
    (hH : ∀ z, (H z).proj = z.proj)
    (hlift : ∀ z, Pullback.lift g (H z) = Pullback.lift f z) (a : A) :
    IsLinearMap R (transportFiberMap P H hH a) := by
  let φ : E (f a) →ₗ[R] E (g a) :=
    (LinearEquiv.cast (R := R) (congrFun hfg a)).toLinearMap
  have heq : transportFiberMap P H hH a = φ := by
    funext v
    apply (TotalSpace.mk_inj (F := P) (E := E) (b := g a)).mp
    calc
      (⟨g a, transportFiberMap P H hH a v⟩ : TotalSpace P E) =
          Pullback.lift g (H ⟨a, v⟩) :=
        congrArg (Pullback.lift g) (transportFiberMap_point P H hH a v)
      _ = Pullback.lift f ⟨a, v⟩ := hlift ⟨a, v⟩
      _ = ⟨g a, φ v⟩ := (TotalSpace.mk_cast (congrFun hfg a) v).symm
  rw [heq]
  exact φ.isLinear

variable {X : Type uX} [TopologicalSpace X] {P : Type uP} {n : ℕ}
  {F : Fin n → Type uF} {E : X × I → Type uE}
  [∀ j, TopologicalSpace (F j)] [TopologicalSpace (TotalSpace P E)]
  {R : Type uR} [Semiring R]
  [∀ j, AddCommMonoid (F j)] [∀ j, Module R (F j)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]

variable (e : ∀ j, Trivialization (F j) (π P E)) (U : Fin n → Set X)
  (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
  (w : Fin n → C(X, ℝ)) (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1)
  (hsum : ∀ x, ∑ i, w i x = 1)
  (hsupport : ∀ j, closure {x | w j x ≠ 0} ⊆ U j)
  (L : ∀ j b, b ∈ (e j).baseSet → E b ≃ₗ[R] F j)
  (hL : ∀ j b (hb : b ∈ (e j).baseSet) (v : E b),
    L j b hb v = (e j (⟨b, v⟩ : TotalSpace P E)).2)

local notation "q" => cylinderPrefixMap w hw hsum

include L hL in
private theorem cylinderStep_isLinearMap_of_coordinates (j : Fin n) (b : X × I) :
    IsLinearMap R (transportFiberMap P (cylinderStep e U hchart w hw hsum hsupport j)
      (cylinderStep_proj e U hchart w hw hsum hsupport j) b) := by
  exact (e j).supportedPullbackHomeomorph_isLinearMap_of_coordinates
    (q j.val) (q (j.val + 1)) (closure {x | w j x ≠ 0} ×ˢ (univ : Set I))
    (isClosed_closure.prod isClosed_univ) (cylinderPrefixMap_eqOn w hw hsum j)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j j.val)
    (cylinderPrefixMap_mapsTo e U hchart w hw hsum hsupport j (j.val + 1))
    (L j) (hL j) b

include L hL in
private theorem cylinderStages_isLinearMap_of_coordinates : ∀ (k : ℕ) (hk : k ≤ n)
    (b : X × I), IsLinearMap R (transportFiberMap P
      (cylinderStages e U hchart w hw hsum hsupport k hk)
      (cylinderStages_proj e U hchart w hw hsum hsupport k hk) b) := by
  intro k
  induction k with
  | zero =>
      intro hk b
      change IsLinearMap R (fun v : E (q 0 b) ↦ v)
      exact (LinearMap.id : E (q 0 b) →ₗ[R] E (q 0 b)).isLinear
  | succ k ih =>
      intro hk b
      exact transportFiberMap_comp_isLinearMap P
        (cylinderStages e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk))
        (cylinderStep e U hchart w hw hsum hsupport ⟨k, hk⟩)
        (cylinderStages_proj e U hchart w hw hsum hsupport k (Nat.le_of_succ_le hk))
        (cylinderStep_proj e U hchart w hw hsum hsupport ⟨k, hk⟩)
        (cylinderStages_proj e U hchart w hw hsum hsupport (k + 1) hk) b
        (ih (Nat.le_of_succ_le hk) b)
        (cylinderStep_isLinearMap_of_coordinates e U hchart w hw hsum hsupport L hL ⟨k, hk⟩ b)

private theorem cylinderZeroComparison_isLinearMap (b : X × I) :
    IsLinearMap R (transportFiberMap P
      (cylinderZeroComparison (P := P) (E := E) w hw hsum)
      (cylinderZeroComparison_proj (P := P) (E := E) w hw hsum) b) := by
  exact transportFiberMap_isLinearMap_of_lift P
    ((fun x : X ↦ (x, (0 : I))) ∘ (Prod.fst : X × I → X)) (q 0)
    (by funext a; exact (cylinderPrefixMap_zero_apply w hw hsum a).symm)
    (cylinderZeroComparison (P := P) (E := E) w hw hsum)
    (cylinderZeroComparison_proj (P := P) (E := E) w hw hsum)
    (cylinderZeroComparison_lift (P := P) (E := E) w hw hsum) b

private theorem cylinderLastComparison_isLinearMap (hπ : Continuous (π P E)) (b : X × I) :
    IsLinearMap R (transportFiberMap P
      (cylinderLastComparison (P := P) (E := E) w hw hsum hπ)
      (cylinderLastComparison_proj (P := P) (E := E) w hw hsum hπ) b) := by
  exact transportFiberMap_isLinearMap_of_lift P (q n) id
    (by funext a; exact cylinderPrefixMap_last_apply w hw hsum a)
    (cylinderLastComparison (P := P) (E := E) w hw hsum hπ)
    (cylinderLastComparison_proj (P := P) (E := E) w hw hsum hπ)
    (cylinderLastComparison_lift (P := P) (E := E) w hw hsum hπ) b

include L hL in
/-- Linear coordinates in each chart make finite cylinder transport linear from
`E (x, 0)` to `E (x, t)`. This is the fiber map of the same ordered weighted
transport, extracted using its projection equality. The module structures are
those on the original fibers and the varying chart models; `R` may be any
semiring, without a topology or continuity of module operations. The real
weights affect only time, not scalar multiplication on these fibers.

The finite ordered cylinder-chart cover is given. Hatcher, *Vector Bundles and
K-Theory*, Proposition 1.7, is a motivating bundle comparison, with subordinate
weights motivated by printed p. 20 (PDF p. 24). The arbitrary-semiring and
varying-model formulation here does not assert the full proposition. -/
theorem finiteCylinderTransport_isLinearMap_of_coordinates
    (hcover : (⋃ j, U j) = univ) (x : X) (t : I) :
    IsLinearMap R (fun v : E (x, (0 : I)) ↦
      cast (congrArg E
        (finiteCylinderTransport_proj e U hchart w hw hsum hsupport hcover
          (⟨(x, t), v⟩ : TotalSpace P
            ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))))
        (finiteCylinderTransport e U hchart w hw hsum hsupport hcover ⟨(x, t), v⟩).2) := by
  let H₀ := cylinderZeroComparison (P := P) (E := E) w hw hsum
  let H₁ := cylinderStages e U hchart w hw hsum hsupport n le_rfl
  let H₂ := cylinderLastComparison (P := P) (E := E) w hw hsum
    (continuous_proj_of_cylinder_cover e U hchart hcover)
  have h01 : ∀ z, (H₁ (H₀ z)).proj = z.proj := fun z ↦
    (cylinderStages_proj e U hchart w hw hsum hsupport n le_rfl (H₀ z)).trans
      (cylinderZeroComparison_proj (P := P) (E := E) w hw hsum z)
  have h01lin : IsLinearMap R (transportFiberMap P (fun z ↦ H₁ (H₀ z)) h01 (x, t)) :=
    transportFiberMap_comp_isLinearMap P H₀ H₁
      (cylinderZeroComparison_proj (P := P) (E := E) w hw hsum)
      (cylinderStages_proj e U hchart w hw hsum hsupport n le_rfl) h01 (x, t)
      (cylinderZeroComparison_isLinearMap (R := R) (P := P) (E := E) w hw hsum (x, t))
      (cylinderStages_isLinearMap_of_coordinates e U hchart w hw hsum hsupport L hL
        n le_rfl (x, t))
  change IsLinearMap R (transportFiberMap P (fun z ↦ H₂ (H₁ (H₀ z)))
    (finiteCylinderTransport_proj e U hchart w hw hsum hsupport hcover) (x, t))
  exact transportFiberMap_comp_isLinearMap P (fun z ↦ H₁ (H₀ z)) H₂ h01
    (cylinderLastComparison_proj (P := P) (E := E) w hw hsum
      (continuous_proj_of_cylinder_cover e U hchart hcover))
    (finiteCylinderTransport_proj e U hchart w hw hsum hsupport hcover) (x, t) h01lin
    (cylinderLastComparison_isLinearMap (R := R) (P := P) (E := E) w hw hsum
      (continuous_proj_of_cylinder_cover e U hchart hcover) (x, t))

end Linear

end Bundle.Trivialization
