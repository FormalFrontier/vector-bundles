/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Pullback transport supported in one bundle chart

A closed subset of the domain localizes a change of base map to the base set of
one trivialization. The resulting homeomorphism of pullback total spaces preserves
the domain point, retains the chart coordinate where both base maps lie in the
chart, and leaves the point of the original total space unchanged off the closed
subset.

The construction uses `Bundle.Trivialization.liftCM` on the intersection of the
two inverse images of the chart's base set, and equality of the base maps on the
complement of the closed subset. These are an open cover. Chart cancellation
identifies the formulas on the overlap; open-cover pasting applies in both
directions. The topology on each pullback is Mathlib's topology determined by its
projection and `Pullback.lift`.

## References

The localization idea is the elementary supported change of time used in the
proof of Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7. The chart lift,
its joint continuity, and the pullback topology are provided by Mathlib's
`Topology.FiberBundle.Trivialization` and `Topology.FiberBundle.Constructions`.
-/

@[expose] public section

open Bundle Set

namespace Bundle.Trivialization

universe uA uB uF uE

variable {A : Type uA} {B : Type uB} {F : Type uF} {E : B → Type uE}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F]
variable [TopologicalSpace (TotalSpace F E)]

omit [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] in
private theorem pullback_ext {f : A → B} {z w : TotalSpace F (f *ᵖ E)}
    (hp : z.proj = w.proj) (hl : Pullback.lift f z = Pullback.lift f w) : z = w := by
  cases z with | mk a v =>
    cases w with | mk b w =>
      dsimp at hp
      subst b
      have hv := (TotalSpace.ext_iff.mp hl).2
      cases eq_of_heq hv
      rfl

private noncomputable def supportedLift (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) : TotalSpace F E := by
  classical
  exact if z.proj ∈ K then e.lift (Pullback.lift f₀ z) (f₁ z.proj)
    else Pullback.lift f₀ z

private theorem supportedLift_proj (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    (supportedLift e f₀ f₁ K z).proj = f₁ z.proj := by
  classical
  by_cases hz : z.proj ∈ K
  · simpa [supportedLift, hz] using e.proj_lift (h₁ hz)
  · simpa [supportedLift, hz] using hEq hz

private noncomputable def supportedMap (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    TotalSpace F ((f₁ : A → B) *ᵖ E) :=
  ⟨z.proj, cast (congrArg E (supportedLift_proj e f₀ f₁ K hEq h₁ z))
    (supportedLift e f₀ f₁ K z).2⟩

private theorem supportedMap_proj (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    (supportedMap e f₀ f₁ K hEq h₁ z).proj = z.proj := rfl

private theorem supportedMap_lift (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    Pullback.lift f₁ (supportedMap e f₀ f₁ K hEq h₁ z) = supportedLift e f₀ f₁ K z := by
  exact TotalSpace.mk_cast (supportedLift_proj e f₀ f₁ K hEq h₁ z) _

private theorem supportedMap_lift_chart (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E))
    (hz : z.proj ∈ (f₀ ⁻¹' e.baseSet) ∩ (f₁ ⁻¹' e.baseSet)) :
    Pullback.lift f₁ (supportedMap e f₀ f₁ K hEq h₁ z) =
      e.lift (Pullback.lift f₀ z) (f₁ z.proj) := by
  classical
  rw [supportedMap_lift, supportedLift]
  split_ifs with h
  · rfl
  · rw [← hEq h]
    exact (Trivialization.lift_self (T := e) (z := Pullback.lift f₀ z) hz.1).symm

private theorem supportedMap_lift_off (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) (hz : z.proj ∉ K) :
    Pullback.lift f₁ (supportedMap e f₀ f₁ K hEq h₁ z) = Pullback.lift f₀ z := by
  classical
  simp [supportedMap_lift, supportedLift, hz]

private theorem supportedMap_continuous (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hK : IsClosed K) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ)
    (h₀ : MapsTo f₀ K e.baseSet) (h₁ : MapsTo f₁ K e.baseSet) :
    Continuous (supportedMap e f₀ f₁ K hEq h₁) := by
  apply (inducing_pullbackTotalSpaceEmbedding (F := F) (E := E) f₁).continuous_iff.mpr
  apply (Pullback.continuous_proj F E f₀).prodMk
  let W : Set (TotalSpace F ((f₀ : A → B) *ᵖ E)) :=
    {z | f₀ z.proj ∈ e.baseSet ∧ f₁ z.proj ∈ e.baseSet}
  let V : Set (TotalSpace F ((f₀ : A → B) *ᵖ E)) := {z | z.proj ∉ K}
  have hW : IsOpen W :=
    (e.open_baseSet.preimage (f₀.continuous.comp (Pullback.continuous_proj F E f₀))).inter
      (e.open_baseSet.preimage (f₁.continuous.comp (Pullback.continuous_proj F E f₀)))
  have hV : IsOpen V := hK.isOpen_compl.preimage (Pullback.continuous_proj F E f₀)
  have cover : W ∪ V = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    by_cases hz : z.proj ∈ K
    · exact Or.inl ⟨h₀ hz, h₁ hz⟩
    · exact Or.inr hz
  have chart : ContinuousOn (fun z : TotalSpace F ((f₀ : A → B) *ᵖ E) ↦
      e.lift (Pullback.lift f₀ z) (f₁ z.proj)) W := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp (e.liftCM.continuous.comp
      (((Pullback.continuous_lift F E f₀).comp continuous_subtype_val).subtype_mk
        (fun z ↦ e.mem_source.mpr z.2.1) |>.prodMk
        ((f₁.continuous.comp ((Pullback.continuous_proj F E f₀).comp
          continuous_subtype_val)).subtype_mk (fun z ↦ z.2.2))))
  have onW : ContinuousOn (fun z ↦ Pullback.lift f₁ (supportedMap e f₀ f₁ K hEq h₁ z)) W :=
    chart.congr (fun z hz ↦ supportedMap_lift_chart e f₀ f₁ K hEq h₁ z hz)
  have onV : ContinuousOn (fun z ↦ Pullback.lift f₁ (supportedMap e f₀ f₁ K hEq h₁ z)) V :=
    (Pullback.continuous_lift F E f₀).continuousOn.congr
      (fun z hz ↦ supportedMap_lift_off e f₀ f₁ K hEq h₁ z hz)
  exact continuousOn_univ.mp (cover ▸ onW.union_of_isOpen onV hW hV)

private theorem supportedMap_inverse (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B))
    (K : Set A) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ)
    (h₀ : MapsTo f₀ K e.baseSet) (h₁ : MapsTo f₁ K e.baseSet)
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    supportedMap e f₁ f₀ K hEq.symm h₀ (supportedMap e f₀ f₁ K hEq h₁ z) = z := by
  refine pullback_ext (f := (f₀ : A → B)) (by rfl) ?_
  by_cases hz : z.proj ∈ K
  · rw [supportedMap_lift_chart e f₁ f₀ K hEq.symm h₀ _ ⟨h₁ hz, h₀ hz⟩,
      supportedMap_proj, supportedMap_lift_chart e f₀ f₁ K hEq h₁ z ⟨h₀ hz, h₁ hz⟩]
    change e.toOpenPartialHomeomorph.symm (f₀ z.proj,
      (e (e.toOpenPartialHomeomorph.symm (f₁ z.proj, (e (Pullback.lift f₀ z)).2))).2) = _
    rw [e.apply_symm_apply' (h₁ hz)]
    exact Trivialization.lift_self (T := e) (z := Pullback.lift f₀ z) (h₀ hz)
  · rw [supportedMap_lift_off e f₁ f₀ K hEq.symm h₀ _ hz,
      supportedMap_lift_off e f₀ f₁ K hEq h₁ z hz]

/-- Change a pullback base map within one chart over a closed subset, fixing the
point of the original total space elsewhere. On the open set
`f₀ ⁻¹' e.baseSet ∩ f₁ ⁻¹' e.baseSet`, retain the chart's fiber coordinate and
replace `f₀ a` by `f₁ a`.

The chart need not be global, and no local compactness or nonemptiness assumption
on the spaces or fibers is required. This is the one-chart localization step in
Hatcher's Proposition 1.7, not a homotopy-invariance theorem. -/
noncomputable def supportedPullbackHomeomorph
    (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B)) (K : Set A)
    (hK : IsClosed K) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ)
    (h₀ : MapsTo f₀ K e.baseSet) (h₁ : MapsTo f₁ K e.baseSet) :
    TotalSpace F ((f₀ : A → B) *ᵖ E) ≃ₜ TotalSpace F ((f₁ : A → B) *ᵖ E) := {
  toFun := private_decl% (show TotalSpace F ((f₀ : A → B) *ᵖ E) →
    TotalSpace F ((f₁ : A → B) *ᵖ E) from supportedMap e f₀ f₁ K hEq h₁)
  invFun := private_decl% (show TotalSpace F ((f₁ : A → B) *ᵖ E) →
    TotalSpace F ((f₀ : A → B) *ᵖ E) from supportedMap e f₁ f₀ K hEq.symm h₀)
  left_inv := by exact supportedMap_inverse e f₀ f₁ K hEq h₀ h₁
  right_inv := by exact supportedMap_inverse e f₁ f₀ K hEq.symm h₁ h₀
  continuous_toFun := by exact supportedMap_continuous e f₀ f₁ K hK hEq h₀ h₁
  continuous_invFun := by exact supportedMap_continuous e f₁ f₀ K hK hEq.symm h₁ h₀ }

variable (e : Trivialization F (π F E)) (f₀ f₁ : C(A, B)) (K : Set A)
variable (hK : IsClosed K) (hEq : EqOn (f₀ : A → B) f₁ Kᶜ)
variable (h₀ : MapsTo f₀ K e.baseSet) (h₁ : MapsTo f₁ K e.baseSet)

/-- Supported transport preserves the point of the domain. -/
@[simp] theorem supportedPullbackHomeomorph_proj
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) :
    (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z).proj = z.proj := by
  rfl

/-- On the common chart domain, the lifted point is the existing chart lift. -/
theorem supportedPullbackHomeomorph_lift_of_mem
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E))
    (hz : z.proj ∈ (f₀ ⁻¹' e.baseSet) ∩ (f₁ ⁻¹' e.baseSet)) :
    Pullback.lift f₁ (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z) =
      e.lift (Pullback.lift f₀ z) (f₁ z.proj) := by
  exact supportedMap_lift_chart e f₀ f₁ K hEq h₁ z hz

/-- The chart-domain formula agrees with Mathlib's jointly continuous chart lift. -/
theorem supportedPullbackHomeomorph_lift_eq_liftCM
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E))
    (hz₀ : f₀ z.proj ∈ e.baseSet) (hz₁ : f₁ z.proj ∈ e.baseSet) :
    Pullback.lift f₁ (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z) =
      (e.liftCM (⟨Pullback.lift f₀ z, e.mem_source.mpr hz₀⟩,
        ⟨f₁ z.proj, hz₁⟩)).val := by
  exact e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z ⟨hz₀, hz₁⟩

/-- The chart fiber coordinate is unchanged on the common chart domain. -/
theorem supportedPullbackHomeomorph_chart
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E))
    (hz : z.proj ∈ (f₀ ⁻¹' e.baseSet) ∩ (f₁ ⁻¹' e.baseSet)) :
    e (Pullback.lift f₁ (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z)) =
      (f₁ z.proj, (e (Pullback.lift f₀ z)).2) := by
  rw [e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z hz]
  exact e.apply_symm_apply' hz.2

/-- Off the closed subset, the original total-space point is unchanged. -/
theorem supportedPullbackHomeomorph_lift_of_notMem
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) (hz : z.proj ∉ K) :
    Pullback.lift f₁ (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z) =
      Pullback.lift f₀ z := by
  exact supportedMap_lift_off e f₀ f₁ K hEq h₁ z hz

/-- Off the closed subset, supported transport is the canonical equality cast
between the two fibers. -/
theorem supportedPullbackHomeomorph_apply_of_notMem
    (z : TotalSpace F ((f₀ : A → B) *ᵖ E)) (hz : z.proj ∉ K) :
    e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ z =
      ⟨z.proj, cast (congrArg E (hEq hz)) z.2⟩ := by
  refine pullback_ext (f := (f₁ : A → B))
    (e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁ z) ?_
  rw [e.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K hK hEq h₀ h₁ z hz]
  exact (TotalSpace.mk_cast (hEq hz) z.2).symm

/-- The inverse is the same supported construction with the base maps exchanged. -/
theorem supportedPullbackHomeomorph_symm :
    (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁).symm =
      e.supportedPullbackHomeomorph f₁ f₀ K hK hEq.symm h₁ h₀ := by
  rfl

/-- Projection and the lifted-point formulas on and off the closed subset
characterize supported transport. This also permits local comparisons without
choosing a distinguished supporting subset. -/
theorem supportedPullbackHomeomorph_unique
    (H : TotalSpace F ((f₀ : A → B) *ᵖ E) ≃ₜ TotalSpace F ((f₁ : A → B) *ᵖ E))
    (hproj : ∀ z, (H z).proj = z.proj)
    (hin : ∀ z, z.proj ∈ K →
      Pullback.lift f₁ (H z) = e.lift (Pullback.lift f₀ z) (f₁ z.proj))
    (hout : ∀ z, z.proj ∉ K → Pullback.lift f₁ (H z) = Pullback.lift f₀ z) :
    H = e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ := by
  ext z : 1
  refine pullback_ext (f := (f₁ : A → B))
    ((hproj z).trans (e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁ z).symm) ?_
  by_cases hz : z.proj ∈ K
  · rw [hin z hz,
      e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z ⟨h₀ hz, h₁ hz⟩]
  · rw [hout z hz,
      e.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K hK hEq h₀ h₁ z hz]

/-- Supported transport in a fixed chart is independent of the admissible closed
support. The supports need not be nested. -/
theorem supportedPullbackHomeomorph_congr_support
    (L : Set A) (hL : IsClosed L) (hEqL : EqOn (f₀ : A → B) f₁ Lᶜ)
    (hL₀ : MapsTo f₀ L e.baseSet) (hL₁ : MapsTo f₁ L e.baseSet) :
    e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ =
      e.supportedPullbackHomeomorph f₀ f₁ L hL hEqL hL₀ hL₁ := by
  apply e.supportedPullbackHomeomorph_unique f₀ f₁ L hL hEqL hL₀ hL₁
  · exact e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁
  · intro z hz
    exact e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z
      ⟨hL₀ hz, hL₁ hz⟩
  · intro z hzL
    by_cases hzK : z.proj ∈ K
    · rw [e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z
        ⟨h₀ hzK, h₁ hzK⟩, ← hEqL hzL]
      exact Trivialization.lift_self (T := e) (z := Pullback.lift f₀ z) (h₀ hzK)
    · exact e.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K hK hEq h₀ h₁ z hzK

/-- A zero change of base map gives the identity, even with nonempty support. -/
@[simp] theorem supportedPullbackHomeomorph_refl
    (f : C(A, B)) (h : MapsTo f K e.baseSet) :
    e.supportedPullbackHomeomorph f f K hK (fun _ _ ↦ rfl) h h =
      Homeomorph.refl (TotalSpace F ((f : A → B) *ᵖ E)) := by
  symm
  apply e.supportedPullbackHomeomorph_unique f f K hK (fun _ _ ↦ rfl) h h
  · exact fun _ ↦ rfl
  · intro z hz
    exact (Trivialization.lift_self (T := e) (z := Pullback.lift f z) (h hz)).symm
  · exact fun _ _ ↦ rfl

/-- Consecutive supported steps in the same chart compose to the direct step.
This law does not compare different charts or reorder steps. -/
theorem supportedPullbackHomeomorph_trans
    (f₂ : C(A, B)) (hEq₁₂ : EqOn (f₁ : A → B) f₂ Kᶜ)
    (h₂ : MapsTo f₂ K e.baseSet) :
    (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁).trans
        (e.supportedPullbackHomeomorph f₁ f₂ K hK hEq₁₂ h₁ h₂) =
      e.supportedPullbackHomeomorph f₀ f₂ K hK (hEq.trans hEq₁₂) h₀ h₂ := by
  apply e.supportedPullbackHomeomorph_unique f₀ f₂ K hK (hEq.trans hEq₁₂) h₀ h₂
  · intro z
    simp only [Homeomorph.trans_apply, supportedPullbackHomeomorph_proj]
  · intro z hz
    simp only [Homeomorph.trans_apply]
    rw [e.supportedPullbackHomeomorph_lift_of_mem f₁ f₂ K hK hEq₁₂ h₁ h₂ _
        ⟨h₁ hz, h₂ hz⟩,
      supportedPullbackHomeomorph_proj,
      e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁ z ⟨h₀ hz, h₁ hz⟩]
    change e.toOpenPartialHomeomorph.symm (f₂ z.proj,
      (e (e.toOpenPartialHomeomorph.symm (f₁ z.proj, (e (Pullback.lift f₀ z)).2))).2) = _
    rw [e.apply_symm_apply' (h₁ hz)]
    rfl
  · intro z hz
    simp only [Homeomorph.trans_apply]
    rw [e.supportedPullbackHomeomorph_lift_of_notMem f₁ f₂ K hK hEq₁₂ h₁ h₂ _
        (by simpa only [supportedPullbackHomeomorph_proj] using hz),
      e.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K hK hEq h₀ h₁ z hz]

universe uA'

/-- Supported transport commutes with continuous precomposition of the base maps
after lifting both results to the original total space. The support on the new
domain is the inverse image of the original support. -/
theorem supportedPullbackHomeomorph_lift_comp
    {A' : Type uA'} [TopologicalSpace A'] (r : C(A', A))
    (z : TotalSpace F (((f₀.comp r) : A' → B) *ᵖ E)) :
    Pullback.lift (f₁.comp r)
        (e.supportedPullbackHomeomorph (f₀.comp r) (f₁.comp r) (r ⁻¹' K)
          (hK.preimage r.continuous) (fun _ hz ↦ hEq hz)
          (fun _ hz ↦ h₀ hz) (fun _ hz ↦ h₁ hz) z) =
      Pullback.lift f₁
        (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁
          (TotalSpace.mk' F (r z.proj) z.snd)) := by
  by_cases hz : r z.proj ∈ K
  · rw [e.supportedPullbackHomeomorph_lift_of_mem
        (f₀.comp r) (f₁.comp r) (r ⁻¹' K) (hK.preimage r.continuous)
        (fun _ hx ↦ hEq hx) (fun _ hx ↦ h₀ hx) (fun _ hx ↦ h₁ hx) z
        ⟨h₀ hz, h₁ hz⟩,
      e.supportedPullbackHomeomorph_lift_of_mem f₀ f₁ K hK hEq h₀ h₁
        (TotalSpace.mk' F (r z.proj) z.snd) ⟨h₀ hz, h₁ hz⟩]
    rfl
  · rw [e.supportedPullbackHomeomorph_lift_of_notMem
        (f₀.comp r) (f₁.comp r) (r ⁻¹' K) (hK.preimage r.continuous)
        (fun _ hx ↦ hEq hx) (fun _ hx ↦ h₀ hx) (fun _ hx ↦ h₁ hx) z hz,
      e.supportedPullbackHomeomorph_lift_of_notMem f₀ f₁ K hK hEq h₀ h₁
        (TotalSpace.mk' F (r z.proj) z.snd) hz]
    rfl

section Linear

variable {R : Type*} [Semiring R] [AddCommMonoid F] [Module R F]
variable [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]

/-- A linear chart makes supported transport linear on each fiber. The cast only
uses the projection equation to view the output in the fiber over the same domain
point. No bundled notion of bundle isomorphism is needed for this conclusion. -/
theorem supportedPullbackHomeomorph_isLinearMap [e.IsLinear R] (a : A) :
    IsLinearMap R (fun v : E (f₀ a) ↦
      cast (congrArg (fun x : A ↦ E (f₁ x))
        (e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁
          (⟨a, v⟩ : TotalSpace F ((f₀ : A → B) *ᵖ E))))
        (e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁ ⟨a, v⟩).2) := by
  let H := e.supportedPullbackHomeomorph f₀ f₁ K hK hEq h₀ h₁
  let out : E (f₀ a) → E (f₁ a) := fun v ↦
    cast (congrArg (fun x : A ↦ E (f₁ x))
      (e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁ ⟨a, v⟩))
      (H ⟨a, v⟩).2
  change IsLinearMap R out
  have point (v : E (f₀ a)) :
      (⟨a, out v⟩ : TotalSpace F ((f₁ : A → B) *ᵖ E)) = H ⟨a, v⟩ :=
    TotalSpace.mk_cast (e.supportedPullbackHomeomorph_proj f₀ f₁ K hK hEq h₀ h₁ ⟨a, v⟩) _
  by_cases ha : a ∈ K
  · let L : E (f₀ a) →ₗ[R] E (f₁ a) :=
      (e.linearEquivAt R (f₁ a) (h₁ ha)).symm.toLinearMap.comp
        (e.linearEquivAt R (f₀ a) (h₀ ha)).toLinearMap
    have eq : out = L := by
      funext v
      apply (e.linearEquivAt R (f₁ a) (h₁ ha)).injective
      change (e ⟨f₁ a, out v⟩).2 =
        e.linearEquivAt R (f₁ a) (h₁ ha)
          ((e.linearEquivAt R (f₁ a) (h₁ ha)).symm
            (e.linearEquivAt R (f₀ a) (h₀ ha) v))
      rw [LinearEquiv.apply_symm_apply]
      have hc := congrArg Prod.snd
        (e.supportedPullbackHomeomorph_chart f₀ f₁ K hK hEq h₀ h₁ ⟨a, v⟩ ⟨h₀ ha, h₁ ha⟩)
      exact (congrArg (fun z ↦ (e (Pullback.lift f₁ z)).2) (point v)).trans hc
    rw [eq]
    exact L.isLinear
  · have eq : out = fun v ↦ cast (congrArg E (hEq ha)) v := by
      funext v
      exact (TotalSpace.mk_inj (F := F) (E := (f₁ : A → B) *ᵖ E) (b := a)).mp ((point v).trans
        (e.supportedPullbackHomeomorph_apply_of_notMem f₀ f₁ K hK hEq h₀ h₁ ⟨a, v⟩ ha))
    rw [eq]
    have cast_linear {b c : B} (hb : b = c) :
        IsLinearMap R (fun v : E b ↦ cast (congrArg E hb) v) := by
      cases hb
      exact (LinearMap.id : E b →ₗ[R] E b).isLinear
    exact cast_linear (hEq ha)

end Linear

end Bundle.Trivialization
