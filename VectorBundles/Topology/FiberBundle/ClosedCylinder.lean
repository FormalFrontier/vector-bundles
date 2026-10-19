/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Gluing trivializations across a closed cylinder cut

Let `p : Z → X × T`, where `T` is linearly ordered. Global charts on the two
closed restrictions at a cut `c` need not agree on the common slice. The right
chart is normalized by the coordinate change from its seam chart to the left
seam chart, applied at every time on the right. The normalized charts determine
a global trivialization.

`T` may itself be a closed interval: taking `T = Set.Icc a b` and
`c = ⟨c₀, hac, hcb⟩` gives the pieces `X × [a,c₀]` and `X × [c₀,b]`, up to their
canonical subspace identifications. Both endpoint cuts are allowed. No
nonemptiness or local triviality assumption is needed in addition to the two
supplied charts and continuity of `p`.

The construction uses Mathlib's `Homeomorph` and `Bundle.Trivialization` objects.
`glueClosedCylinder_isLinear` gives its fiberwise-linear specialization on a
dependent total space. This is the two-piece triviality fact, not the
paracompact homotopy theorem.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
* Mathlib's `Bundle.Trivialization.piecewiseLe` supplies the corresponding
  normalization for charts on a common ambient space over a linearly ordered base.
  `glueClosedCylinder_eq_piecewiseLe` compares the constructions after restricting
  the ambient charts and transporting the base by `Homeomorph.punitProd`.
-/

@[expose] public section

open Bundle Set

universe uX uT uZ uF uE uK

namespace Bundle.Trivialization

section Cylinder

variable {X : Type uX} {T : Type uT} {Z : Type uZ} {F : Type uF}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace Z] [TopologicalSpace F]
  (c : T) (p : Z → X × T)

private theorem chart_symm_base {B : Type*} [TopologicalSpace B] {q : Z → B}
    {s : Set B} (h : (q ⁻¹' s) ≃ₜ s × F)
    (hp : ∀ z, (h z).1.val = q z.val) (w : s × F) :
    q (h.symm w).val = w.1.val := by
  rw [← hp, h.apply_symm_apply]

/-- Restrict a base-preserving global chart to a fiber on the cut slice. -/
private noncomputable def seamHomeomorph (s : Set (X × T))
    (hs : ∀ x, (x, c) ∈ s) (h : (p ⁻¹' s) ≃ₜ s × F)
    (hp : ∀ z : p ⁻¹' s, (h z).1.val = p z.val) (x : X) :
    {z : Z // p z = (x, c)} ≃ₜ F := by
  refine
    { toFun := fun z ↦ (h ⟨z.val, by rw [mem_preimage, z.property]; exact hs x⟩).2
      invFun := fun v ↦ ⟨(h.symm (⟨(x, c), hs x⟩, v)).val,
        chart_symm_base h hp _⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    have hb : (h ⟨z.val, by rw [mem_preimage, z.property]; exact hs x⟩).1 =
        ⟨(x, c), hs x⟩ := Subtype.ext ((hp _).trans z.property)
    simp only [← hb, h.symm_apply_apply]
  · intro v
    exact congrArg Prod.snd (h.apply_symm_apply (⟨(x, c), hs x⟩, v))
  · exact continuous_snd.comp (h.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  · exact (continuous_subtype_val.comp (h.symm.continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

omit [LinearOrder T] in
private theorem seamHomeomorph_apply (s : Set (X × T))
    (hs : ∀ x, (x, c) ∈ s) (h : (p ⁻¹' s) ≃ₜ s × F)
    (hp : ∀ z : p ⁻¹' s, (h z).1.val = p z.val) (x : X)
    (z : {z : Z // p z = (x, c)}) :
    seamHomeomorph c p s hs h hp x z =
      (h ⟨z.val, by change p z.val ∈ s; rw [z.property]; exact hs x⟩).2 := by
  rfl


variable (h₁ : (p ⁻¹' {b : X × T | b.2 ≤ c}) ≃ₜ {b : X × T | b.2 ≤ c} × F)
  (h₂ : (p ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × F)
  (hp₁ : ∀ z : p ⁻¹' {b : X × T | b.2 ≤ c}, (h₁ z).1.val = p z.val)
  (hp₂ : ∀ z : p ⁻¹' {b : X × T | c ≤ b.2}, (h₂ z).1.val = p z.val)

/-- The seam change `h₁,c ∘ h₂,c⁻¹`, from right coordinates to left coordinates. -/
noncomputable def closedCylinderCoordChange
    (h₁ : (p ⁻¹' {b : X × T | b.2 ≤ c}) ≃ₜ {b : X × T | b.2 ≤ c} × F)
    (h₂ : (p ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × F)
    (hp₁ : ∀ z, (h₁ z).1.val = p z.val)
    (hp₂ : ∀ z, (h₂ z).1.val = p z.val) (x : X) : F ≃ₜ F := private_decl% (show F ≃ₜ F from
  (seamHomeomorph (F := F) c p {b : X × T | c ≤ b.2} (fun _ ↦ le_rfl) h₂ hp₂ x).symm.trans
    (seamHomeomorph (F := F) c p {b : X × T | b.2 ≤ c} (fun _ ↦ le_rfl) h₁ hp₁ x))

/-- At the seam the coordinate change takes right coordinates to left coordinates. -/
theorem closedCylinderCoordChange_apply (x : X) (z : Z) (hz : p z = (x, c)) :
    closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ x
        (h₂ ⟨z, by change c ≤ (p z).2; simp [hz]⟩).2 =
      (h₁ ⟨z, by change (p z).2 ≤ c; simp [hz]⟩).2 := by
  let w : {z : Z // p z = (x, c)} := ⟨z, hz⟩
  change seamHomeomorph c p {b : X × T | b.2 ≤ c} (fun _ ↦ le_rfl) h₁ hp₁ x
    ((seamHomeomorph c p {b : X × T | c ≤ b.2} (fun _ ↦ le_rfl) h₂ hp₂ x).symm
      (seamHomeomorph c p {b : X × T | c ≤ b.2} (fun _ ↦ le_rfl) h₂ hp₂ x w)) = _
  rw [Homeomorph.symm_apply_apply, seamHomeomorph_apply]

omit [LinearOrder T] in
private theorem continuous_seam_transition (s t : Set (X × T))
    (hs : ∀ x, (x, c) ∈ s) (ht : ∀ x, (x, c) ∈ t)
    (h : (p ⁻¹' s) ≃ₜ s × F) (k : (p ⁻¹' t) ≃ₜ t × F)
    (hk : ∀ z, (k z).1.val = p z.val) :
    Continuous (fun xv : X × F ↦
      (h ⟨(k.symm (⟨(xv.1, c), ht xv.1⟩, xv.2)).val, by
        rw [mem_preimage, chart_symm_base k hk]; exact hs xv.1⟩).2) := by
  have hi : Continuous (fun xv : X × F ↦
      (k.symm (⟨(xv.1, c), ht xv.1⟩, xv.2)).val) :=
    continuous_subtype_val.comp (k.symm.continuous.comp
      (((continuous_fst.prodMk continuous_const).subtype_mk _).prodMk continuous_snd))
  exact continuous_snd.comp (h.continuous.comp (hi.subtype_mk _))

/-- Evaluation of the seam coordinate change is jointly continuous in base and fiber. -/
theorem continuous_closedCylinderCoordChange :
    Continuous (fun xv : X × F ↦
      closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ xv.1 xv.2) := by
  exact continuous_seam_transition c p {b : X × T | b.2 ≤ c} {b : X × T | c ≤ b.2}
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) h₁ h₂ hp₂

/-- Inverse evaluation of the seam coordinate change is jointly continuous. -/
theorem continuous_closedCylinderCoordChange_symm :
    Continuous (fun xv : X × F ↦
      (closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ xv.1).symm xv.2) := by
  exact continuous_seam_transition c p {b : X × T | c ≤ b.2} {b : X × T | b.2 ≤ c}
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) h₂ h₁ hp₁

/-- Normalize the right chart by `h₁,c ∘ h₂,c⁻¹` at every right-hand time. -/
noncomputable def normalizeClosedCylinderRight :
    (p ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × F where
  toFun z := ((h₂ z).1,
    closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (h₂ z).1.val.1 (h₂ z).2)
  invFun q := h₂.symm (q.1,
    (closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ q.1.val.1).symm q.2)
  left_inv := by
    intro z
    simp
  right_inv := by
    intro q
    simp
  continuous_toFun := by
    have hc : Continuous (fun z : p ⁻¹' {b : X × T | c ≤ b.2} ↦
        ((h₂ z).1.val.1, (h₂ z).2)) :=
      h₂.continuous.fst.subtype_val.fst.prodMk h₂.continuous.snd
    have hd := (continuous_closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂).comp hc
    change Continuous (fun z ↦ ((h₂ z).1,
      (fun xv : X × F ↦ closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ xv.1 xv.2)
        ((h₂ z).1.val.1, (h₂ z).2)))
    exact h₂.continuous.fst.prodMk hd
  continuous_invFun := by
    have hc : Continuous (fun q : {b : X × T | c ≤ b.2} × F ↦ (q.1.val.1, q.2)) :=
      continuous_fst.subtype_val.fst.prodMk continuous_snd
    have hd := (continuous_closedCylinderCoordChange_symm c p h₁ h₂ hp₁ hp₂).comp hc
    exact h₂.symm.continuous.comp (continuous_fst.prodMk hd)

/-- Forward formula for the normalized right chart. -/
@[simp] theorem normalizeClosedCylinderRight_apply (z : p ⁻¹' {b : X × T | c ≤ b.2}) :
    normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ z =
      ((h₂ z).1,
        closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (h₂ z).1.val.1 (h₂ z).2) :=
  rfl

/-- Inverse formula for the normalized right chart. -/
@[simp] theorem normalizeClosedCylinderRight_symm_apply (q : {b : X × T | c ≤ b.2} × F) :
    (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂).symm q =
      h₂.symm (q.1,
        (closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ q.1.val.1).symm q.2) :=
  rfl

/-- Normalization changes no base coordinate. -/
@[simp] theorem normalizeClosedCylinderRight_fst (z : p ⁻¹' {b : X × T | c ≤ b.2}) :
    (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ z).1.val = p z.val := by
  exact hp₂ z

/-- The normalized right and left fiber coordinates agree on the common slice. -/
theorem normalizeClosedCylinderRight_seam (x : X) (z : Z) (hz : p z = (x, c)) :
    (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂
        ⟨z, by change c ≤ (p z).2; simp [hz]⟩).2 =
      (h₁ ⟨z, by change (p z).2 ≤ c; simp [hz]⟩).2 := by
  change closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (h₂ _).1.val.1 _ = _
  rw [hp₂, hz]
  exact closedCylinderCoordChange_apply c p h₁ h₂ hp₁ hp₂ x z hz

private noncomputable def closedCoverMap {A B : Type*} (s t : Set A)
    (cover : ∀ a, a ∈ s ∨ a ∈ t) (f : s → B) (g : t → B) (a : A) : B := by
  classical
  exact if hs : a ∈ s then f ⟨a, hs⟩ else g ⟨a, (cover a).resolve_left hs⟩

private theorem closedCoverMap_left {A B : Type*} (s t : Set A)
    (cover : ∀ a, a ∈ s ∨ a ∈ t) (f : s → B) (g : t → B) (a : A) (ha : a ∈ s) :
    closedCoverMap s t cover f g a = f ⟨a, ha⟩ := by
  classical
  simp [closedCoverMap, ha]

private theorem closedCoverMap_right {A B : Type*} (s t : Set A)
    (cover : ∀ a, a ∈ s ∨ a ∈ t) (f : s → B) (g : t → B)
    (agree : ∀ a hs ht, f ⟨a, hs⟩ = g ⟨a, ht⟩) (a : A) (ha : a ∈ t) :
    closedCoverMap s t cover f g a = g ⟨a, ha⟩ := by
  classical
  by_cases hs : a ∈ s
  · rw [closedCoverMap_left s t cover f g a hs, agree a hs ha]
  · simp [closedCoverMap, hs]

-- Continuity is checked on each closed member, then pasted with Mathlib's closed-union lemma.
private theorem continuous_closedCoverMap {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (s t : Set A) (hs : IsClosed s) (ht : IsClosed t)
    (cover : ∀ a, a ∈ s ∨ a ∈ t) (f : s → B) (g : t → B)
    (agree : ∀ a hs ht, f ⟨a, hs⟩ = g ⟨a, ht⟩) (hf : Continuous f) (hg : Continuous g) :
    Continuous (closedCoverMap s t cover f g) := by
  have hfs : ContinuousOn (closedCoverMap s t cover f g) s :=
    continuousOn_iff_continuous_domRestrict.mpr (by
      convert hf using 1
      ext a
      exact closedCoverMap_left s t cover f g a.val a.property)
  have hgt : ContinuousOn (closedCoverMap s t cover f g) t :=
    continuousOn_iff_continuous_domRestrict.mpr (by
      convert hg using 1
      ext a
      exact closedCoverMap_right s t cover f g agree a.val a.property)
  have hu : s ∪ t = univ := eq_univ_iff_forall.mpr cover
  rw [← continuousOn_univ, ← hu]
  exact hfs.union_of_isClosed hgt hs ht

private theorem normalized_chart_agree (z : Z) (hl : (p z).2 ≤ c) (hr : c ≤ (p z).2) :
    (p z, (h₁ ⟨z, hl⟩).2) =
      (p z, (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ ⟨z, hr⟩).2) := by
  have hz : p z = ((p z).1, c) := Prod.ext rfl (le_antisymm hl hr)
  exact Prod.ext rfl (normalizeClosedCylinderRight_seam c p h₁ h₂ hp₁ hp₂ _ z hz).symm

private theorem normalized_inverse_agree (b : X × T) (hl : b.2 ≤ c) (hr : c ≤ b.2)
    (v : F) : (h₁.symm (⟨b, hl⟩, v)).val =
      ((normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂).symm (⟨b, hr⟩, v)).val := by
  let k := normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂
  let z := h₁.symm (⟨b, hl⟩, v)
  have hz : p z.val = b := chart_symm_base h₁ hp₁ _
  have hzr : c ≤ (p z.val).2 := hz ▸ hr
  have hzl : (p z.val).2 ≤ c := hz ▸ hl
  have he : k ⟨z.val, hzr⟩ = (⟨b, hr⟩, v) := by
    apply Prod.ext
    · apply Subtype.ext
      exact (normalizeClosedCylinderRight_fst c p h₁ h₂ hp₁ hp₂ _).trans hz
    · have ha := congrArg Prod.snd
        (normalized_chart_agree c p h₁ h₂ hp₁ hp₂ z.val hzl hzr)
      have hi : (h₁ ⟨z.val, hzl⟩).2 = v := congrArg Prod.snd (h₁.apply_symm_apply _)
      exact ha.symm.trans hi
  have hi := congrArg (fun w ↦ (k.symm w).val) he
  simpa only [k.symm_apply_apply] using hi

private noncomputable def cylinderHomeomorph [ClosedIicTopology T] [ClosedIciTopology T]
    (hπ : Continuous p) : Z ≃ₜ (X × T) × F := by
  let k := normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂
  let s : Set Z := {z | (p z).2 ≤ c}
  let t : Set Z := {z | c ≤ (p z).2}
  let S : Set ((X × T) × F) := {q | q.1.2 ≤ c}
  let U : Set ((X × T) × F) := {q | c ≤ q.1.2}
  have cover : ∀ z, z ∈ s ∨ z ∈ t := fun z ↦ le_total _ _
  have Cover : ∀ q, q ∈ S ∨ q ∈ U := fun q ↦ le_total _ _
  let f : s → (X × T) × F := fun z ↦ (p z.val, (h₁ z).2)
  let g : t → (X × T) × F := fun z ↦ (p z.val, (k z).2)
  let i : S → Z := fun q ↦ (h₁.symm (⟨q.val.1, q.property⟩, q.val.2)).val
  let j : U → Z := fun q ↦ (k.symm (⟨q.val.1, q.property⟩, q.val.2)).val
  have agree : ∀ z hs ht, f ⟨z, hs⟩ = g ⟨z, ht⟩ :=
    normalized_chart_agree c p h₁ h₂ hp₁ hp₂
  have Agree : ∀ q hs ht, i ⟨q, hs⟩ = j ⟨q, ht⟩ := fun q ↦
    normalized_inverse_agree c p h₁ h₂ hp₁ hp₂ q.1 (v := q.2)
  let forward := closedCoverMap s t cover f g
  -- Paste the inverse on the target's closed ray-products independently of the forward map.
  let inverse := closedCoverMap S U Cover i j
  have fl (z) (hz : z ∈ s) : forward z = f ⟨z, hz⟩ :=
    closedCoverMap_left s t cover f g z hz
  have fr (z) (hz : z ∈ t) : forward z = g ⟨z, hz⟩ :=
    closedCoverMap_right s t cover f g agree z hz
  have il (q) (hq : q ∈ S) : inverse q = i ⟨q, hq⟩ :=
    closedCoverMap_left S U Cover i j q hq
  have ir (q) (hq : q ∈ U) : inverse q = j ⟨q, hq⟩ :=
    closedCoverMap_right S U Cover i j Agree q hq
  refine
    { toFun := forward
      invFun := inverse
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    rcases cover z with hz | hz
    · rw [fl z hz, il _ hz]
      change (h₁.symm (⟨p z, hz⟩, (h₁ ⟨z, hz⟩).2)).val = z
      have hb : (h₁ ⟨z, hz⟩).1 = ⟨p z, hz⟩ := Subtype.ext (hp₁ _)
      simp only [← hb, h₁.symm_apply_apply]
    · rw [fr z hz, ir _ hz]
      change (k.symm (⟨p z, hz⟩, (k ⟨z, hz⟩).2)).val = z
      have hb : (k ⟨z, hz⟩).1 = ⟨p z, hz⟩ :=
        Subtype.ext (normalizeClosedCylinderRight_fst c p h₁ h₂ hp₁ hp₂ _)
      simp only [← hb, k.symm_apply_apply]
  · intro q
    rcases Cover q with hq | hq
    · rw [il q hq]
      have hb : p (i ⟨q, hq⟩) = q.1 := chart_symm_base h₁ hp₁ _
      rw [fl _ (show i ⟨q, hq⟩ ∈ s from show (p (i ⟨q, hq⟩)).2 ≤ c by rw [hb]; exact hq)]
      apply Prod.ext hb
      change (h₁ (h₁.symm (⟨q.1, hq⟩, q.2))).2 = q.2
      exact congrArg Prod.snd (h₁.apply_symm_apply _)
    · rw [ir q hq]
      have hb : p (j ⟨q, hq⟩) = q.1 :=
        chart_symm_base k (normalizeClosedCylinderRight_fst c p h₁ h₂ hp₁ hp₂) _
      rw [fr _ (show j ⟨q, hq⟩ ∈ t from show c ≤ (p (j ⟨q, hq⟩)).2 by rw [hb]; exact hq)]
      apply Prod.ext hb
      change (k (k.symm (⟨q.1, hq⟩, q.2))).2 = q.2
      exact congrArg Prod.snd (k.apply_symm_apply _)
  · apply continuous_closedCoverMap s t
      (isClosed_Iic.preimage hπ.snd) (isClosed_Ici.preimage hπ.snd) cover f g agree
    · exact (hπ.comp continuous_subtype_val).prodMk h₁.continuous.snd
    · exact (hπ.comp continuous_subtype_val).prodMk k.continuous.snd
  · apply continuous_closedCoverMap S U
      (isClosed_Iic.preimage (continuous_snd.comp continuous_fst))
      (isClosed_Ici.preimage (continuous_snd.comp continuous_fst)) Cover i j Agree
    · exact continuous_subtype_val.comp (h₁.symm.continuous.comp
        ((continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd))
    · exact continuous_subtype_val.comp (k.symm.continuous.comp
        ((continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd))

private theorem cylinderHomeomorph_left [ClosedIicTopology T] [ClosedIciTopology T]
    (hπ : Continuous p) (z : Z) (hz : (p z).2 ≤ c) :
    cylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ z = (p z, (h₁ ⟨z, hz⟩).2) :=
  closedCoverMap_left {z | (p z).2 ≤ c} {z | c ≤ (p z).2}
    (fun _ ↦ le_total _ _) (fun z ↦ (p z.val, (h₁ z).2))
    (fun z ↦ (p z.val, (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ z).2)) z hz

private theorem cylinderHomeomorph_right [ClosedIicTopology T] [ClosedIciTopology T]
    (hπ : Continuous p) (z : Z) (hz : c ≤ (p z).2) :
    cylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ z =
      (p z, (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ ⟨z, hz⟩).2) :=
  closedCoverMap_right {z | (p z).2 ≤ c} {z | c ≤ (p z).2}
    (fun _ ↦ le_total _ _) (fun z ↦ (p z.val, (h₁ z).2))
    (fun z ↦ (p z.val, (normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂ z).2))
    (normalized_chart_agree c p h₁ h₂ hp₁ hp₂) z hz

private theorem cylinderHomeomorph_base [ClosedIicTopology T] [ClosedIciTopology T]
    (hπ : Continuous p) (z : Z) :
    (cylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ z).1 = p z := by
  rcases le_total (p z).2 c with hz | hz
  · rw [cylinderHomeomorph_left c p h₁ h₂ hp₁ hp₂ hπ z hz]
  · rw [cylinderHomeomorph_right c p h₁ h₂ hp₁ hp₂ hπ z hz]

private theorem trivialization_cast_base {B : Type*} [TopologicalSpace B]
    {q r : Z → B} (h : q = r) (e : Trivialization F q) :
    (h ▸ e : Trivialization F r).baseSet = e.baseSet := by
  cases h
  rfl

private theorem trivialization_cast_apply {B : Type*} [TopologicalSpace B]
    {q r : Z → B} (h : q = r) (e : Trivialization F q) (z : Z) :
    (h ▸ e : Trivialization F r) z = e z := by
  cases h
  rfl

/-- Glue closed-piece global charts after normalizing the right chart on the seam.

The input charts are defined on the two restricted spaces, not on all of `Z`.
Continuity of `p` makes these a closed cover. No agreement between the original
charts and no extra inverse-continuity hypothesis is required. Both projection
continuity and closed time slabs are essential: on three ordered points, a
noncontinuous projection or nonclosed slabs can admit the two restricted charts
without a global chart.

This is the construction in Hatcher, Proposition 1.7, preliminary fact (1). -/
noncomputable def glueClosedCylinder (c : T) (p : Z → X × T)
    (h₁ : (p ⁻¹' {b : X × T | b.2 ≤ c}) ≃ₜ {b : X × T | b.2 ≤ c} × F)
    (h₂ : (p ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × F)
    (hp₁ : ∀ z : p ⁻¹' {b : X × T | b.2 ≤ c}, (h₁ z).1.val = p z.val)
    (hp₂ : ∀ z : p ⁻¹' {b : X × T | c ≤ b.2}, (h₂ z).1.val = p z.val)
    [ClosedIicTopology T] [ClosedIciTopology T]
    (hπ : Continuous p) : Trivialization F p := private_decl% (show Trivialization F p from by
  let h : Z ≃ₜ TotalSpace F (Bundle.Trivial (X × T) F) := by
    exact (cylinderHomeomorph c p h₁ h₂ hp₁ hp₂ hπ).trans
      (Bundle.Trivial.homeomorphProd (X × T) F).symm
  have hp : (π F (Bundle.Trivial (X × T) F)) ∘ h = p := by
    exact funext (cylinderHomeomorph_base c p h₁ h₂ hp₁ hp₂ hπ)
  exact hp ▸ (Bundle.Trivial.trivialization (X × T) F).compHomeomorph h)

variable [ClosedIicTopology T] [ClosedIciTopology T] (hπ : Continuous p)

/-- The glued chart is global. -/
@[simp] theorem glueClosedCylinder_baseSet :
    (glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ).baseSet = univ := by
  change (glueClosedCylinder._private_1 c p h₁ h₂ hp₁ hp₂ hπ).baseSet = _
  unfold glueClosedCylinder._private_1
  rw [trivialization_cast_base]
  rfl

/-- The glued trivialization preserves the original projection. -/
@[simp] theorem glueClosedCylinder_fst (z : Z) :
    (glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ z).1 = p z := by
  exact (glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ).coe_fst'
    (by rw [glueClosedCylinder_baseSet]; trivial)

/-- The glued chart restricts to the original left chart, including the seam. -/
theorem glueClosedCylinder_apply_left (z : Z) (hz : (p z).2 ≤ c) :
    glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ z = (p z, (h₁ ⟨z, hz⟩).2) := by
  change (glueClosedCylinder._private_1 c p h₁ h₂ hp₁ hp₂ hπ) z = _
  unfold glueClosedCylinder._private_1
  rw [trivialization_cast_apply]
  exact cylinderHomeomorph_left c p h₁ h₂ hp₁ hp₂ hπ z hz

/-- The glued chart restricts to the normalized right chart, including the seam. -/
theorem glueClosedCylinder_apply_right (z : Z) (hz : c ≤ (p z).2) :
    glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ z =
      (p z, closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (p z).1 (h₂ ⟨z, hz⟩).2) := by
  have ha := cylinderHomeomorph_right c p h₁ h₂ hp₁ hp₂ hπ z hz
  rw [normalizeClosedCylinderRight_apply, hp₂] at ha
  change (glueClosedCylinder._private_1 c p h₁ h₂ hp₁ hp₂ hπ) z = _
  unfold glueClosedCylinder._private_1
  rw [trivialization_cast_apply]
  exact ha

/-- In left coordinates the inverse is the inverse of the original left chart. -/
theorem glueClosedCylinder_symm_apply_left (b : X × T) (hb : b.2 ≤ c) (v : F) :
    (glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ).toOpenPartialHomeomorph.symm (b, v) =
      (h₁.symm (⟨b, hb⟩, v)).val := by
  let e := glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ
  let z := h₁.symm (⟨b, hb⟩, v)
  have hz : p z.val = b := chart_symm_base h₁ hp₁ _
  have hzl : (p z.val).2 ≤ c := hz ▸ hb
  have hf : e z.val = (b, v) := by
    rw [glueClosedCylinder_apply_left c p h₁ h₂ hp₁ hp₂ hπ z.val hzl]
    apply Prod.ext hz
    change (h₁ (h₁.symm (⟨b, hb⟩, v))).2 = v
    exact congrArg Prod.snd (h₁.apply_symm_apply _)
  have hi := e.toOpenPartialHomeomorph.left_inv
    (e.mem_source.mpr (show p z.val ∈ e.baseSet by rw [glueClosedCylinder_baseSet]; trivial))
  change e.toOpenPartialHomeomorph.symm (e z.val) = z.val at hi
  rw [hf] at hi
  exact hi

/-- In right coordinates first undo the seam change, then use the right inverse. -/
theorem glueClosedCylinder_symm_apply_right (b : X × T) (hb : c ≤ b.2) (v : F) :
    (glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ).toOpenPartialHomeomorph.symm (b, v) =
      (h₂.symm (⟨b, hb⟩,
        (closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ b.1).symm v)).val := by
  let e := glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ
  let k := normalizeClosedCylinderRight c p h₁ h₂ hp₁ hp₂
  let z := k.symm (⟨b, hb⟩, v)
  have hz : p z.val = b :=
    chart_symm_base k (normalizeClosedCylinderRight_fst c p h₁ h₂ hp₁ hp₂) _
  have hzr : c ≤ (p z.val).2 := hz ▸ hb
  have hf : e z.val = (b, v) := by
    rw [glueClosedCylinder_apply_right c p h₁ h₂ hp₁ hp₂ hπ z.val hzr]
    have hk : (k ⟨z.val, hzr⟩).2 = v := congrArg Prod.snd (k.apply_symm_apply _)
    apply Prod.ext hz
    simpa only [k, normalizeClosedCylinderRight_apply, hp₂, hz] using hk
  have hi := e.toOpenPartialHomeomorph.left_inv
    (e.mem_source.mpr (show p z.val ∈ e.baseSet by rw [glueClosedCylinder_baseSet]; trivial))
  change e.toOpenPartialHomeomorph.symm (e z.val) = z.val at hi
  rw [hf] at hi
  exact hi

/-- A global trivialization with these two coordinate formulas is the glued chart. -/
theorem glueClosedCylinder_unique (e : Trivialization F p) (he : e.baseSet = univ)
    (hl : ∀ (z : Z) (hz : (p z).2 ≤ c), e z = (p z, (h₁ ⟨z, hz⟩).2))
    (hr : ∀ (z : Z) (hz : c ≤ (p z).2),
      e z = (p z,
        closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (p z).1 (h₂ ⟨z, hz⟩).2)) :
    e = glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ := by
  let g := glueClosedCylinder c p h₁ h₂ hp₁ hp₂ hπ
  have hf : ∀ z, e z = g z := by
    intro z
    rcases le_total (p z).2 c with hz | hz
    · rw [hl z hz, glueClosedCylinder_apply_left c p h₁ h₂ hp₁ hp₂ hπ z hz]
    · rw [hr z hz, glueClosedCylinder_apply_right c p h₁ h₂ hp₁ hp₂ hπ z hz]
  apply toPretrivialization_injective
  apply Pretrivialization.ext hf ?_
    (he.trans (glueClosedCylinder_baseSet c p h₁ h₂ hp₁ hp₂ hπ).symm)
  intro q
  have hq : q ∈ g.target := g.mem_target.mpr (by rw [glueClosedCylinder_baseSet]; trivial)
  have hz : g.toOpenPartialHomeomorph.symm q ∈ e.source := e.mem_source.mpr (by rw [he]; trivial)
  have hi := e.toOpenPartialHomeomorph.left_inv hz
  have hfg : e (g.toOpenPartialHomeomorph.symm q) = q :=
    (hf _).trans (g.apply_symm_apply hq)
  change e.toOpenPartialHomeomorph.symm (e (g.toOpenPartialHomeomorph.symm q)) = _ at hi
  rw [hfg] at hi
  exact hi

end Cylinder

section PiecewiseLe

variable {T : Type uT} {Z : Type uZ} {F : Type uF}
  [TopologicalSpace T] [TopologicalSpace Z] [TopologicalSpace F]

private theorem preimageHomeomorph_fst {B : Type*} [TopologicalSpace B]
    {q : Z → B} (e : Trivialization F q) {s : Set B} (hs : s ⊆ e.baseSet)
    (z : q ⁻¹' s) :
    (e.preimageHomeomorph hs z).1.val = q z.val := by
  simp only [preimageHomeomorph_apply]

private theorem punitProd_preimage_subset {q : Z → T} (e : Trivialization F q)
    {s : Set T} (hs : s ⊆ e.baseSet) :
    {b : PUnit × T | b.2 ∈ s} ⊆
      (e.homeomorphComp (Homeomorph.punitProd T).symm).baseSet := by
  intro b hb
  exact hs hb

variable [LinearOrder T] [OrderTopology T]

omit [OrderTopology T] in
private theorem continuous_paired_of_half_charts {q : Z → T}
    (e₁ e₂ : Trivialization F q) (c : T)
    (hl : Iic c ⊆ e₁.baseSet) (hr : Ici c ⊆ e₂.baseSet) :
    Continuous ((Homeomorph.punitProd T).symm ∘ q) := by
  have hq : Continuous q := continuous_iff_continuousAt.2 fun z ↦ by
    rcases le_total (q z) c with hz | hz
    · exact e₁.continuousAt_proj (e₁.mem_source.2 (hl hz))
    · exact e₂.continuousAt_proj (e₂.mem_source.2 (hr hz))
  exact (Homeomorph.punitProd T).symm.continuous.comp hq

private theorem piecewiseLe_apply {q : Z → T} (e₁ e₂ : Trivialization F q)
    (c : T) (hc₁ : c ∈ e₁.baseSet) (hc₂ : c ∈ e₂.baseSet) (z : Z) :
    e₁.piecewiseLe e₂ c hc₁ hc₂ z =
      if q z ≤ c then e₁ z else ((e₂ z).1, e₂.coordChange e₁ c (e₂ z).2) := by
  classical
  simp only [piecewiseLe, piecewiseLeOfEq, piecewise, coe_mk,
    OpenPartialHomeomorph.piecewise_apply]
  simp only [Set.piecewise, mem_preimage, mem_Iic, coe_coe,
    transFiberHomeomorph_apply, coordChangeHomeomorph_coe]

/-- On closed-half restrictions of ambient charts, closed-cylinder gluing is
`piecewiseLe` transported to the base `PUnit × T`.

The paired projection `(Homeomorph.punitProd T).symm ∘ q` is
`z ↦ (PUnit.unit, q z)`. The ambient base sets need only contain their respective
closed halves, not the whole base. Their source cover supplies continuity of the
projection. All product and subspace topologies are the canonical ones.

This equality of trivializations includes their base sets, forward maps
and inverse maps; in particular the transported `piecewiseLe` chart is global. -/
theorem glueClosedCylinder_eq_piecewiseLe {q : Z → T}
    (e₁ e₂ : Trivialization F q) (c : T)
    (hl : Iic c ⊆ e₁.baseSet) (hr : Ici c ⊆ e₂.baseSet) :
    glueClosedCylinder c ((Homeomorph.punitProd T).symm ∘ q)
      ((e₁.homeomorphComp (Homeomorph.punitProd T).symm).preimageHomeomorph
        (by exact punitProd_preimage_subset e₁ hl))
      ((e₂.homeomorphComp (Homeomorph.punitProd T).symm).preimageHomeomorph
        (by exact punitProd_preimage_subset e₂ hr))
      (by exact preimageHomeomorph_fst _ (punitProd_preimage_subset e₁ hl))
      (by exact preimageHomeomorph_fst _ (punitProd_preimage_subset e₂ hr))
      (by exact continuous_paired_of_half_charts e₁ e₂ c hl hr) =
    (e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)).homeomorphComp
      (Homeomorph.punitProd T).symm := by
  let H := (Homeomorph.punitProd T).symm
  let p := H ∘ q
  let h₁ := (e₁.homeomorphComp H).preimageHomeomorph
    (punitProd_preimage_subset e₁ hl)
  let h₂ := (e₂.homeomorphComp H).preimageHomeomorph
    (punitProd_preimage_subset e₂ hr)
  let hp₁ := preimageHomeomorph_fst (e₁.homeomorphComp H)
    (punitProd_preimage_subset e₁ hl)
  let hp₂ := preimageHomeomorph_fst (e₂.homeomorphComp H)
    (punitProd_preimage_subset e₂ hr)
  have hα (v : F) :
      closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ PUnit.unit v =
        e₂.coordChange e₁ c v := by
    let z := e₂.toOpenPartialHomeomorph.symm (c, v)
    have hz : q z = c := e₂.proj_symm_apply' (hr le_rfl)
    have hpz : p z = (PUnit.unit, c) := by
      change (PUnit.unit, q z) = (PUnit.unit, c)
      rw [hz]
    have heq := closedCylinderCoordChange_apply c p h₁ h₂ hp₁ hp₂ PUnit.unit z hpz
    change closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ PUnit.unit
      ((e₂.homeomorphComp H).preimageHomeomorph _ ⟨z, _⟩).2 =
      ((e₁.homeomorphComp H).preimageHomeomorph _ ⟨z, _⟩).2 at heq
    simp only [preimageHomeomorph_apply] at heq
    change closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ PUnit.unit (e₂ z).2 =
      (e₁ z).2 at heq
    simpa only [z, e₂.apply_symm_apply' (hr le_rfl), coordChange] using heq
  change glueClosedCylinder c p h₁ h₂ hp₁ hp₂ _ = _
  symm
  apply glueClosedCylinder_unique
  · change H.symm ⁻¹' (Iic c).ite e₁.baseSet e₂.baseSet = univ
    apply eq_univ_of_forall
    intro b
    change b.2 ∈ (Iic c).ite e₁.baseSet e₂.baseSet
    by_cases hb : b.2 ≤ c
    · simpa only [Set.ite, mem_union, mem_inter_iff, mem_sdiff, mem_Iic, hb,
        and_true, not_true_eq_false, and_false, or_false] using hl hb
    · simpa only [Set.ite, mem_union, mem_inter_iff, mem_sdiff, mem_Iic, hb,
        and_false, not_false_eq_true, and_true, false_or] using hr (le_of_not_ge hb)
  · intro z hz
    change q z ≤ c at hz
    change (H ((e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z).1,
      ((e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z).2) = _
    have he : (e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z = e₁ z := by
      rw [piecewiseLe_apply, ite_eq_left hz]
    rw [he]
    apply Prod.ext
    · exact congrArg H (e₁.coe_fst' (hl hz))
    · change (e₁ z).2 = (h₁ ⟨z, hz⟩).2
      simp only [h₁, preimageHomeomorph_apply]
      rfl
  · intro z hz
    have hcoord : closedCylinderCoordChange c p h₁ h₂ hp₁ hp₂ (p z).1
        (h₂ ⟨z, hz⟩).2 = e₂.coordChange e₁ c (e₂ z).2 := by
      exact hα (e₂ z).2
    have he : (e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z =
        (q z, e₂.coordChange e₁ c (e₂ z).2) := by
      by_cases hz' : q z ≤ c
      · have hzc : q z = c := le_antisymm hz' hz
        rw [piecewiseLe_apply, ite_eq_left hz']
        apply Prod.ext
        · exact e₁.coe_fst' (hl hz')
        · simpa only [← hzc] using (e₂.coordChange_apply_snd e₁ (hr hz)).symm
      · rw [piecewiseLe_apply, ite_eq_right hz', e₂.coe_fst' (hr hz)]
    change (H ((e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z).1,
      ((e₁.piecewiseLe e₂ c (hl le_rfl) (hr le_rfl)) z).2) = _
    rw [he]
    apply Prod.ext
    · rfl
    · exact hcoord.symm

end PiecewiseLe

section Linear

private noncomputable def restrictedChartLinearEquiv
    {B : Type*} {F : Type*} {K : Type*} {E : B → Type*}
    [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [Semiring K] [AddCommMonoid F] [Module K F]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
    {s : Set B} (h : ((π F E) ⁻¹' s) ≃ₜ s × F)
    (hp : ∀ z : (π F E) ⁻¹' s, (h z).1.val = z.val.proj)
    (b : B) (hb : b ∈ s)
    (hlin : IsLinearMap K (fun v : E b ↦ (h ⟨⟨b, v⟩, hb⟩).2)) :
    E b ≃ₗ[K] F := by
  apply LinearEquiv.ofBijective (hlin.mk' _)
  constructor
  · intro v w hvw
    apply TotalSpace.mk_injective (F := F) b
    have he : h ⟨⟨b, v⟩, hb⟩ = h ⟨⟨b, w⟩, hb⟩ :=
      Prod.ext (Subtype.ext ((hp ⟨⟨b, v⟩, hb⟩).trans (hp ⟨⟨b, w⟩, hb⟩).symm)) hvw
    exact congrArg Subtype.val (h.injective he)
  · intro v
    obtain ⟨⟨⟨b', w⟩, hz⟩, he⟩ := h.surjective (⟨b, hb⟩, v)
    have hbb : b' = b := by
      have hbase := hp ⟨⟨b', w⟩, hz⟩
      rw [he] at hbase
      exact hbase.symm
    subst b'
    exact ⟨w, congrArg Prod.snd he⟩

variable {X : Type uX} {T : Type uT} {F : Type uF} {K : Type uK}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T]
  [ClosedIicTopology T] [ClosedIciTopology T] [TopologicalSpace F]
  [Semiring K] [AddCommMonoid F] [Module K F]
  {E : X × T → Type uE} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module K (E b)]
  (c : T)

/-- Fiberwise linearity of the two restricted charts is inherited by the global
trivialization on the dependent total space. The inverse linearity needed in the
normalization follows from the supplied linear charts and their inverse laws. -/
theorem glueClosedCylinder_isLinear
    (h₁ : ((π F E) ⁻¹' {b : X × T | b.2 ≤ c}) ≃ₜ {b : X × T | b.2 ≤ c} × F)
    (h₂ : ((π F E) ⁻¹' {b : X × T | c ≤ b.2}) ≃ₜ {b : X × T | c ≤ b.2} × F)
    (hp₁ : ∀ z : (π F E) ⁻¹' {b : X × T | b.2 ≤ c}, (h₁ z).1.val = z.val.proj)
    (hp₂ : ∀ z : (π F E) ⁻¹' {b : X × T | c ≤ b.2}, (h₂ z).1.val = z.val.proj)
    (hπ : Continuous (π F E))
    (hl : ∀ (b : X × T) (hb : b.2 ≤ c),
      IsLinearMap K (fun v : E b ↦ (h₁ ⟨⟨b, v⟩, hb⟩).2))
    (hr : ∀ (b : X × T) (hb : c ≤ b.2),
      IsLinearMap K (fun v : E b ↦ (h₂ ⟨⟨b, v⟩, hb⟩).2)) :
    (glueClosedCylinder c (π F E) h₁ h₂ hp₁ hp₂ hπ).IsLinear K := by
  have hα (x : X) :
      IsLinearMap K (closedCylinderCoordChange c (π F E) h₁ h₂ hp₁ hp₂ x) := by
    let l₁ := restrictedChartLinearEquiv h₁ hp₁ (x, c) le_rfl (hl (x, c) le_rfl)
    let l₂ := restrictedChartLinearEquiv h₂ hp₂ (x, c) le_rfl (hr (x, c) le_rfl)
    have heq : (closedCylinderCoordChange c (π F E) h₁ h₂ hp₁ hp₂ x : F → F) =
        (l₂.symm.trans l₁ : F → F) := by
      funext v
      have hseam := closedCylinderCoordChange_apply c (π F E) h₁ h₂ hp₁ hp₂ x
        ⟨(x, c), l₂.symm v⟩ rfl
      change closedCylinderCoordChange c (π F E) h₁ h₂ hp₁ hp₂ x
        (l₂ (l₂.symm v)) = l₁ (l₂.symm v) at hseam
      simpa only [l₂.apply_symm_apply, LinearEquiv.trans_apply] using hseam
    rw [heq]
    exact (l₂.symm.trans l₁).toLinearMap.isLinear
  constructor
  intro b _
  rcases le_total b.2 c with hb | hb
  · convert hl b hb using 1
    funext v
    exact congrArg Prod.snd
      (glueClosedCylinder_apply_left c (π F E) h₁ h₂ hp₁ hp₂ hπ ⟨b, v⟩ hb)
  · convert (((hα b.1).mk' _).comp ((hr b hb).mk' _)).isLinear using 1
    funext v
    exact congrArg Prod.snd
      (glueClosedCylinder_apply_right c (π F E) h₁ h₂ hp₁ hp₂ hπ ⟨b, v⟩ hb)

end Linear

end Bundle.Trivialization
