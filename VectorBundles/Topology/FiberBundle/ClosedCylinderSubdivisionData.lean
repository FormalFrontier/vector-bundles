/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinderSlab
public import VectorBundles.Topology.UnitInterval

/-!
# Product charts from finite closed subdivisions

A finite monotone subdivision with at least one slab, together with base-preserving
product charts on the original preimages of its slabs, gives a product chart on the
original preimage of the whole interval. The models may depend on the slab and have
an independent universe. The result uses the first model and retains the first chart
on its entire closed slab, including the bottom and the first seam.

The construction is a recursion in data over nonempty prefixes. Its public
zero and successor equations identify the value at each stage. Each successor
uses `Bundle.Trivialization.glueClosedSlabHomeomorph`, retaining the entire
previous prefix. Repeated cuts, a single slab, empty base sets, and empty models
are allowed. No new closed-cover pasting construction is used here.

For the unit interval, the endpoint-normalized chart has domain the original
preimage of `U ×ˢ univ` and codomain `(U × I) × M 0`. Applying uniform subdivision
and rectangular restriction to an open cover of `X × I` gives a chart over a whole
cylinder near each point of `X`, retaining an original chart's bottom coordinates.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
* `Bundle.Trivialization.glueClosedSlabHomeomorph`, for adjoining two closed slabs.
-/

@[expose] public section

open Set
open scoped unitInterval

universe uX uT uZ uM uJ

namespace Bundle.Trivialization

section Subdivision

variable {X : Type uX} {T : Type uT} {Z : Type uZ}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T] [TopologicalSpace Z]
  [ClosedIicTopology T] [ClosedIciTopology T]
  (p : Z → X × T) (U : Set X) {N : ℕ} (hN : 1 ≤ N)
  (t : ℕ → T) (ht : Monotone t)
  (M : Fin N → Type uM) [∀ k, TopologicalSpace (M k)]
  (e : ∀ k : Fin N,
    (p ⁻¹' (U ×ˢ Icc (t k.val) (t (k.val + 1)))) ≃ₜ
      (U × Icc (t k.val) (t (k.val + 1))) × M k)
  (he : ∀ k z, (((e k z).1.1 : X), ((e k z).1.2 : T)) = p z.val)
  (hp : Continuous p)

private noncomputable def closedSubdivisionPrefixData :
    ∀ k : ℕ, k + 1 ≤ N →
      {H : (p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1)))) ≃ₜ
          (U × Icc (t 0) (t (k + 1))) × M ⟨0, hN⟩ //
        (∀ z, (((H z).1.1 : X), ((H z).1.2 : T)) = p z.val) ∧
        (∀ z (hz : (p z.val).2 ≤ t 1),
          (H z).2 =
            (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2)} := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨e ⟨0, hN⟩, he ⟨0, hN⟩, ?_⟩
      intro z hz
      rfl
  | succ k ih =>
      intro hk
      let previous := ih ((Nat.le_succ (k + 1)).trans hk)
      let H := previous.val
      have hH := previous.property.1
      have hfirst := previous.property.2
      have hac : t 0 ≤ t (k + 1) := ht (Nat.zero_le (k + 1))
      have hcb : t (k + 1) ≤ t (k + 1 + 1) := ht (Nat.le_succ (k + 1))
      let G := glueClosedSlabHomeomorph p U (t 0) (t (k + 1)) (t (k + 1 + 1))
        hac hcb H (e ⟨k + 1, hk⟩) hH (he ⟨k + 1, hk⟩) hp
      refine ⟨G, ?_, ?_⟩
      · exact glueClosedSlabHomeomorph_apply_base p U (t 0) (t (k + 1))
          (t (k + 1 + 1)) hac hcb H (e ⟨k + 1, hk⟩) hH (he ⟨k + 1, hk⟩) hp
      · intro z hz
        have hzleft : (p z.val).2 ≤ t (k + 1) :=
          hz.trans (ht (Nat.succ_le_succ (Nat.zero_le k)))
        have hglue := congrArg Prod.snd
          (glueClosedSlabHomeomorph_apply_left p U (t 0) (t (k + 1))
            (t (k + 1 + 1)) hac hcb H (e ⟨k + 1, hk⟩) hH
            (he ⟨k + 1, hk⟩) hp z hzleft)
        exact hglue.trans (hfirst
          ⟨z.val, ⟨z.property.1, z.property.2.1, hzleft⟩⟩ hz)

/-- Assemble the first `k + 1` closed slabs by recursion, using the first slab's
model. At each successor, adjoin the next chart with
`glueClosedSlabHomeomorph`. -/
noncomputable def closedSubdivisionPrefixHomeomorph (k : ℕ) (hk : k + 1 ≤ N) :
    (p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1)))) ≃ₜ
      (U × Icc (t 0) (t (k + 1))) × M ⟨0, hN⟩ := private_decl% (show
        (p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1)))) ≃ₜ
          (U × Icc (t 0) (t (k + 1))) × M ⟨0, hN⟩ from
  (closedSubdivisionPrefixData p U hN t ht M e he hp k hk).val)

/-- Every recursively assembled prefix preserves both original base coordinates. -/
theorem closedSubdivisionPrefixHomeomorph_apply_base (k : ℕ) (hk : k + 1 ≤ N)
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1)))) :
    (((closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k hk z).1.1 : X),
      ((closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k hk z).1.2 : T)) =
        p z.val := private_decl% (by
  exact (closedSubdivisionPrefixData p U hN t ht M e he hp k hk).property.1 z)

/-- The prefix with one slab is the given first chart. -/
@[simp] theorem closedSubdivisionPrefixHomeomorph_zero (hk : 1 ≤ N) :
    closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp 0 hk = e ⟨0, hN⟩ :=
  private_decl% (by rfl)

/-- The next prefix is precisely one closed-slab gluing of the preceding prefix
and the next given chart. In particular, the recursive value, not only its base
and first-slab properties, is determined. -/
theorem closedSubdivisionPrefixHomeomorph_succ (k : ℕ) (hk : k + 1 + 1 ≤ N) :
    closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp (k + 1) hk =
      glueClosedSlabHomeomorph p U (t 0) (t (k + 1)) (t (k + 1 + 1))
        (ht (Nat.zero_le (k + 1))) (ht (Nat.le_succ (k + 1)))
        (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k
          ((Nat.le_succ (k + 1)).trans hk))
        (e ⟨k + 1, hk⟩)
        (closedSubdivisionPrefixHomeomorph_apply_base p U hN t ht M e he hp k
          ((Nat.le_succ (k + 1)).trans hk))
        (he ⟨k + 1, hk⟩) hp := private_decl% (by rfl)

/-- The successor equation retains the preceding prefix's fiber coordinate
throughout its whole closed interval, including the seam. -/
theorem closedSubdivisionPrefixHomeomorph_succ_apply_left
    (k : ℕ) (hk : k + 1 + 1 ≤ N)
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1 + 1))))
    (hz : (p z.val).2 ≤ t (k + 1)) :
    closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp (k + 1) hk z =
      ((⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩),
        (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k
          ((Nat.le_succ (k + 1)).trans hk)
          ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2) := by
  rw [closedSubdivisionPrefixHomeomorph_succ p U hN t ht M e he hp k hk]
  exact glueClosedSlabHomeomorph_apply_left p U (t 0) (t (k + 1))
    (t (k + 1 + 1)) (ht (Nat.zero_le (k + 1))) (ht (Nat.le_succ (k + 1)))
    (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k
      ((Nat.le_succ (k + 1)).trans hk))
    (e ⟨k + 1, hk⟩)
    (closedSubdivisionPrefixHomeomorph_apply_base p U hN t ht M e he hp k
      ((Nat.le_succ (k + 1)).trans hk))
    (he ⟨k + 1, hk⟩) hp z hz

/-- The first chart's fiber coordinate is retained in every nonempty prefix. -/
theorem closedSubdivisionPrefixHomeomorph_apply_first_snd
    (k : ℕ) (hk : k + 1 ≤ N)
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t (k + 1)))) (hz : (p z.val).2 ≤ t 1) :
    (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k hk z).2 =
      (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2 :=
  private_decl% (by
    exact (closedSubdivisionPrefixData p U hN t ht M e he hp k hk).property.2 z hz)

private noncomputable def closedSubdivisionData :
    {H : (p ⁻¹' (U ×ˢ Icc (t 0) (t N))) ≃ₜ
        (U × Icc (t 0) (t N)) × M ⟨0, hN⟩ //
      (∀ z, (((H z).1.1 : X), ((H z).1.2 : T)) = p z.val) ∧
      (∀ z (hz : (p z.val).2 ≤ t 1),
        (H z).2 =
          (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2)} := by
  cases N with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hN)
  | succ n =>
      exact closedSubdivisionPrefixData p U hN t ht M e he hp n (Nat.le_refl (n + 1))

/-- Assemble the charts of a nonempty finite monotone closed subdivision in the
original total space by taking its last recursively assembled prefix. The model
is the first slab's model, and the first chart's fiber coordinate is retained on
its whole closed slab. -/
noncomputable def closedSubdivisionHomeomorph :
    (p ⁻¹' (U ×ˢ Icc (t 0) (t N))) ≃ₜ
      (U × Icc (t 0) (t N)) × M ⟨0, hN⟩ := private_decl% (show
        (p ⁻¹' (U ×ˢ Icc (t 0) (t N))) ≃ₜ
          (U × Icc (t 0) (t N)) × M ⟨0, hN⟩ from
  (closedSubdivisionData p U hN t ht M e he hp).val)

/-- The final fiber coordinate is that of the terminal prefix. The source point
is the same point of the original total space, with its endpoint proof rewritten. -/
theorem closedSubdivisionHomeomorph_apply_snd_eq_prefix
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) :
    (closedSubdivisionHomeomorph p U hN t ht M e he hp z).2 =
      (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp (N - 1)
        (by rw [Nat.sub_add_cancel hN])
        ⟨z.val, by simpa only [Nat.sub_add_cancel hN] using z.property⟩).2 :=
  private_decl% (by
    cases N with
    | zero => cases hN
    | succ n => rfl)

/-- The assembled chart preserves both coordinates in the original base space. -/
theorem closedSubdivisionHomeomorph_apply_base
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) :
    (((closedSubdivisionHomeomorph p U hN t ht M e he hp z).1.1 : X),
      ((closedSubdivisionHomeomorph p U hN t ht M e he hp z).1.2 : T)) = p z.val :=
  private_decl% (by
    exact (closedSubdivisionData p U hN t ht M e he hp).property.1 z)

/-- The assembled chart preserves the base point in the product of subspaces. -/
@[simp] theorem closedSubdivisionHomeomorph_proj
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) :
    (closedSubdivisionHomeomorph p U hN t ht M e he hp z).1 =
      (⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩) := by
  have hb := closedSubdivisionHomeomorph_apply_base p U hN t ht M e he hp z
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hb
  · apply Subtype.ext
    exact congrArg Prod.snd hb

/-- The first fiber coordinate is unchanged throughout the first closed slab. -/
theorem closedSubdivisionHomeomorph_apply_first_snd
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) (hz : (p z.val).2 ≤ t 1) :
    (closedSubdivisionHomeomorph p U hN t ht M e he hp z).2 =
      (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2 := private_decl% (by
  exact (closedSubdivisionData p U hN t ht M e he hp).property.2 z hz)

/-- On the entire first slab, the assembled chart consists of the original base
point and the original first chart's fiber coordinate. This includes its seam. -/
theorem closedSubdivisionHomeomorph_apply_first
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) (hz : (p z.val).2 ≤ t 1) :
    closedSubdivisionHomeomorph p U hN t ht M e he hp z =
      ((⟨(p z.val).1, z.property.1⟩, ⟨(p z.val).2, z.property.2⟩),
        (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1, hz⟩⟩).2) :=
  Prod.ext (closedSubdivisionHomeomorph_proj p U hN t ht M e he hp z)
    (closedSubdivisionHomeomorph_apply_first_snd p U hN t ht M e he hp z hz)

/-- At the bottom, the assembled chart retains the first chart's fiber coordinate. -/
theorem closedSubdivisionHomeomorph_apply_bottom
    (z : p ⁻¹' (U ×ˢ Icc (t 0) (t N))) (hz : (p z.val).2 = t 0) :
    (closedSubdivisionHomeomorph p U hN t ht M e he hp z).2 =
      (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1, z.property.2.1,
        by rw [hz]; exact ht (Nat.zero_le 1)⟩⟩).2 :=
  closedSubdivisionHomeomorph_apply_first_snd p U hN t ht M e he hp z
    (by rw [hz]; exact ht (Nat.zero_le 1))

/-- The inverse of the assembled chart preserves the full original base point. -/
theorem closedSubdivisionHomeomorph_symm_apply_base
    (w : (U × Icc (t 0) (t N)) × M ⟨0, hN⟩) :
    p ((closedSubdivisionHomeomorph p U hN t ht M e he hp).symm w).val =
      ((w.1.1 : X), (w.1.2 : T)) := by
  let H := closedSubdivisionHomeomorph p U hN t ht M e he hp
  have hb := closedSubdivisionHomeomorph_apply_base p U hN t ht M e he hp (H.symm w)
  change (((H (H.symm w)).1.1 : X), ((H (H.symm w)).1.2 : T)) = p (H.symm w).val at hb
  rw [H.apply_symm_apply] at hb
  exact hb.symm

/-- On every time in the first slab, the assembled inverse gives the same point
of the original total space as the first chart inverse. -/
theorem closedSubdivisionHomeomorph_symm_apply_first
    (w : (U × Icc (t 0) (t N)) × M ⟨0, hN⟩) (hw : (w.1.2 : T) ≤ t 1) :
    ((closedSubdivisionHomeomorph p U hN t ht M e he hp).symm w).val =
      ((e ⟨0, hN⟩).symm
        ((w.1.1, ⟨(w.1.2 : T), w.1.2.property.1, hw⟩), w.2)).val := by
  let H := closedSubdivisionHomeomorph p U hN t ht M e he hp
  let v : (U × Icc (t 0) (t 1)) × M ⟨0, hN⟩ :=
    ((w.1.1, ⟨(w.1.2 : T), w.1.2.property.1, hw⟩), w.2)
  have hv : p ((e ⟨0, hN⟩).symm v).val = ((w.1.1 : X), (w.1.2 : T)) := by
    have hb := he ⟨0, hN⟩ ((e ⟨0, hN⟩).symm v)
    rw [(e ⟨0, hN⟩).apply_symm_apply] at hb
    exact hb.symm
  let z : p ⁻¹' (U ×ˢ Icc (t 0) (t N)) :=
    ⟨((e ⟨0, hN⟩).symm v).val,
      ⟨((e ⟨0, hN⟩).symm v).property.1,
        ((e ⟨0, hN⟩).symm v).property.2.1,
        ((e ⟨0, hN⟩).symm v).property.2.2.trans (ht hN)⟩⟩
  have hz : (p z.val).2 ≤ t 1 := ((e ⟨0, hN⟩).symm v).property.2.2
  have hf : H z = w := by
    change closedSubdivisionHomeomorph p U hN t ht M e he hp z = w
    rw [closedSubdivisionHomeomorph_apply_first p U hN t ht M e he hp z hz]
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hv
      · apply Subtype.ext
        exact congrArg Prod.snd hv
    · change (e ⟨0, hN⟩ ((e ⟨0, hN⟩).symm v)).2 = w.2
      exact congrArg Prod.snd ((e ⟨0, hN⟩).apply_symm_apply v)
  have hi := H.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi

/-- At the bottom time, the assembled inverse is the original first chart inverse. -/
theorem closedSubdivisionHomeomorph_symm_apply_bottom
    (w : (U × Icc (t 0) (t N)) × M ⟨0, hN⟩) (hw : (w.1.2 : T) = t 0) :
    ((closedSubdivisionHomeomorph p U hN t ht M e he hp).symm w).val =
      ((e ⟨0, hN⟩).symm
        ((w.1.1, ⟨(w.1.2 : T), w.1.2.property.1,
          by rw [hw]; exact ht (Nat.zero_le 1)⟩), w.2)).val :=
  closedSubdivisionHomeomorph_symm_apply_first p U hN t ht M e he hp w
    (by rw [hw]; exact ht (Nat.zero_le 1))

end Subdivision

section UnitInterval

variable {X : Type uX} {Z : Type uZ} [TopologicalSpace X] [TopologicalSpace Z]
  (p : Z → X × I) (U : Set X) {N : ℕ} (hN : 1 ≤ N)
  (t : ℕ → I) (ht : Monotone t) (ht0 : t 0 = 0) (htN : t N = 1)
  (M : Fin N → Type uM) [∀ k, TopologicalSpace (M k)]
  (e : ∀ k : Fin N,
    (p ⁻¹' (U ×ˢ Icc (t k.val) (t (k.val + 1)))) ≃ₜ
      (U × Icc (t k.val) (t (k.val + 1))) × M k)
  (he : ∀ k z, (((e k z).1.1 : X), ((e k z).1.2 : I)) = p z.val)
  (hp : Continuous p)

include ht0 htN in
private theorem subdivision_Icc_eq_univ : Icc (t 0) (t N) = (univ : Set I) := by
  rw [ht0, htN]
  exact unitInterval.univ_eq_Icc.symm

private def subdivisionUnitIntervalSource :
    (p ⁻¹' (U ×ˢ (univ : Set I))) ≃ₜ (p ⁻¹' (U ×ˢ Icc (t 0) (t N))) :=
  Homeomorph.setCongr (by rw [subdivision_Icc_eq_univ t ht0 htN])

private def subdivisionUnitIntervalTime : Icc (t 0) (t N) ≃ₜ I :=
  (Homeomorph.setCongr (subdivision_Icc_eq_univ t ht0 htN)).trans
    (Homeomorph.Set.univ I)

/-- Assemble a subdivision from `0` to `1`, identifying its whole closed interval
with the unit interval itself. The domain remains an original preimage and the
first slab's model and coordinates are retained. -/
noncomputable def closedSubdivisionUnitIntervalHomeomorph :
    (p ⁻¹' (U ×ˢ (univ : Set I))) ≃ₜ (U × I) × M ⟨0, hN⟩ := private_decl% (show
      (p ⁻¹' (U ×ˢ (univ : Set I))) ≃ₜ (U × I) × M ⟨0, hN⟩ from
  (subdivisionUnitIntervalSource p U t ht0 htN).trans
    ((closedSubdivisionHomeomorph p U hN t ht M e he hp).trans
      (((Homeomorph.refl U).prodCongr (subdivisionUnitIntervalTime t ht0 htN)).prodCongr
        (Homeomorph.refl (M ⟨0, hN⟩)))))

/-- Endpoint normalization leaves the assembled fiber coordinate unchanged at
every point, not only on the first slab. -/
theorem closedSubdivisionUnitIntervalHomeomorph_apply_snd_eq_subdivision
    (z : p ⁻¹' (U ×ˢ (univ : Set I))) :
    (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).2 =
      (closedSubdivisionHomeomorph p U hN t ht M e he hp
        ⟨z.val, ⟨z.property.1,
          by rw [ht0]; exact unitInterval.nonneg',
          by rw [htN]; exact unitInterval.le_one'⟩⟩).2 := private_decl% (by
  unfold closedSubdivisionUnitIntervalHomeomorph
  rfl)

/-- The endpoint-normalized chart keeps the original base coordinates. -/
theorem closedSubdivisionUnitIntervalHomeomorph_apply_base
    (z : p ⁻¹' (U ×ˢ (univ : Set I))) :
    (((closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).1.1 : X),
      (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).1.2) =
        p z.val := private_decl% (by
  exact closedSubdivisionHomeomorph_apply_base p U hN t ht M e he hp
    (subdivisionUnitIntervalSource p U t ht0 htN z))

/-- The endpoint-normalized chart preserves the base in `U × I`. -/
@[simp] theorem closedSubdivisionUnitIntervalHomeomorph_proj
    (z : p ⁻¹' (U ×ˢ (univ : Set I))) :
    (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).1 =
      (⟨(p z.val).1, z.property.1⟩, (p z.val).2) := by
  have hb := closedSubdivisionUnitIntervalHomeomorph_apply_base
    p U hN t ht ht0 htN M e he hp z
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hb
  · exact congrArg (fun q : X × I => q.2) hb

/-- On the first closed slab, normalization does not change the first fiber coordinate. -/
theorem closedSubdivisionUnitIntervalHomeomorph_apply_first_snd
    (z : p ⁻¹' (U ×ˢ (univ : Set I))) (hz : (p z.val).2 ≤ t 1) :
    (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).2 =
      (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1,
        by rw [ht0]; exact unitInterval.nonneg', hz⟩⟩).2 := private_decl% (by
  exact closedSubdivisionHomeomorph_apply_first_snd p U hN t ht M e he hp
    (subdivisionUnitIntervalSource p U t ht0 htN z) hz)

/-- The normalized chart retains the first chart's fiber coordinate at time zero. -/
theorem closedSubdivisionUnitIntervalHomeomorph_apply_bottom
    (z : p ⁻¹' (U ×ˢ (univ : Set I))) (hz : (p z.val).2 = 0) :
    (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp z).2 =
      (e ⟨0, hN⟩ ⟨z.val, ⟨z.property.1,
        by rw [ht0]; exact unitInterval.nonneg',
        by rw [hz, ← ht0]; exact ht (Nat.zero_le 1)⟩⟩).2 :=
  closedSubdivisionUnitIntervalHomeomorph_apply_first_snd p U hN t ht ht0 htN M e he hp z
    (by rw [hz, ← ht0]; exact ht (Nat.zero_le 1))

/-- The inverse of the endpoint-normalized chart preserves the original base. -/
theorem closedSubdivisionUnitIntervalHomeomorph_symm_apply_base
    (w : (U × I) × M ⟨0, hN⟩) :
    p ((closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp).symm w).val =
      ((w.1.1 : X), w.1.2) := by
  let H := closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp
  have hb := closedSubdivisionUnitIntervalHomeomorph_apply_base
    p U hN t ht ht0 htN M e he hp (H.symm w)
  change (((H (H.symm w)).1.1 : X), (H (H.symm w)).1.2) = p (H.symm w).val at hb
  rw [H.apply_symm_apply] at hb
  exact hb.symm

/-- Throughout the first slab the normalized inverse is the first chart inverse
at the same original time and fiber coordinate. -/
theorem closedSubdivisionUnitIntervalHomeomorph_symm_apply_first
    (w : (U × I) × M ⟨0, hN⟩) (hw : w.1.2 ≤ t 1) :
    ((closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp).symm w).val =
      ((e ⟨0, hN⟩).symm
        ((w.1.1, ⟨w.1.2, by rw [ht0]; exact unitInterval.nonneg', hw⟩), w.2)).val :=
  private_decl% (by
    exact closedSubdivisionHomeomorph_symm_apply_first p U hN t ht M e he hp
      ((w.1.1, (subdivisionUnitIntervalTime t ht0 htN).symm w.1.2), w.2) hw)

/-- At time zero the normalized inverse is the original first chart inverse. -/
theorem closedSubdivisionUnitIntervalHomeomorph_symm_apply_bottom
    (u : U) (v : M ⟨0, hN⟩) :
    ((closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp).symm
      ((u, (0 : I)), v)).val =
      ((e ⟨0, hN⟩).symm
        ((u, ⟨(0 : I), by rw [ht0],
          by rw [← ht0]; exact ht (Nat.zero_le 1)⟩), v)).val :=
  closedSubdivisionUnitIntervalHomeomorph_symm_apply_first
    p U hN t ht ht0 htN M e he hp ((u, (0 : I)), v)
    (by rw [← ht0]; exact ht (Nat.zero_le 1))

end UnitInterval

/-- An open cover of `X × I` by base-preserving product charts gives, near each
point of `X`, a product chart on a whole cylinder in the original total space.
Its model is one original chart's model, and both its forward and inverse bottom
coordinates are those of that same chart. No nonempty-model or separation
hypothesis on `X` is required.

This is the topological local cylinder construction in Hatcher, *Vector Bundles
and K-Theory*, Proposition 1.7, preliminary fact (1). -/
theorem exists_local_cylinder_homeomorph_of_preimage_charts
    {X : Type uX} {Z : Type uZ} {J : Type uJ}
    [TopologicalSpace X] [TopologicalSpace Z]
    (p : Z → X × I) (M : J → Type uM) [∀ j, TopologicalSpace (M j)]
    (W : J → Set (X × I))
    (e : ∀ j, (p ⁻¹' W j) ≃ₜ W j × M j)
    (hp : Continuous p) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : X × I, ∃ j, b ∈ W j)
    (he : ∀ j z, (e j z).1.val = p z.val) (x : X) :
    ∃ (U : Set X) (j₀ : J)
      (hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀)
      (H : {z : Z // (p z).1 ∈ U} ≃ₜ (U × I) × M j₀),
      IsOpen U ∧ x ∈ U ∧
      (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
      (∀ q : (U × I) × M j₀, p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ (u : U) (v : {z : Z // p z = (u.val, (0 : I))}),
        (H ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e j₀ ⟨v.val,
          Eq.mpr (congrArg (fun b => b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
      (∀ (u : U) (v : M j₀),
        (H.symm ((u, (0 : I)), v)).val =
        ((e j₀).symm (⟨(u.val, (0 : I)), hU₀ u⟩, v)).val) := by
  classical
  obtain ⟨U, hU, hxU, N, hN, t, ht0, ht, htN, j, hj⟩ :=
    exists_open_nhds_prod_Icc_subset_open_cover_unitInterval W hW hcover x
  let E : ∀ k : Fin N,
      (p ⁻¹' (U ×ˢ Icc (t k.val) (t (k.val + 1)))) ≃ₜ
        (U × Icc (t k.val) (t (k.val + 1))) × M (j k) :=
    fun k => (e (j k)).restrictPreimageProd (hj k) (he (j k))
  have hE : ∀ k z, (((E k z).1.1 : X), ((E k z).1.2 : I)) = p z.val := by
    intro k z
    rw [Homeomorph.restrictPreimageProd_apply]
  let Hraw := closedSubdivisionUnitIntervalHomeomorph
    p U hN t ht ht0 htN (fun k => M (j k)) E hE hp
  let S : {z : Z // (p z).1 ∈ U} ≃ₜ (p ⁻¹' (U ×ˢ (univ : Set I))) :=
    (Homeomorph.refl Z).subtype
      (fun z => ⟨fun hz => ⟨hz, mem_univ _⟩, fun hz => hz.1⟩)
  let H := S.trans Hraw
  let j₀ := j ⟨0, hN⟩
  have hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀ := by
    intro u
    apply hj ⟨0, hN⟩
    refine ⟨u.property, ?_, ?_⟩
    · rw [ht0]
    · rw [← ht0]
      exact ht (Nat.zero_le 1)
  refine ⟨U, j₀, hU₀, H, hU, hxU, ?_, ?_, ?_, ?_⟩
  · intro z
    exact closedSubdivisionUnitIntervalHomeomorph_apply_base
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp (S z)
  · intro q
    exact closedSubdivisionUnitIntervalHomeomorph_symm_apply_base
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp q
  · intro u v
    let z : {z : Z // (p z).1 ∈ U} :=
      ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩
    have hz : (p (S z).val).2 = 0 := congrArg Prod.snd v.property
    have hSz : (S z).val = v.val := rfl
    change (Hraw (S z)).2 = _
    simpa only [Hraw, E, Homeomorph.restrictPreimageProd_apply, hSz, j₀] using
      (closedSubdivisionUnitIntervalHomeomorph_apply_bottom
        p U hN t ht ht0 htN (fun k => M (j k)) E hE hp (S z) hz)
  · intro u v
    change (Hraw.symm ((u, (0 : I)), v)).val = _
    simpa only [Hraw, E, Homeomorph.restrictPreimageProd_symm_apply_val] using
      (closedSubdivisionUnitIntervalHomeomorph_symm_apply_bottom
        p U hN t ht ht0 htN (fun k => M (j k)) E hE hp u v)

end Bundle.Trivialization
