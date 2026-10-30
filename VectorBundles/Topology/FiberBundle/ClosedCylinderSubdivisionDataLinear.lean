/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.FiberBundle.ClosedCylinderSubdivisionData
public import VectorBundles.Topology.FiberBundle.FiniteCylinderCover

/-!
# Linear coordinates for charts assembled along a closed subdivision

A finite monotone closed subdivision with varying chart models has linear
coordinates on each given projection fiber whenever its input charts do.
`closedSubdivisionFiberLinearEquiv` refines the homeomorphism
`closedSubdivisionHomeomorph`; it does not construct another homeomorphism.
The first chart's linear coordinates are retained on its entire closed slab.

The unit-interval specialization, followed by rectangular restriction of an
ordinary open atlas, gives whole-cylinder charts near each spatial base point.
Both original-chart bottom laws and both linear-coordinate laws hold. Over a
compact base, the existing finite-cover selection theorems give finite families.

## Implementation notes

The proof proceeds by induction on the public successor equation for the prefix
homeomorphism. At a successor it uses `glueClosedSlabFiberLinearEquiv` and its
forward-coordinate formula. A family of linear equivalences is selected only
after its forward coordinates have been specified everywhere; this specification
uniquely determines every selected equivalence. The module structures on the
given projection fibers are never replaced. No topology on the scalar semiring
or continuity of addition or scalar multiplication is assumed.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.7, preliminary fact (1).
* `Bundle.Trivialization.closedSubdivisionPrefixHomeomorph_succ` for the
  subdivision recursion.
* `Bundle.Trivialization.glueClosedSlabFiberLinearEquiv` for the linear
  refinement of one closed-slab gluing.
-/

@[expose] public section

open Set
open scoped unitInterval

universe uX uT uZ uM uJ uR

namespace Bundle.Trivialization

section Subdivision

variable {X : Type uX} {T : Type uT} {Z : Type uZ} {R : Type uR}
  [TopologicalSpace X] [LinearOrder T] [TopologicalSpace T] [TopologicalSpace Z]
  [ClosedIicTopology T] [ClosedIciTopology T] [Semiring R]
  (p : Z → X × T) (U : Set X) {N : ℕ} (hN : 1 ≤ N)
  (t : ℕ → T) (ht : Monotone t)
  (M : Fin N → Type uM) [∀ k, TopologicalSpace (M k)]
  [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  [∀ d : X × T, AddCommMonoid {z : Z // p z = d}]
  [∀ d : X × T, Module R {z : Z // p z = d}]
  (e : ∀ k : Fin N,
    (p ⁻¹' (U ×ˢ Icc (t k.val) (t (k.val + 1)))) ≃ₜ
      (U × Icc (t k.val) (t (k.val + 1))) × M k)
  (he : ∀ k z, (((e k z).1.1 : X), ((e k z).1.2 : T)) = p z.val)
  (hp : Continuous p)
  (L : ∀ (k : Fin N) (d : X × T),
    d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1)) → {z : Z // p z = d} ≃ₗ[R] M k)
  (hL : ∀ (k : Fin N) (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) (v : {z : Z // p z = d}),
    L k d hd v = (e k ⟨v.val,
      Eq.mpr (congrArg (fun b : X × T =>
        b ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) v.property) hd⟩).2)

include L hL in
private theorem exists_closedSubdivisionPrefixFiberLinearEquiv :
    ∀ (k : ℕ) (hk : k + 1 ≤ N),
      ∃ K : ∀ (d : X × T), d ∈ U ×ˢ Icc (t 0) (t (k + 1)) →
          {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩,
        ∀ (d : X × T) (hd : d ∈ U ×ˢ Icc (t 0) (t (k + 1)))
          (v : {z : Z // p z = d}),
          K d hd v =
            (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k hk
              ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
                b ∈ U ×ˢ Icc (t 0) (t (k + 1))) v.property) hd⟩).2 := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨L ⟨0, hN⟩, ?_⟩
      intro d hd v
      rw [closedSubdivisionPrefixHomeomorph_zero p U hN t ht M e he hp hk]
      exact hL ⟨0, hN⟩ d hd v
  | succ k ih =>
      intro hk
      obtain ⟨K, hK⟩ := ih ((Nat.le_succ (k + 1)).trans hk)
      refine ⟨glueClosedSlabFiberLinearEquiv p U (t 0) (t (k + 1))
        (t (k + 1 + 1)) (ht (Nat.zero_le (k + 1))) (ht (Nat.le_succ (k + 1)))
        K (L ⟨k + 1, hk⟩), ?_⟩
      intro d hd v
      rw [closedSubdivisionPrefixHomeomorph_succ p U hN t ht M e he hp k hk]
      exact glueClosedSlabFiberLinearEquiv_apply p U (t 0) (t (k + 1))
        (t (k + 1 + 1)) (ht (Nat.zero_le (k + 1))) (ht (Nat.le_succ (k + 1)))
        (closedSubdivisionPrefixHomeomorph p U hN t ht M e he hp k
          ((Nat.le_succ (k + 1)).trans hk))
        (e ⟨k + 1, hk⟩)
        (closedSubdivisionPrefixHomeomorph_apply_base p U hN t ht M e he hp k
          ((Nat.le_succ (k + 1)).trans hk))
        (he ⟨k + 1, hk⟩) hp K (L ⟨k + 1, hk⟩) hK (hL ⟨k + 1, hk⟩) d hd v

include L hL in
private theorem exists_closedSubdivisionFiberLinearEquiv :
    ∃ K : ∀ (d : X × T), d ∈ U ×ˢ Icc (t 0) (t N) →
        {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩,
      ∀ (d : X × T) (hd : d ∈ U ×ˢ Icc (t 0) (t N))
        (v : {z : Z // p z = d}),
        K d hd v = (closedSubdivisionHomeomorph p U hN t ht M e he hp
          ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
            b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩).2 := by
  have hend : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hlast : N - 1 + 1 ≤ N := by rw [hend]
  obtain ⟨K, hK⟩ := exists_closedSubdivisionPrefixFiberLinearEquiv
    p U hN t ht M e he hp L hL (N - 1) hlast
  refine ⟨(fun d hd => K d (by simpa only [hend] using hd)), ?_⟩
  intro d hd v
  exact (hK d (by simpa only [hend] using hd) v).trans
    (closedSubdivisionHomeomorph_apply_snd_eq_prefix p U hN t ht M e he hp
      ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
        b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩).symm

/-- Linear coordinates on a given projection fiber of the assembled subdivision
chart. The model is the first slab's model, over an arbitrary scalar semiring. -/
noncomputable def closedSubdivisionFiberLinearEquiv (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) :
    {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩ := private_decl% (show
      {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩ from
  (Classical.choose
    (exists_closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL)) d hd)

/-- The linear coordinates are exactly the second coordinates of the assembled
subdivision homeomorphism at every point of each given projection fiber. -/
theorem closedSubdivisionFiberLinearEquiv_apply (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (v : {z : Z // p z = d}) :
    closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd v =
      (closedSubdivisionHomeomorph p U hN t ht M e he hp
        ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
          b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩).2 := private_decl% (by
  exact Classical.choose_spec
    (exists_closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL) d hd v)

/-- Forward-coordinate compatibility uniquely specifies the linear equivalence
on a projection fiber. -/
theorem closedSubdivisionFiberLinearEquiv_unique (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N))
    (K : {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩)
    (hK : ∀ v, K v = (closedSubdivisionHomeomorph p U hN t ht M e he hp
      ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
        b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩).2) :
    K = closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd := by
  apply LinearEquiv.ext
  intro v
  exact (hK v).trans
    (closedSubdivisionFiberLinearEquiv_apply p U hN t ht M e he hp L hL d hd v).symm

/-- The entire first closed slab retains the given first linear equivalence. -/
theorem closedSubdivisionFiberLinearEquiv_first (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (hfirst : d ∈ U ×ˢ Icc (t 0) (t 1)) :
    closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd =
      L ⟨0, hN⟩ d hfirst := by
  apply LinearEquiv.ext
  intro v
  rw [closedSubdivisionFiberLinearEquiv_apply p U hN t ht M e he hp L hL d hd v,
    closedSubdivisionHomeomorph_apply_first_snd p U hN t ht M e he hp _
      (by rw [v.property]; exact hfirst.2.2)]
  exact (hL ⟨0, hN⟩ d hfirst v).symm

/-- At the bottom endpoint the given first linear equivalence is unchanged. -/
theorem closedSubdivisionFiberLinearEquiv_bottom (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (hbottom : d.2 = t 0) :
    closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd =
      L ⟨0, hN⟩ d ⟨hd.1, hd.2.1, by rw [hbottom]; exact ht (Nat.zero_le 1)⟩ :=
  closedSubdivisionFiberLinearEquiv_first p U hN t ht M e he hp L hL d hd
    ⟨hd.1, hd.2.1, by rw [hbottom]; exact ht (Nat.zero_le 1)⟩

/-- On each projection fiber the full chart consists of the unchanged base and
the constructed linear coordinates. -/
theorem closedSubdivisionHomeomorph_apply_fiber (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (v : {z : Z // p z = d}) :
    closedSubdivisionHomeomorph p U hN t ht M e he hp
      ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
        b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩ =
      ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩),
        closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd v) := by
  apply Prod.ext
  · rw [closedSubdivisionHomeomorph_proj]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst v.property
    · apply Subtype.ext
      exact congrArg Prod.snd v.property
  · exact (closedSubdivisionFiberLinearEquiv_apply p U hN t ht M e he hp L hL d hd v).symm

/-- Inverse linear coordinates give the same point of the given total space as
the assembled chart inverse, at every time. -/
theorem closedSubdivisionHomeomorph_symm_apply_fiber (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (w : M ⟨0, hN⟩) :
    ((closedSubdivisionHomeomorph p U hN t ht M e he hp).symm
      ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩), w)).val =
      ((closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd).symm w).val := by
  let H := closedSubdivisionHomeomorph p U hN t ht M e he hp
  let v := (closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d hd).symm w
  let z : p ⁻¹' (U ×ˢ Icc (t 0) (t N)) :=
    ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
      b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩
  have hf : H z = ((⟨d.1, hd.1⟩, ⟨d.2, hd.2⟩), w) := by
    have h := closedSubdivisionHomeomorph_apply_fiber p U hN t ht M e he hp L hL d hd v
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hi := H.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi

include L hL in
/-- The assembled chart sends scalar multiplication in each given projection
fiber to scalar multiplication in the first model. -/
theorem closedSubdivisionHomeomorph_apply_smul (d : X × T)
    (hd : d ∈ U ×ˢ Icc (t 0) (t N)) (r : R) (v : {z : Z // p z = d}) :
    (closedSubdivisionHomeomorph p U hN t ht M e he hp
      ⟨(r • v).val, Eq.mpr (congrArg (fun b : X × T =>
        b ∈ U ×ˢ Icc (t 0) (t N)) (r • v).property) hd⟩).2 =
      r • (closedSubdivisionHomeomorph p U hN t ht M e he hp
        ⟨v.val, Eq.mpr (congrArg (fun b : X × T =>
          b ∈ U ×ˢ Icc (t 0) (t N)) v.property) hd⟩).2 := by
  rw [← closedSubdivisionFiberLinearEquiv_apply p U hN t ht M e he hp L hL d hd (r • v),
    ← closedSubdivisionFiberLinearEquiv_apply p U hN t ht M e he hp L hL d hd v]
  exact (closedSubdivisionFiberLinearEquiv
    p U hN t ht M e he hp L hL d hd).toLinearMap.map_smul r v

end Subdivision

section UnitInterval

variable {X : Type uX} {Z : Type uZ} {R : Type uR}
  [TopologicalSpace X] [TopologicalSpace Z] [Semiring R]
  (p : Z → X × I) (U : Set X) {N : ℕ} (hN : 1 ≤ N)
  (t : ℕ → I) (ht : Monotone t) (ht0 : t 0 = 0) (htN : t N = 1)
  (M : Fin N → Type uM) [∀ k, TopologicalSpace (M k)]
  [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  [∀ d : X × I, AddCommMonoid {z : Z // p z = d}]
  [∀ d : X × I, Module R {z : Z // p z = d}]
  (e : ∀ k : Fin N,
    (p ⁻¹' (U ×ˢ Icc (t k.val) (t (k.val + 1)))) ≃ₜ
      (U × Icc (t k.val) (t (k.val + 1))) × M k)
  (he : ∀ k z, (((e k z).1.1 : X), ((e k z).1.2 : I)) = p z.val)
  (hp : Continuous p)
  (L : ∀ (k : Fin N) (d : X × I),
    d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1)) → {z : Z // p z = d} ≃ₗ[R] M k)
  (hL : ∀ (k : Fin N) (d : X × I)
    (hd : d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) (v : {z : Z // p z = d}),
    L k d hd v = (e k ⟨v.val,
      Eq.mpr (congrArg (fun b : X × I =>
        b ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) v.property) hd⟩).2)

/-- Linear coordinates on the given projection fibers of an endpoint-normalized
subdivision chart. Only the interval-membership proof is changed. -/
noncomputable def closedSubdivisionUnitIntervalFiberLinearEquiv (d : X × I)
    (hd : d ∈ U ×ˢ (univ : Set I)) : {z : Z // p z = d} ≃ₗ[R] M ⟨0, hN⟩ :=
  closedSubdivisionFiberLinearEquiv p U hN t ht M e he hp L hL d
    ⟨hd.1, by rw [ht0]; exact unitInterval.nonneg',
      by rw [htN]; exact unitInterval.le_one'⟩

/-- The normalized linear coordinates equal the normalized chart's fiber
coordinates at every point of every given projection fiber. -/
theorem closedSubdivisionUnitIntervalFiberLinearEquiv_apply (d : X × I)
    (hd : d ∈ U ×ˢ (univ : Set I)) (v : {z : Z // p z = d}) :
    closedSubdivisionUnitIntervalFiberLinearEquiv p U hN t ht ht0 htN M e he hp L hL d hd v =
      (closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp
        ⟨v.val, Eq.mpr (congrArg (fun b : X × I =>
          b ∈ U ×ˢ (univ : Set I)) v.property) hd⟩).2 := by
  have hfull : d ∈ U ×ˢ Icc (t 0) (t N) :=
    ⟨hd.1, by rw [ht0]; exact unitInterval.nonneg',
      by rw [htN]; exact unitInterval.le_one'⟩
  exact (closedSubdivisionFiberLinearEquiv_apply
    p U hN t ht M e he hp L hL d hfull v).trans
      (closedSubdivisionUnitIntervalHomeomorph_apply_snd_eq_subdivision
        p U hN t ht ht0 htN M e he hp
          ⟨v.val, Eq.mpr (congrArg (fun b : X × I =>
            b ∈ U ×ˢ (univ : Set I)) v.property) hd⟩).symm

/-- On the first closed slab, normalized linear coordinates remain those of the
first input chart. -/
theorem closedSubdivisionUnitIntervalFiberLinearEquiv_first (d : X × I)
    (hd : d ∈ U ×ˢ (univ : Set I)) (hfirst : d ∈ U ×ˢ Icc (t 0) (t 1)) :
    closedSubdivisionUnitIntervalFiberLinearEquiv p U hN t ht ht0 htN M e he hp L hL d hd =
      L ⟨0, hN⟩ d hfirst := by
  exact closedSubdivisionFiberLinearEquiv_first p U hN t ht M e he hp L hL d _ hfirst

/-- At time zero the normalized linear equivalence is the first chart's given
linear equivalence on the same projection fiber. -/
theorem closedSubdivisionUnitIntervalFiberLinearEquiv_bottom (u : U) :
    closedSubdivisionUnitIntervalFiberLinearEquiv p U hN t ht ht0 htN M e he hp L hL
      (u.val, (0 : I)) ⟨u.property, mem_univ _⟩ =
      L ⟨0, hN⟩ (u.val, (0 : I))
        ⟨u.property, by simpa only [ht0] using (le_rfl : (0 : I) ≤ 0),
          by rw [← ht0]; exact ht (Nat.zero_le 1)⟩ :=
  closedSubdivisionUnitIntervalFiberLinearEquiv_first
    p U hN t ht ht0 htN M e he hp L hL (u.val, (0 : I)) ⟨u.property, mem_univ _⟩
      ⟨u.property, by simpa only [ht0] using (le_rfl : (0 : I) ≤ 0),
        by rw [← ht0]; exact ht (Nat.zero_le 1)⟩

/-- The normalized chart on a projection fiber has its unchanged base and the
constructed linear coordinates. -/
theorem closedSubdivisionUnitIntervalHomeomorph_apply_fiber (d : X × I)
    (hd : d ∈ U ×ˢ (univ : Set I)) (v : {z : Z // p z = d}) :
    closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp
      ⟨v.val, Eq.mpr (congrArg (fun b : X × I =>
        b ∈ U ×ˢ (univ : Set I)) v.property) hd⟩ =
      ((⟨d.1, hd.1⟩, d.2),
        closedSubdivisionUnitIntervalFiberLinearEquiv
          p U hN t ht ht0 htN M e he hp L hL d hd v) := by
  apply Prod.ext
  · rw [closedSubdivisionUnitIntervalHomeomorph_proj]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst v.property
    · exact congrArg (fun q : X × I => q.2) v.property
  · exact (closedSubdivisionUnitIntervalFiberLinearEquiv_apply
      p U hN t ht ht0 htN M e he hp L hL d hd v).symm

/-- The normalized inverse and inverse linear coordinates agree as points of the
given total space at every time. -/
theorem closedSubdivisionUnitIntervalHomeomorph_symm_apply_fiber (d : X × I)
    (hd : d ∈ U ×ˢ (univ : Set I)) (w : M ⟨0, hN⟩) :
    ((closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp).symm
      ((⟨d.1, hd.1⟩, d.2), w)).val =
      ((closedSubdivisionUnitIntervalFiberLinearEquiv
        p U hN t ht ht0 htN M e he hp L hL d hd).symm w).val := by
  let H := closedSubdivisionUnitIntervalHomeomorph p U hN t ht ht0 htN M e he hp
  let v := (closedSubdivisionUnitIntervalFiberLinearEquiv
    p U hN t ht ht0 htN M e he hp L hL d hd).symm w
  let z : p ⁻¹' (U ×ˢ (univ : Set I)) :=
    ⟨v.val, Eq.mpr (congrArg (fun b : X × I =>
      b ∈ U ×ˢ (univ : Set I)) v.property) hd⟩
  have hf : H z = ((⟨d.1, hd.1⟩, d.2), w) := by
    have h := closedSubdivisionUnitIntervalHomeomorph_apply_fiber
      p U hN t ht ht0 htN M e he hp L hL d hd v
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hi := H.symm_apply_apply z
  rw [hf] at hi
  exact congrArg Subtype.val hi

end UnitInterval

/-- An ordinary open atlas with linear coordinates on the given projection fibers
gives a whole-cylinder chart near each spatial base point. The model may vary
across the atlas. The assembled chart preserves both base coordinates in both
directions, agrees with one original chart at the bottom in both directions,
and has matching linear equivalences on every original projection fiber.

This is the linear local cylinder construction in Hatcher, *Vector Bundles and
K-Theory*, Proposition 1.7, preliminary fact (1). -/
theorem exists_local_linear_cylinder_homeomorph_of_preimage_charts
    {X : Type uX} {Z : Type uZ} {J : Type uJ} {R : Type uR}
    [TopologicalSpace X] [TopologicalSpace Z] [Semiring R]
    (p : Z → X × I) (M : J → Type uM) [∀ j, TopologicalSpace (M j)]
    [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    [∀ b : X × I, AddCommMonoid {z : Z // p z = b}]
    [∀ b : X × I, Module R {z : Z // p z = b}]
    (W : J → Set (X × I))
    (e : ∀ j, (p ⁻¹' W j) ≃ₜ W j × M j)
    (L : ∀ (j : J) (b : X × I), b ∈ W j → {z : Z // p z = b} ≃ₗ[R] M j)
    (hp : Continuous p) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : X × I, ∃ j, b ∈ W j)
    (he : ∀ j z, (e j z).1.val = p z.val)
    (hL : ∀ j b (hb : b ∈ W j) (v : {z : Z // p z = b}),
      L j b hb v =
        (e j ⟨v.val, Eq.mpr (congrArg (fun b => b ∈ W j) v.property) hb⟩).2)
    (x : X) :
    ∃ (U : Set X) (j₀ : J)
      (hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀)
      (H : {z : Z // (p z).1 ∈ U} ≃ₜ (U × I) × M j₀)
      (K : ∀ (u : U) (t : I), {z : Z // p z = (u.val, t)} ≃ₗ[R] M j₀),
      IsOpen U ∧ x ∈ U ∧
      (∀ z, ((H z).1.1.val, (H z).1.2) = p z.val) ∧
      (∀ q : (U × I) × M j₀, p (H.symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ (u : U) (v : {z : Z // p z = (u.val, (0 : I))}),
        (H ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e j₀ ⟨v.val,
          Eq.mpr (congrArg (fun b => b ∈ W j₀) v.property) (hU₀ u)⟩).2) ∧
      (∀ (u : U) (v : M j₀),
        (H.symm ((u, (0 : I)), v)).val =
        ((e j₀).symm (⟨(u.val, (0 : I)), hU₀ u⟩, v)).val) ∧
      (∀ (u : U) (t : I) (v : {z : Z // p z = (u.val, t)}),
        K u t v =
          (H ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
      (∀ (u : U) (t : I) (v : M j₀),
        (H.symm ((u, t), v)).val = ((K u t).symm v).val) ∧
      (∀ u : U, K u (0 : I) = L j₀ (u.val, (0 : I)) (hU₀ u)) := by
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
  let LK : ∀ (k : Fin N) (d : X × I),
      d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1)) →
        {z : Z // p z = d} ≃ₗ[R] M (j k) :=
    fun k d hd => L (j k) d (hj k hd)
  have hLK : ∀ (k : Fin N) (d : X × I)
      (hd : d ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) (v : {z : Z // p z = d}),
      LK k d hd v = (E k ⟨v.val, Eq.mpr (congrArg (fun b : X × I =>
        b ∈ U ×ˢ Icc (t k.val) (t (k.val + 1))) v.property) hd⟩).2 := by
    intro k d hd v
    simpa only [LK, E, Homeomorph.restrictPreimageProd_apply] using
      (hL (j k) d (hj k hd) v)
  let Hraw := closedSubdivisionUnitIntervalHomeomorph
    p U hN t ht ht0 htN (fun k => M (j k)) E hE hp
  let S : {z : Z // (p z).1 ∈ U} ≃ₜ (p ⁻¹' (U ×ˢ (univ : Set I))) :=
    (Homeomorph.refl Z).subtype
      (fun z => ⟨fun hz => ⟨hz, mem_univ _⟩, fun hz => hz.1⟩)
  let H := S.trans Hraw
  let j₀ := j ⟨0, hN⟩
  let K : ∀ (u : U) (s : I), {z : Z // p z = (u.val, s)} ≃ₗ[R] M j₀ :=
    fun u s => closedSubdivisionUnitIntervalFiberLinearEquiv
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp LK hLK
        (u.val, s) ⟨u.property, mem_univ _⟩
  have hU₀ : ∀ u : U, (u.val, (0 : I)) ∈ W j₀ := by
    intro u
    apply hj ⟨0, hN⟩
    refine ⟨u.property, ?_, ?_⟩
    · simpa only [ht0] using (le_rfl : (0 : I) ≤ 0)
    · rw [← ht0]
      exact ht (Nat.zero_le 1)
  refine ⟨U, j₀, hU₀, H, K, hU, hxU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro u s v
    exact closedSubdivisionUnitIntervalFiberLinearEquiv_apply
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp LK hLK
        (u.val, s) ⟨u.property, mem_univ _⟩ v
  · intro u s v
    exact closedSubdivisionUnitIntervalHomeomorph_symm_apply_fiber
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp LK hLK
        (u.val, s) ⟨u.property, mem_univ _⟩ v
  · intro u
    exact closedSubdivisionUnitIntervalFiberLinearEquiv_bottom
      p U hN t ht ht0 htN (fun k => M (j k)) E hE hp LK hLK u

/-- Over a compact spatial base, an ordinary open atlas gives a finite ordered
cover by whole-cylinder charts. Both full-base laws and both original-chart
bottom laws are retained. -/
theorem exists_finite_cylinder_cover_of_preimage_charts
    {X : Type uX} {Z : Type uZ} {J : Type uJ}
    [TopologicalSpace X] [TopologicalSpace Z] [CompactSpace X]
    (p : Z → X × I) (M : J → Type uM) [∀ j, TopologicalSpace (M j)]
    (W : J → Set (X × I)) (e : ∀ j, (p ⁻¹' W j) ≃ₜ W j × M j)
    (hp : Continuous p) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : X × I, ∃ j, b ∈ W j)
    (he : ∀ j z, (e j z).1.val = p z.val) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, (0 : I)) ∈ W (j₀ k))
      (H : ∀ k, {z : Z // (p z).1 ∈ U k} ≃ₜ ((U k) × I) × M (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × I) × M (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : Z // p z = (u.val, (0 : I))}),
        (H k ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b => b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : M (j₀ k)),
        ((H k).symm ((u, (0 : I)), v)).val =
        ((e (j₀ k)).symm (⟨(u.val, (0 : I)), hU₀ k u⟩, v)).val) := by
  exact exists_finiteCylinderCover_of_local p M W e
    (exists_local_cylinder_homeomorph_of_preimage_charts p M W e hp hW hcover he)

/-- Over a compact spatial base, an ordinary open atlas with linear projection-
fiber coordinates gives a finite ordered whole-cylinder cover. Every chosen
chart retains both original-chart bottom laws, both full-base laws, forward and
inverse linear coordinates at every time, and the original bottom equivalence.
The scalar semiring may be noncommutative and has no topology assumptions. -/
theorem exists_finite_linear_cylinder_cover_of_preimage_charts
    {X : Type uX} {Z : Type uZ} {J : Type uJ} {R : Type uR}
    [TopologicalSpace X] [TopologicalSpace Z] [CompactSpace X] [Semiring R]
    (p : Z → X × I) (M : J → Type uM) [∀ j, TopologicalSpace (M j)]
    [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    [∀ b : X × I, AddCommMonoid {z : Z // p z = b}]
    [∀ b : X × I, Module R {z : Z // p z = b}]
    (W : J → Set (X × I)) (e : ∀ j, (p ⁻¹' W j) ≃ₜ W j × M j)
    (L : ∀ (j : J) (b : X × I), b ∈ W j → {z : Z // p z = b} ≃ₗ[R] M j)
    (hp : Continuous p) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : X × I, ∃ j, b ∈ W j)
    (he : ∀ j z, (e j z).1.val = p z.val)
    (hL : ∀ j b (hb : b ∈ W j) (v : {z : Z // p z = b}),
      L j b hb v =
        (e j ⟨v.val, Eq.mpr (congrArg (fun b => b ∈ W j) v.property) hb⟩).2) :
    ∃ (n : ℕ) (x₀ : Fin n → X) (U : Fin n → Set X)
      (j₀ : Fin n → J)
      (hU₀ : ∀ k (u : U k), (u.val, (0 : I)) ∈ W (j₀ k))
      (H : ∀ k, {z : Z // (p z).1 ∈ U k} ≃ₜ ((U k) × I) × M (j₀ k))
      (K : ∀ k (u : U k) (t : I),
        {z : Z // p z = (u.val, t)} ≃ₗ[R] M (j₀ k)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, x₀ k ∈ U k) ∧
      (⋃ k, U k) = univ ∧
      (∀ k z, ((H k z).1.1.val, (H k z).1.2) = p z.val) ∧
      (∀ k (q : ((U k) × I) × M (j₀ k)),
        p ((H k).symm q).val = (q.1.1.val, q.1.2)) ∧
      (∀ k (u : U k) (v : {z : Z // p z = (u.val, (0 : I))}),
        (H k ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2 =
        (e (j₀ k) ⟨v.val,
          Eq.mpr (congrArg (fun b => b ∈ W (j₀ k)) v.property) (hU₀ k u)⟩).2) ∧
      (∀ k (u : U k) (v : M (j₀ k)),
        ((H k).symm ((u, (0 : I)), v)).val =
        ((e (j₀ k)).symm (⟨(u.val, (0 : I)), hU₀ k u⟩, v)).val) ∧
      (∀ k (u : U k) (t : I) (v : {z : Z // p z = (u.val, t)}),
        K k u t v =
          (H k ⟨v.val, (congrArg Prod.fst v.property).symm ▸ u.property⟩).2) ∧
      (∀ k (u : U k) (t : I) (v : M (j₀ k)),
        ((H k).symm ((u, t), v)).val = ((K k u t).symm v).val) ∧
      (∀ k (u : U k), K k u (0 : I) =
        L (j₀ k) (u.val, (0 : I)) (hU₀ k u)) := by
  exact exists_finiteLinearCylinderCover_of_local p M W e L
    (exists_local_linear_cylinder_homeomorph_of_preimage_charts p M W e L hp hW hcover he hL)

end Bundle.Trivialization
