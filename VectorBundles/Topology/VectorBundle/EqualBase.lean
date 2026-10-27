/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Equal-base sums

`Bundle.EqualBaseSum` is the space of pairs in two total spaces with the same
base point. Its topology is the subtype topology of the product of the given
total-space topologies. No topology on either total space is reconstructed.

`Bundle.EqualBaseTrivialization` combines a global homeomorphism with compatible
linear equivalences on the fibres. Base preservation and the inverse formula
follow from this compatibility; they are not additional fields.
-/

@[expose] public section

universe uK uX uP uE uQ uH uY

namespace Bundle

/-- Pairs of total-space points with the same base point. -/
abbrev EqualBaseSum {X : Type uX}
    (P : Type uP) (E : X → Type uE) (Q : Type uQ) (H : X → Type uH) :=
  {z : TotalSpace P E × TotalSpace Q H // z.1.proj = z.2.proj}

namespace EqualBaseSum

variable {X : Type uX} {P : Type uP} {E : X → Type uE}
variable {Q : Type uQ} {H : X → Type uH}

/-- A pair of vectors in one fibre. -/
def mk (x : X) (v : E x) (w : H x) : EqualBaseSum P E Q H :=
  ⟨(TotalSpace.mk x v, TotalSpace.mk x w), rfl⟩

/-- The first total-space component. -/
def fst (z : EqualBaseSum P E Q H) : TotalSpace P E := z.1.1

/-- The second total-space component. -/
def snd (z : EqualBaseSum P E Q H) : TotalSpace Q H := z.1.2

/-- The common base point. -/
def proj (z : EqualBaseSum P E Q H) : X := z.fst.proj

@[simp] theorem fst_mk (x : X) (v : E x) (w : H x) :
    (mk (P := P) (Q := Q) x v w).fst = TotalSpace.mk x v := rfl

@[simp] theorem snd_mk (x : X) (v : E x) (w : H x) :
    (mk (P := P) (Q := Q) x v w).snd = TotalSpace.mk x w := rfl

@[simp] theorem proj_mk (x : X) (v : E x) (w : H x) :
    (mk (P := P) (Q := Q) x v w).proj = x := rfl

@[simp] theorem proj_snd (z : EqualBaseSum P E Q H) :
    z.snd.proj = z.proj := z.2.symm

/-- The two total-space components determine an equal-base pair. -/
@[ext] theorem ext {z w : EqualBaseSum P E Q H}
    (hf : z.fst = w.fst) (hs : z.snd = w.snd) : z = w :=
  Subtype.ext (Prod.ext hf hs)

/-- Every equal-base pair has a diagonal representation, after transporting
along its base equality. -/
theorem exists_mk (z : EqualBaseSum P E Q H) :
    ∃ (x : X) (v : E x) (w : H x), mk x v w = z := by
  rcases z with ⟨⟨⟨x, v⟩, ⟨y, w⟩⟩, h⟩
  change x = y at h
  cases h
  exact ⟨x, v, w, rfl⟩

/-- Pair two maps whose base points agree. -/
def lift {Y : Type uY} (f : Y → TotalSpace P E) (g : Y → TotalSpace Q H)
    (h : ∀ y, (f y).proj = (g y).proj) (y : Y) : EqualBaseSum P E Q H :=
  ⟨(f y, g y), h y⟩

@[simp] theorem fst_lift {Y : Type uY} (f : Y → TotalSpace P E)
    (g : Y → TotalSpace Q H) (h : ∀ y, (f y).proj = (g y).proj) (y : Y) :
    (lift f g h y).fst = f y := rfl

@[simp] theorem snd_lift {Y : Type uY} (f : Y → TotalSpace P E)
    (g : Y → TotalSpace Q H) (h : ∀ y, (f y).proj = (g y).proj) (y : Y) :
    (lift f g h y).snd = g y := rfl

section Topology

variable [TopologicalSpace (TotalSpace P E)] [TopologicalSpace (TotalSpace Q H)]
variable {Y : Type uY} [TopologicalSpace Y]

/-- The first total-space component is continuous. -/
@[fun_prop] theorem continuous_fst :
    Continuous (fst : EqualBaseSum P E Q H → TotalSpace P E) :=
  _root_.continuous_fst.comp continuous_subtype_val

/-- The second total-space component is continuous. -/
@[fun_prop] theorem continuous_snd :
    Continuous (snd : EqualBaseSum P E Q H → TotalSpace Q H) :=
  _root_.continuous_snd.comp continuous_subtype_val

/-- Continuity into the equal-base subtype is continuity of its two total-space
components, for the product-then-subtype topology. -/
theorem continuous_iff (f : Y → EqualBaseSum P E Q H) :
    Continuous f ↔ Continuous (fun y => (f y).fst) ∧
      Continuous (fun y => (f y).snd) := by
  constructor
  · intro h
    exact ⟨continuous_fst.comp h,
      continuous_snd.comp h⟩
  · rintro ⟨hf, hg⟩
    exact (hf.prodMk hg).subtype_mk (fun y => (f y).2)

/-- The canonical pairing is continuous exactly when both maps are continuous. -/
theorem continuous_lift_iff (f : Y → TotalSpace P E) (g : Y → TotalSpace Q H)
    (h : ∀ y, (f y).proj = (g y).proj) :
    Continuous (lift f g h) ↔ Continuous f ∧ Continuous g :=
  continuous_iff (lift f g h)

end Topology
end EqualBaseSum

/-- A jointly bicontinuous trivialization compatible with fibre linear equivalences.
No continuity of scalar or fibre operations is required. -/
structure EqualBaseTrivialization
    (K : Type uK) [Semiring K] [TopologicalSpace K]
    {X : Type uX} [TopologicalSpace X]
    (P : Type uP) (E : X → Type uE) (Q : Type uQ) (H : X → Type uH)
    [∀ x, AddCommMonoid (E x)] [∀ x, Module K (E x)]
    [∀ x, AddCommMonoid (H x)] [∀ x, Module K (H x)]
    [TopologicalSpace (TotalSpace P E)] [TopologicalSpace (TotalSpace Q H)]
    (N : ℕ) where
  /-- A global homeomorphism for the given total-space topologies. -/
  toHomeomorph : EqualBaseSum P E Q H ≃ₜ (X × (Fin N → K))
  /-- Linear coordinates on each pair of fibres. -/
  linearEquiv : ∀ x, (E x × H x) ≃ₗ[K] (Fin N → K)
  /-- The homeomorphism agrees with the fibre coordinates. -/
  apply_mk : ∀ (x : X) (v : E x) (w : H x),
    toHomeomorph (EqualBaseSum.mk x v w) = (x, linearEquiv x (v, w))

attribute [simp] EqualBaseTrivialization.apply_mk

namespace EqualBaseTrivialization

variable {K : Type uK} [Semiring K] [TopologicalSpace K]
variable {X : Type uX} [TopologicalSpace X]
variable {P : Type uP} {E : X → Type uE} {Q : Type uQ} {H : X → Type uH}
variable [∀ x, AddCommMonoid (E x)] [∀ x, Module K (E x)]
variable [∀ x, AddCommMonoid (H x)] [∀ x, Module K (H x)]
variable [TopologicalSpace (TotalSpace P E)] [TopologicalSpace (TotalSpace Q H)]
variable {N : ℕ} (T : EqualBaseTrivialization K P E Q H N)

/-- Compatibility on diagonal representatives forces preservation of the base. -/
@[simp] theorem proj_apply (z : EqualBaseSum P E Q H) :
    (T.toHomeomorph z).1 = z.proj := by
  obtain ⟨x, v, w, rfl⟩ := EqualBaseSum.exists_mk z
  exact congrArg Prod.fst (T.apply_mk x v w)

/-- The global inverse is given by the inverse fibre linear equivalence. -/
@[simp] theorem symm_apply (x : X) (a : Fin N → K) :
    T.toHomeomorph.symm (x, a) =
      EqualBaseSum.mk x ((T.linearEquiv x).symm a).1
        ((T.linearEquiv x).symm a).2 := by
  apply T.toHomeomorph.injective
  rw [T.toHomeomorph.apply_symm_apply, T.apply_mk]
  exact congrArg (fun b => (x, b)) ((T.linearEquiv x).apply_symm_apply a).symm

/-- The inverse homeomorphism preserves the specified base point. -/
@[simp] theorem proj_symm_apply (p : X × (Fin N → K)) :
    (T.toHomeomorph.symm p).proj = p.1 :=
  (T.proj_apply (T.toHomeomorph.symm p)).symm.trans
    (congrArg Prod.fst (T.toHomeomorph.apply_symm_apply p))

/-- A trivialization is determined by its global homeomorphism. -/
@[ext] theorem ext {S T : EqualBaseTrivialization K P E Q H N}
    (h : S.toHomeomorph = T.toHomeomorph) : S = T := by
  rcases S with ⟨s, sl, hs⟩
  rcases T with ⟨t, tl, ht⟩
  change s = t at h
  subst t
  have hl : sl = tl := by
    funext x
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.snd ((hs x v.1 v.2).symm.trans (ht x v.1 v.2))
  subst tl
  rfl

end EqualBaseTrivialization
end Bundle
