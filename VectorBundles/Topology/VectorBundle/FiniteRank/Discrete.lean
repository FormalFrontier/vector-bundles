/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.FiniteRank

/-!
# Discrete families of finite-dimensional vector spaces

For a discrete base and an arbitrary function assigning a finite rank to each base
point, the disjoint union of the standard vector spaces has a finite-rank atlas.
The total-space topology is the final topology of the canonical fibre injections,
declared once for this family.

Constant ranks include trivial bundles and zero bundles. A two-point base with ranks
zero and one gives a bundle that cannot have a single dimension for all its fibres.
-/

@[expose] public section

open Bundle Topology

universe uK uB

namespace Bundle.DiscreteFiniteRank

variable (K : Type uK) {B : Type uB} (rank : B → ℕ)

/-- The standard coordinate fibre at a point with the prescribed rank, with the canonical
function-space algebraic structures and topology when these are available. -/
abbrev Fiber (b : B) : Type uK := Fin (rank b) → K

private theorem mk_injective (b : B) :
    Function.Injective (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) := by
  intro v w h
  cases h
  rfl

private theorem preimage_image_mk (b : B) (s : Set (Fiber K rank b)) :
    (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) ⁻¹'
      ((TotalSpace.mk b) '' s) = s := by
  ext v
  constructor
  · rintro ⟨w, hw, h⟩
    have hwv := mk_injective K rank b h
    simpa only [hwv] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem preimage_image_mk_of_ne (b c : B) (hc : c ≠ b)
    (s : Set (Fiber K rank b)) :
    (TotalSpace.mk c : Fiber K rank c → TotalSpace Unit (Fiber K rank)) ⁻¹'
      ((TotalSpace.mk b) '' s) = ∅ := by
  ext v
  constructor
  · rintro ⟨w, _, h⟩
    exact False.elim (hc (congrArg TotalSpace.proj h).symm)
  · intro hv
    exact False.elim hv

/-- Turn standard coordinates into a point of the fibre over `b`. The base component
of the coordinate pair is ignored outside the singleton chart target. -/
def fromCoordinates (b : B) (q : B × (Fin (rank b) → K)) :
    TotalSpace Unit (Fiber K rank) :=
  TotalSpace.mk b q.2

/-- A coordinate vector gives the corresponding point of the specified fibre. -/
@[simp] theorem fromCoordinates_pair (b c : B) (v : Fiber K rank b) :
    fromCoordinates K rank b (c, v) = TotalSpace.mk b v := rfl

section Topology

variable [TopologicalSpace K]

/-- The total-space topology is the final topology of the canonical fibre injections. -/
instance : TopologicalSpace (TotalSpace Unit (Fiber K rank)) :=
  ⨆ b : B, TopologicalSpace.coinduced
    (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) inferInstance

/-- A set in the total space is open exactly when its preimage in each fibre is open. -/
theorem isOpen_total_iff (s : Set (TotalSpace Unit (Fiber K rank))) :
    IsOpen s ↔ ∀ b : B, IsOpen ((TotalSpace.mk b : Fiber K rank b → _) ⁻¹' s) :=
  isOpen_iSup_iff

/-- A map out of the total space is continuous exactly when its restriction to every
standard fibre is continuous. -/
theorem continuous_iff_on_fibres {Y : Type*} [TopologicalSpace Y]
    (f : TotalSpace Unit (Fiber K rank) → Y) :
    Continuous f ↔ ∀ b : B, Continuous (fun v : Fiber K rank b => f (TotalSpace.mk b v)) := by
  constructor
  · intro h b
    rw [continuous_def] at h ⊢
    intro s hs
    exact (isOpen_total_iff K rank (f ⁻¹' s)).mp (h s hs) b
  · intro h
    rw [continuous_def]
    intro s hs
    apply (isOpen_total_iff K rank (f ⁻¹' s)).mpr
    intro b
    exact (h b).isOpen_preimage s hs

private theorem isOpen_image_mk (b : B) (s : Set (Fiber K rank b)) (hs : IsOpen s) :
    IsOpen ((TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) '' s) := by
  classical
  apply (isOpen_total_iff K rank _).mpr
  intro c
  by_cases hc : c = b
  · subst c
    simpa only [preimage_image_mk] using hs
  · rw [preimage_image_mk_of_ne K rank b c hc]
    exact isOpen_empty

/-- Every canonical fibre injection is continuous for the final total-space topology. -/
theorem continuous_mk (b : B) :
    Continuous (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) := by
  rw [continuous_def]
  intro s hs
  exact (isOpen_total_iff K rank s).mp hs b

/-- The given topology on each standard fibre is its induced total-space topology. -/
theorem inducing_mk (b : B) :
    IsInducing (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) := by
  have hind :
      TopologicalSpace.induced
        (TotalSpace.mk b : Fiber K rank b → TotalSpace Unit (Fiber K rank)) inferInstance =
        (inferInstance : TopologicalSpace (Fiber K rank b)) := by
    apply TopologicalSpace.ext
    funext s
    apply propext
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (isOpen_total_iff K rank u).mp hu b
    · intro hs
      exact ⟨(TotalSpace.mk b) '' s, isOpen_image_mk K rank b s hs,
        preimage_image_mk K rank b s⟩
  first
  | exact ⟨hind⟩
  | exact ⟨hind.symm⟩

variable [TopologicalSpace B]

/-- The projection of the disjoint union of standard fibres is continuous. -/
theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit (Fiber K rank) → B) := by
  apply (continuous_iff_on_fibres K rank _).mpr
  intro c
  exact continuous_const

/-- Inserting a coordinate vector into the specified fibre is continuous. -/
theorem continuous_fromCoordinates (b : B) : Continuous (fromCoordinates K rank b) :=
  (continuous_mk K rank b).comp continuous_snd

end Topology

section Coordinates

variable [Zero K]

/-- Standard coordinates for the singleton chart at `b`. On the fibre over `b` these
are the original vector; on every other fibre they are the zero vector. -/
noncomputable def toCoordinates (b : B)
    (p : TotalSpace Unit (Fiber K rank)) : B × (Fin (rank b) → K) := by
  classical
  exact (b, if h : p.proj = b then h ▸ p.2 else 0)

/-- Coordinates on the fibre indexing the singleton chart are the original vector. -/
@[simp] theorem toCoordinates_mk (b : B) (v : Fiber K rank b) :
    toCoordinates K rank b (TotalSpace.mk b v) = (b, v) := by
  classical
  simp [toCoordinates]

private theorem coordinates_left_inv (b : B) (p : TotalSpace Unit (Fiber K rank))
    (hp : p.proj = b) :
    fromCoordinates K rank b (toCoordinates K rank b p) = p := by
  rcases p with ⟨c, v⟩
  change c = b at hp
  subst c
  rw [toCoordinates_mk, fromCoordinates_pair]

private theorem coordinates_right_inv (b : B) (q : B × (Fin (rank b) → K))
    (hq : q.1 = b) :
    toCoordinates K rank b (fromCoordinates K rank b q) = q := by
  rcases q with ⟨c, v⟩
  change c = b at hq
  subst c
  rw [fromCoordinates_pair, toCoordinates_mk]

section Topology

variable [TopologicalSpace K] [TopologicalSpace B]

/-- Singleton-chart coordinates are continuous on the final total space. -/
theorem continuous_toCoordinates (b : B) : Continuous (toCoordinates K rank b) := by
  classical
  apply (continuous_iff_on_fibres K rank _).mpr
  intro c
  by_cases h : c = b
  · subst c
    have hfun :
        (fun v : Fiber K rank b => toCoordinates K rank b (TotalSpace.mk b v)) =
          (fun v => (b, v)) :=
      funext (toCoordinates_mk K rank b)
    rw [hfun]
    exact continuous_const.prodMk continuous_id
  · simpa only [toCoordinates, dite_eq_right h] using
      (continuous_const :
        Continuous (fun _ : Fiber K rank c => (b, (0 : Fin (rank b) → K))))

variable [DiscreteTopology B]

/-- The chart at a base point has the singleton base set and the prescribed model. -/
noncomputable def chart (b : B) :
    Trivialization (Fin (rank b) → K)
      (TotalSpace.proj : TotalSpace Unit (Fiber K rank) → B) where
  toFun := toCoordinates K rank b
  invFun := fromCoordinates K rank b
  source := TotalSpace.proj ⁻¹' {b}
  target := {b} ×ˢ Set.univ
  map_source' := by
    intro p hp
    exact ⟨rfl, Set.mem_univ _⟩
  map_target' := by
    intro q hq
    rfl
  left_inv' := by
    intro p hp
    exact coordinates_left_inv K rank b p hp
  right_inv' := by
    intro q hq
    exact coordinates_right_inv K rank b q hq.1
  open_source := (isOpen_discrete {b}).preimage (continuous_proj K rank)
  open_target := (isOpen_discrete {b}).prod isOpen_univ
  continuousOn_toFun := (continuous_toCoordinates K rank b).continuousOn
  continuousOn_invFun := (continuous_fromCoordinates K rank b).continuousOn
  baseSet := {b}
  open_baseSet := isOpen_discrete {b}
  source_eq := rfl
  target_eq := rfl
  proj_toFun p hp := hp.symm

/-- The singleton chart has precisely its indexing point as base set. -/
@[simp] theorem chart_baseSet (b : B) : (chart K rank b).baseSet = {b} := rfl

/-- On its fibre, the singleton chart is the identity in standard coordinates. -/
@[simp] theorem chart_mk (b : B) (v : Fiber K rank b) :
    chart K rank b (TotalSpace.mk b v) = (b, v) := toCoordinates_mk K rank b v

end Topology
end Coordinates

section Atlas

variable [Field K] [TopologicalSpace K] [TopologicalSpace B] [DiscreteTopology B]

/-- Every singleton chart is fibrewise linear on its base set. -/
theorem chart_isFiberwiseLinear (b : B) :
    (chart K rank b).IsFiberwiseLinear (K := K) := by
  constructor
  · intro c hc v w
    have hcb : c = b := by simpa using hc
    subst c
    simp only [chart_mk]
  · intro c hc a v
    have hcb : c = b := by simpa using hc
    subst c
    simp only [chart_mk]

/-- The atlas of singleton charts for an arbitrary finite-rank function on a discrete base. -/
noncomputable def atlas : FiniteRankAtlas K Unit (Fiber K rank) where
  Index := B
  rank := rank
  chart := chart K rank
  linear := chart_isFiberwiseLinear K rank
  cover b := ⟨b, by simp⟩
  inducing := inducing_mk K rank

/-- The rank of the chart at a point is the prescribed rank. -/
@[simp] theorem atlas_rank (b : B) : (atlas K rank).rank b = rank b := rfl

/-- A discrete trivial bundle of any finite rank. Rank zero is included. -/
noncomputable def trivial (n : ℕ) :
    FiniteRankAtlas K Unit (Fiber K (fun _ : B => n)) := atlas K (fun _ : B => n)

end Atlas

/-- A base space with two points. -/
inductive TwoPoint
  | left
  | right
  deriving DecidableEq

instance : TopologicalSpace TwoPoint := ⊥

instance : DiscreteTopology TwoPoint := ⟨rfl⟩

/-- The rank function on the two-point base, with a zero-dimensional and a
one-dimensional fibre. -/
def twoPointRank : TwoPoint → ℕ
  | .left => 0
  | .right => 1

/-- The zero-dimensional fibre of the two-point bundle has exactly one element. -/
instance : Subsingleton (Fiber K twoPointRank .left) :=
  inferInstanceAs (Subsingleton (Fin 0 → K))

section TwoPoint

variable [Field K]

/-- A bundle over two points with different fibre dimensions. -/
noncomputable def twoPoint [TopologicalSpace K] :
    FiniteRankAtlas K Unit (Fiber K twoPointRank) := atlas K twoPointRank

/-- The positive-dimensional fibre of the two-point bundle has distinct zero and one. -/
theorem twoPoint_zero_ne_one :
    (0 : Fiber K twoPointRank .right) ≠ (fun _ => 1) := by
  intro h
  have h01 : (0 : K) = 1 := congrFun h (⟨0, Nat.zero_lt_succ 0⟩ : Fin (twoPointRank .right))
  exact zero_ne_one h01

/-- The two fibres cannot both be linearly equivalent to one common vector space. -/
theorem twoPoint_no_common_model (V : Type*) [AddCommGroup V] [Module K V] :
    ¬ (Nonempty (Fiber K twoPointRank .left ≃ₗ[K] V) ∧
      Nonempty (Fiber K twoPointRank .right ≃ₗ[K] V)) := by
  rintro ⟨⟨e₀⟩, ⟨e₁⟩⟩
  have hsub : Subsingleton (Fiber K twoPointRank .right) :=
    ⟨fun v w => e₁.injective (e₀.symm.injective (Subsingleton.elim _ _))⟩
  exact twoPoint_zero_ne_one K (hsub.elim _ _)

end TwoPoint
end Bundle.DiscreteFiniteRank
