/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Supported weighted coordinates

Given modules `F x`, model modules `G i`, and linear equivalences from `G i` to `F x`
where `x ∈ U i`, `LinearMap.weightedCoordinates` multiplies the inverse coordinates
by a scalar weight and sets coordinates outside the chart to zero. Its target is
the full dependent product of the given models. Neither the index type nor any
module is required to be finite or nontrivial.

The membership, nonmembership, zero-weight, and chart-evaluation rules describe the
map without unfolding its definition. Two images are equal exactly when every valid
weight acts equally on the original fibre vectors. Preservation of zero, addition,
and scalar multiplication uses the usual linear-map API. If the valid weights
generate the unit ideal, the map admits a linear left inverse and hence is injective.
An injective scalar action at one valid coordinate also suffices for injectivity;
the weight need not be a unit. Mere nonzeroness of a weight would not suffice over a
general commutative semiring.

## Implementation notes

The construction uses `LinearMap.pi` and scalar multiplication on linear maps. The
fibre modules, their operations, and the chart equivalences are given data. No
replacement fibres, topologies, atlas, or weights are constructed here.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2: motivation for the finite
  weighted local-coordinate construction.
-/

@[expose] public section

universe uK uX uI uF uG

namespace LinearMap

variable {K : Type uK} [CommSemiring K]
  {X : Type uX} {I : Type uI} {F : X → Type uF} {G : I → Type uG}
  [∀ x, AddCommMonoid (F x)] [∀ x, Module K (F x)]
  [∀ i, AddCommMonoid (G i)] [∀ i, Module K (G i)]

variable (U : I → Set X) (w : I → X → K)
  (c : ∀ (i : I) (x : X), x ∈ U i → G i ≃ₗ[K] F x)

/-- The linear map into all model coordinates, weighted on each chart and zero off it. -/
noncomputable def weightedCoordinates (x : X) : F x →ₗ[K] ∀ i, G i := by
  classical
  exact LinearMap.pi fun i ↦
    if hx : x ∈ U i then w i x • (c i x hx).symm.toLinearMap else 0

/-- On a chart, the coordinate is its weighted inverse linear equivalence. -/
@[simp]
theorem weightedCoordinates_apply_of_mem {x : X} {i : I} (hx : x ∈ U i) (v : F x) :
    weightedCoordinates U w c x v i = w i x • (c i x hx).symm v := by
  classical
  simp [weightedCoordinates, hx]

/-- Outside a chart, its coordinate vanishes. -/
@[simp]
theorem weightedCoordinates_apply_of_notMem {x : X} {i : I} (hx : x ∉ U i) (v : F x) :
    weightedCoordinates U w c x v i = 0 := by
  classical
  simp [weightedCoordinates, hx]

/-- A zero weight makes its coordinate vanish, whether or not the chart is defined. -/
@[simp]
theorem weightedCoordinates_apply_of_eq_zero {x : X} {i : I}
    (hw : w i x = 0) (v : F x) : weightedCoordinates U w c x v i = 0 := by
  classical
  by_cases hx : x ∈ U i
  · rw [weightedCoordinates_apply_of_mem U w c hx v, hw, zero_smul]
  · exact weightedCoordinates_apply_of_notMem U w c hx v

/-- Coordinates of a vector supplied by another chart use the same exact chart inverses. -/
theorem weightedCoordinates_apply_chart {x : X} {i j : I}
    (hi : x ∈ U i) (hj : x ∈ U j) (v : G j) :
    weightedCoordinates U w c x (c j x hj v) i =
      w i x • (c i x hi).symm (c j x hj v) :=
  weightedCoordinates_apply_of_mem U w c hi _

/-- On the chart that supplies the vector, its coordinate is scalar multiplication
by the weight. -/
theorem weightedCoordinates_apply_chart_self {x : X} {i : I}
    (hx : x ∈ U i) (v : G i) :
    weightedCoordinates U w c x (c i x hx v) i = w i x • v := by
  rw [weightedCoordinates_apply_of_mem U w c hx, (c i x hx).symm_apply_apply]

/-- Two vectors have the same weighted coordinates exactly when every valid weight
acts equally on them in the given fibre. -/
theorem weightedCoordinates_apply_eq_apply_iff {x : X} (v v' : F x) :
    weightedCoordinates U w c x v = weightedCoordinates U w c x v' ↔
      ∀ i, x ∈ U i → w i x • v = w i x • v' := by
  classical
  constructor
  · intro h i hi
    have hiw : w i x • (c i x hi).symm v =
        w i x • (c i x hi).symm v' := by
      simpa only [weightedCoordinates_apply_of_mem U w c hi] using
        congrArg (fun f : ∀ j, G j ↦ f i) h
    simpa using congrArg (c i x hi) hiw
  · intro h
    funext i
    by_cases hi : x ∈ U i
    · have hiw : w i x • (c i x hi).symm v =
          w i x • (c i x hi).symm v' := by
        simpa using congrArg (c i x hi).symm (h i hi)
      simpa only [weightedCoordinates_apply_of_mem U w c hi] using hiw
    · simp only [weightedCoordinates_apply_of_notMem U w c hi]

/-- An injective scalar action at one valid coordinate suffices for injectivity.
The scalar need not be a unit. -/
theorem weightedCoordinates_injective_of_smul_injective {x : X} {i : I}
    (hx : x ∈ U i) (hw : Function.Injective (fun v : F x ↦ w i x • v)) :
    Function.Injective (weightedCoordinates U w c x) := by
  intro v v' h
  exact hw ((weightedCoordinates_apply_eq_apply_iff U w c v v').mp h i hx)

/-- If the weights of the valid charts generate the unit ideal, there is a linear
reconstruction from the full product of model coordinates that is a left inverse of
the weighted coordinate map. -/
theorem weightedCoordinates_exists_leftInverse_of_span_eq_top {x : X}
    (hspan : Ideal.span ((fun i : I => w i x) '' {i : I | x ∈ U i}) = ⊤) :
    ∃ ρ : (∀ i, G i) →ₗ[K] F x,
      ρ.comp (weightedCoordinates U w c x) = LinearMap.id := by
  -- The scalars admitting reconstruction form an ideal, even without subtraction.
  let J : Ideal K :=
    { carrier := {r | ∃ ρ : (∀ i, G i) →ₗ[K] F x,
          ρ.comp (weightedCoordinates U w c x) = r • LinearMap.id}
      zero_mem' := by
        refine ⟨0, ?_⟩
        ext v
        simp
      add_mem' := by
        rintro r s ⟨ρ, hρ⟩ ⟨σ, hσ⟩
        refine ⟨ρ + σ, ?_⟩
        ext v
        change ρ (weightedCoordinates U w c x v) +
            σ (weightedCoordinates U w c x v) = (r + s) • v
        calc
          _ = r • v + s • v :=
            congrArg₂ (fun a b : F x ↦ a + b)
              (congrArg (fun f : F x →ₗ[K] F x ↦ f v) hρ)
              (congrArg (fun f : F x →ₗ[K] F x ↦ f v) hσ)
          _ = _ := (add_smul r s v).symm
      smul_mem' := by
        rintro t r ⟨ρ, hρ⟩
        refine ⟨t • ρ, ?_⟩
        ext v
        change t • ρ (weightedCoordinates U w c x v) = (t * r) • v
        calc
          _ = t • (r • v) :=
            congrArg (fun y : F x ↦ t • y)
              (congrArg (fun f : F x →ₗ[K] F x ↦ f v) hρ)
          _ = _ := (mul_smul t r v).symm }
  have hgenerators : ((fun i : I => w i x) '' {i : I | x ∈ U i}) ⊆ J := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨(c i x hi).toLinearMap.comp (LinearMap.proj i), ?_⟩
    ext v
    change c i x hi (weightedCoordinates U w c x v i) = w i x • v
    rw [weightedCoordinates_apply_of_mem U w c hi]
    simp
  have hspanJ : Ideal.span ((fun i : I => w i x) '' {i : I | x ∈ U i}) ≤ J :=
    Ideal.span_le.mpr hgenerators
  have hone : (1 : K) ∈ J := by
    rw [hspan] at hspanJ
    exact hspanJ (by simp)
  obtain ⟨ρ, hρ⟩ := hone
  exact ⟨ρ, by simpa using hρ⟩

/-- If the weights of the valid charts generate the unit ideal, the weighted coordinate
map is injective. No individual weight needs to be a unit. -/
theorem weightedCoordinates_injective_of_span_eq_top {x : X}
    (hspan : Ideal.span ((fun i : I => w i x) '' {i : I | x ∈ U i}) = ⊤) :
    Function.Injective (weightedCoordinates U w c x) := by
  obtain ⟨ρ, hρ⟩ := weightedCoordinates_exists_leftInverse_of_span_eq_top U w c hspan
  have hleft : Function.LeftInverse ρ (weightedCoordinates U w c x) := by
    intro v
    exact congrArg (fun f : F x →ₗ[K] F x ↦ f v) hρ
  exact hleft.injective

/-- One chart coordinate with a unit weight suffices for injectivity.

No nontriviality or field assumption is needed: unit scalar cancellation works for the
same given module action, followed by injectivity of the exact inverse chart.
-/
theorem weightedCoordinates_injective_of_isUnit {x : X} {i : I}
    (hx : x ∈ U i) (hw : IsUnit (w i x)) :
    Function.Injective (weightedCoordinates U w c x) := by
  apply weightedCoordinates_injective_of_span_eq_top U w c
  apply top_unique
  calc
    ⊤ = Ideal.span {w i x} := (Ideal.span_singleton_eq_top.mpr hw).symm
    _ ≤ Ideal.span ((fun j : I => w j x) '' {j : I | x ∈ U j}) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨i, hx, rfl⟩)

open scoped BigOperators

/-- Reconstruct a fibre vector from finitely many valid chart coordinates and coefficients.

The map is defined on the full product of models and ignores coordinates outside `s`.
It does not depend on the weights used by `weightedCoordinates`.
-/
noncomputable def finiteChartReconstruction (x : X) (s : Finset I)
    (a : I → K) (hvalid : ∀ i ∈ s, x ∈ U i) : (∀ i, G i) →ₗ[K] F x := by
  classical
  exact ∑ i ∈ s.attach,
    a i • (c i x (hvalid i i.property)).toLinearMap.comp (LinearMap.proj (i : I))

/-- Finite chart reconstruction is the sum of the prescribed chart values, with each
chart evaluated using the membership proof supplied by `hvalid`. -/
@[simp]
theorem finiteChartReconstruction_apply (x : X) (s : Finset I)
    (a : I → K) (hvalid : ∀ i ∈ s, x ∈ U i) (z : ∀ i, G i) :
    finiteChartReconstruction U c x s a hvalid z =
      ∑ i ∈ s.attach, a i • c i x (hvalid i i.property) (z i) := by
  classical
  simp [finiteChartReconstruction]

/-- Reconstructing weighted coordinates multiplies a vector by the finite sum of
coefficient-weight products over the chosen valid charts. -/
theorem finiteChartReconstruction_comp_weightedCoordinates (x : X) (s : Finset I)
    (a : I → K) (hvalid : ∀ i ∈ s, x ∈ U i) :
    (finiteChartReconstruction U c x s a hvalid).comp (weightedCoordinates U w c x) =
      (∑ i ∈ s, a i * w i x) • LinearMap.id := by
  classical
  ext v
  simp only [LinearMap.comp_apply, finiteChartReconstruction_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  calc
    _ = ∑ i ∈ s.attach, (a i * w i x) • v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedCoordinates_apply_of_mem U w c (hvalid i i.property),
        (c i x (hvalid i i.property)).map_smul,
        (c i x (hvalid i i.property)).apply_symm_apply, smul_smul]
    _ = _ := by
      rw [Finset.sum_attach (s := s) (f := fun i : I => (a i * w i x) • v)]
      exact (map_sum (LinearMap.toSpanSingleton K (F x) v)
        (fun i : I => a i * w i x) s).symm

/-- Coefficients whose weighted sum is one give a linear left inverse to the
weighted-coordinate map. -/
theorem finiteChartReconstruction_comp_weightedCoordinates_of_sum_eq_one
    (x : X) (s : Finset I) (a : I → K) (hvalid : ∀ i ∈ s, x ∈ U i)
    (hsum : ∑ i ∈ s, a i * w i x = 1) :
    (finiteChartReconstruction U c x s a hvalid).comp (weightedCoordinates U w c x) =
      LinearMap.id := by
  rw [finiteChartReconstruction_comp_weightedCoordinates U w c x s a hvalid,
    hsum, one_smul]

end LinearMap
