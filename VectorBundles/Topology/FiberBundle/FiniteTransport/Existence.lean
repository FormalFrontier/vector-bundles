/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.ContinuousMap.FiniteWeights
public import VectorBundles.Topology.FiberBundle.FiniteTransport
public import VectorBundles.Topology.FiberBundle.FiniteTransport.Projection

/-!
# Cylinder transport from finite open covers

A finite open cover of a normal space, with a chart covering each whole open
cylinder, gives transport from the standard pullback of the entire zero-time
restriction to the original total space. No subordinate weights are required as
input: `ContinuousMap.exists_finite_weights` supplies them, and supported chart
steps assemble the transport in increasing index order.

The family theorem uses the iterated standard pullback of a family. For a given
projection `p : T → X × I`, the source instead uses the standard product and
subspace topologies of the full original zero slice. The topology on `T` is
unchanged. Both directions preserve the whole cylinder base point and fix every
bottom point, including points in the closed supports of the selected weights.

`Bundle.Trivialization.exists_finiteCylinderTransportOfProjection` also gives
linearity on the original projection fibers over any semiring, using the given
modules and matching linear chart coordinates. Chart models may vary with the
index, independently of the original total space and the scalar type. No scalar
topology or continuity of module operations is required: real weights change
time only. The same selected weights specify the independently ordered endpoint
transport with which the top restriction agrees.

## Limitations

The finite cylinder-chart cover is given. No independence of the selected
weights or the chart order, or homotopy invariance for arbitrary bundles, is
asserted.

## References

- The subordinate weights use finite normal shrinking and Urysohn's lemma via
  `ContinuousMap.exists_finite_weights`, reusing Mathlib's formalization.
- The ordered chart transport is supplied by
  `Bundle.Trivialization.finiteCylinderTransport` and
  `Bundle.Trivialization.finiteCylinderTransportOfProjection`.
- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  printed p. 20 (PDF p. 24), motivates subordinate weights in bundle
  constructions. Here the finite cylinder-chart cover is assumed, and the
  fiberwise algebra allows arbitrary semirings and varying chart models.
-/

@[expose] public section

open Bundle Set
open scoped BigOperators unitInterval

namespace Bundle.Trivialization

universe uX uP uF uE uT uR

section Family

variable {X : Type uX} [TopologicalSpace X] [NormalSpace X]
  {P : Type uP} {n : ℕ} {F : Fin n → Type uF} {E : X × I → Type uE}
  [∀ j, TopologicalSpace (F j)] [TopologicalSpace (TotalSpace P E)]

/-- Finite cylinder charts over an open cover of a normal space give a
base-preserving homeomorphism from the iterated standard pullback of the whole
zero-time restriction to the same original total space. Both directions fix
every bottom point, including points in the closed supports of the weights.

No weights are assumed: they are obtained from
`ContinuousMap.exists_finite_weights` and used by `finiteCylinderTransport`.
The chart models may vary, and the parameter `P` has no structure assumptions. -/
theorem exists_finiteCylinderTransport
    (e : ∀ j, Trivialization (F j) (π P E)) (U : Fin n → Set X)
    (hU : ∀ j, IsOpen (U j)) (hcover : (⋃ j, U j) = univ)
    (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet) :
    ∃ H : TotalSpace P
        ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)) ≃ₜ
        TotalSpace P E,
      (∀ z, (H z).proj = z.proj) ∧
      (∀ z, (H.symm z).proj = z.proj) ∧
      (∀ (x : X) (v : E (x, (0 : I))),
        H (⟨(x, 0), v⟩ : TotalSpace P
          ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E))) =
          (⟨(x, 0), v⟩ : TotalSpace P E)) ∧
      (∀ (x : X) (v : E (x, (0 : I))),
        H.symm (⟨(x, 0), v⟩ : TotalSpace P E) =
          (⟨(x, 0), v⟩ : TotalSpace P
            ((Prod.fst : X × I → X) *ᵖ ((fun x : X ↦ (x, (0 : I))) *ᵖ E)))) := by
  classical
  obtain ⟨w, hw, _, hsum, hsupport⟩ := ContinuousMap.exists_finite_weights
    (Finset.univ : Finset (Fin n)) U (fun j _ ↦ hU j) (by simpa using hcover)
  have hsum' : ∀ x, ∑ j : Fin n, w j x = 1 := by
    simpa using hsum
  refine ⟨finiteCylinderTransport e U hchart w hw hsum' hsupport hcover, ?_, ?_, ?_, ?_⟩
  · exact finiteCylinderTransport_proj e U hchart w hw hsum' hsupport hcover
  · exact finiteCylinderTransport_symm_proj e U hchart w hw hsum' hsupport hcover
  · exact finiteCylinderTransport_apply_bottom e U hchart w hw hsum' hsupport hcover
  · exact finiteCylinderTransport_symm_apply_bottom e U hchart w hw hsum' hsupport hcover

end Family

section Projection

variable {X : Type uX} [TopologicalSpace X] [NormalSpace X]
    {T : Type uT} [TopologicalSpace T] {n : ℕ} {F : Fin n → Type uF}
    [∀ j, TopologicalSpace (F j)] {R : Type uR} [Semiring R]
    [∀ j, AddCommMonoid (F j)] [∀ j, Module R (F j)]
    (p : T → X × I)
    [∀ b, AddCommMonoid {z : T // p z = b}] [∀ b, Module R {z : T // p z = b}]

/-- A finite open cylinder-chart cover of a normal space gives transport from
the standard pullback of the entire original zero slice to the same `T`, without
given weights. The selected weights and their certificates are returned with
`finiteCylinderTransportOfProjection`, its whole-base and every-bottom laws,
linearity on the given projection-fiber modules over any semiring, and its top
comparison with the independently ordered endpoint using the same weights.

No scalar topology or continuity of module operations is needed. The base,
total space, varying chart models and scalar type have independent universes;
projection fibers inherit the universe of `T`.

Hatcher, *Vector Bundles and K-Theory*, printed p. 20 (PDF p. 24), motivates the
subordinate weights. This finite cylinder-chart cover result allows arbitrary
semirings and does not assert homotopy invariance for arbitrary bundles. -/
theorem exists_finiteCylinderTransportOfProjection
    (e : ∀ j, Trivialization (F j) p) (U : Fin n → Set X)
    (hU : ∀ j, IsOpen (U j)) (hcover : (⋃ j, U j) = univ)
    (hchart : ∀ j, U j ×ˢ (univ : Set I) ⊆ (e j).baseSet)
    (L : ∀ j b, b ∈ (e j).baseSet → {z : T // p z = b} ≃ₗ[R] F j)
    (hL : ∀ j b (hb : b ∈ (e j).baseSet) (v : {z : T // p z = b}),
      L j b hb v = (e j v.val).2) :
    ∃ (w : Fin n → C(X, ℝ)) (hw : ∀ j x, 0 ≤ w j x ∧ w j x ≤ 1)
      (hsum : ∀ x, ∑ j, w j x = 1)
      (hsupport : ∀ j, closure {x | w j x ≠ 0} ⊆ U j)
      (H : {s : (X × I) × {z : T // (p z).2 = 0} //
        s.1.1 = (p s.2.val).1} ≃ₜ T)
      (hH : ∀ s, p (H s) = s.val.1),
      H = finiteCylinderTransportOfProjection p e U hchart w hw hsum hsupport hcover ∧
      (∀ z, (H.symm z).val.1 = p z) ∧
      (∀ z : {z : T // (p z).2 = 0}, H ⟨(((p z.val).1, 0), z), rfl⟩ = z.val) ∧
      (∀ z : {z : T // (p z).2 = 0}, H.symm z.val = ⟨(((p z.val).1, 0), z), rfl⟩) ∧
      (∀ (x : X) (t : I),
        IsLinearMap R (fun v : {z : T // p z = (x, (0 : I))} ↦
          (⟨H ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
              (congrArg Prod.fst v.property).symm⟩,
            hH ⟨((x, t), ⟨v.val, congrArg Prod.snd v.property⟩),
              (congrArg Prod.fst v.property).symm⟩⟩ : {z : T // p z = (x, t)}))) ∧
      (∀ z : {z : T // (p z).2 = 0},
        H ⟨(((p z.val).1, 1), z), rfl⟩ =
          (finiteCylinderEndpointTransportOfProjection p e U hchart w hw hsum hsupport
            hcover z).val) := by
  classical
  obtain ⟨w, hw, _, hsum, hsupport⟩ := ContinuousMap.exists_finite_weights
    (Finset.univ : Finset (Fin n)) U (fun j _ ↦ hU j) (by simpa using hcover)
  have hsum' : ∀ x, ∑ j : Fin n, w j x = 1 := by
    simpa using hsum
  refine ⟨w, hw, hsum', hsupport,
    finiteCylinderTransportOfProjection p e U hchart w hw hsum' hsupport hcover,
    finiteCylinderTransportOfProjection_proj p e U hchart w hw hsum' hsupport hcover,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteCylinderTransportOfProjection_symm_proj p e U hchart w hw hsum' hsupport
      hcover
  · exact finiteCylinderTransportOfProjection_apply_bottom p e U hchart w hw hsum' hsupport
      hcover
  · exact finiteCylinderTransportOfProjection_symm_apply_bottom p e U hchart w hw hsum'
      hsupport hcover
  · intro x t
    exact finiteCylinderTransportOfProjection_isLinearMap_of_coordinates p e U hchart w hw
      hsum' hsupport L hL hcover x t
  · exact finiteCylinderTransportOfProjection_apply_top p e U hchart w hw hsum' hsupport
      hcover

end Projection

end Bundle.Trivialization
