/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order
public import Mathlib.Topology.WithTopology
public import VectorBundles.Topology.Compactness.Paracompact
public import VectorBundles.Topology.FiberBundle.Paracompact

/-!
# Paracompact models of canonical trivial bundles

These applications retain the canonical total-space topology and fiber-bundle structure of
`Bundle.Trivial`. The total-space paracompactness premises come from metric spaces, a product
with a compact first factor, or finiteness, independently of reflection to the model.
-/

@[expose] public section

open Bundle Set

namespace ParacompactSpace

/-- The second projection of the real plane retracts continuously onto the real line, with
section `y ↦ (0, y)`. The plane is paracompact by its stock metric structure. -/
theorem real_of_plane_retraction : ParacompactSpace ℝ := by
  let : ParacompactSpace (ℝ × ℝ) := inferInstance
  exact ParacompactSpace.of_continuous_leftInverse
    (r := (Prod.snd : ℝ × ℝ → ℝ)) (j := fun y : ℝ => (0, y))
    continuous_snd (continuous_const.prodMk continuous_id) (fun _ => rfl)

/-- In the canonical trivial real bundle over `ℝ`, the closed base patch is the whole,
noncompact real line. Its original total space is homeomorphic to the metric real plane. -/
theorem real_of_trivial_real_bundle_closed_univ : ParacompactSpace ℝ := by
  have hplane : ParacompactSpace (ℝ × ℝ) := inferInstance
  let : ParacompactSpace (TotalSpace ℝ (Trivial ℝ ℝ)) :=
    (Trivial.homeomorphProd ℝ ℝ).paracompactSpace_iff.mpr hplane
  exact (trivializationAt ℝ (Trivial ℝ ℝ) 0).paracompactSpace_model_of_isClosed
    (FiberBundle.continuous_proj ℝ (Trivial ℝ ℝ)) (s := Set.univ)
    isClosed_univ ⟨0, Set.mem_univ _⟩ (by
      intro b _
      change b ∈ (Set.univ : Set ℝ)
      exact Set.mem_univ b)

/-- The canonical real bundle over the indiscrete two-point space has paracompact original
total space: its product presentation has compact first factor and paracompact real second
factor. The base topology is `⊤`, not the discrete topology `⊥`. -/
theorem real_of_indiscrete_trivial_bundle : ParacompactSpace ℝ := by
  let : R0Space (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) :=
    { specializes_symm := ⟨fun {x y} _ => (Inseparable.all y x).specializes⟩ }
  let : CompactSpace (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) :=
    Finite.compactSpace
  let : ParacompactSpace ℝ := inferInstance
  have hproduct :
      ParacompactSpace (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2)) × ℝ) :=
    inferInstance
  let : ParacompactSpace
      (TotalSpace ℝ (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) ℝ)) :=
    (Homeomorph.paracompactSpace_iff
      (Trivial.homeomorphProd (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) ℝ)).mpr
      hproduct
  exact FiberBundle.paracompactSpace_model ℝ
    (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) ℝ)
    (WithTopology.toTopology (⊤ : TopologicalSpace (Fin 2)) 0)

/-- Over the same nonempty indiscrete two-point base, the canonical trivial bundle with empty
model has empty original total space, hence a nonsurjective original projection. Finiteness of
that total space supplies paracompactness without any nonemptiness assumption on the model. -/
theorem empty_of_indiscrete_trivial_bundle : ParacompactSpace Empty := by
  let : R0Space (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) :=
    { specializes_symm := ⟨fun {x y} _ => (Inseparable.all y x).specializes⟩ }
  let : Finite
      (TotalSpace Empty
        (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) Empty)) :=
    Finite.of_equiv
      (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2)) × Empty)
      ((Trivial.homeomorphProd
        (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) Empty).toEquiv.symm)
  let : CompactSpace
      (TotalSpace Empty
        (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) Empty)) :=
    Finite.compactSpace
  let : ParacompactSpace
      (TotalSpace Empty
        (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) Empty)) :=
    inferInstance
  exact FiberBundle.paracompactSpace_model Empty
    (Trivial (WithTopology (Fin 2) (⊤ : TopologicalSpace (Fin 2))) Empty)
    (WithTopology.toTopology (⊤ : TopologicalSpace (Fin 2)) 0)

/-- With both base and model the canonical Sierpiński space `Prop`, the original total space
has four points and is therefore paracompact. The closed-patch theorem applies even though
this base and this model are not R₀ spaces. -/
theorem prop_of_trivial_sierpinski_bundle : ParacompactSpace Prop := by
  let : Finite (TotalSpace Prop (Trivial Prop Prop)) :=
    Finite.of_equiv (Prop × Prop) (Trivial.homeomorphProd Prop Prop).toEquiv.symm
  let : CompactSpace (TotalSpace Prop (Trivial Prop Prop)) := Finite.compactSpace
  let : ParacompactSpace (TotalSpace Prop (Trivial Prop Prop)) := inferInstance
  exact (trivializationAt Prop (Trivial Prop Prop) True).paracompactSpace_model_of_isClosed
    (FiberBundle.continuous_proj Prop (Trivial Prop Prop)) (s := Set.univ)
    isClosed_univ ⟨True, Set.mem_univ _⟩ (by
      intro b _
      change b ∈ (Set.univ : Set Prop)
      exact Set.mem_univ b)

end ParacompactSpace
