/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import VectorBundles.Topology.VectorBundle.MetricComap
import VectorBundlesTest.Topology.VectorBundle.OrthogonalComparison

/-!
# Comapping the standard metric by the Euclidean shear

The plane, trivial bundle, shear operators and both supplied metrics are those of
`ShearMetricComparison`. The plane keeps its original Euclidean norm throughout.
The comap of the standard metric is the existing shear metric, and its endpoint forms
are neither equal nor scalar multiples. The second coordinate vector has squared lengths
one and two at parameters zero and one, respectively.
-/

noncomputable section

open Bundle ShearMetricComparison

namespace ShearMetricComap

private theorem shear_isEmbedding (t : ℝ) : Topology.IsEmbedding (shear t) := by
  exact (LinearMap.isClosedEmbedding_of_injective
    (f := (shear t).toLinearMap) (LinearMap.ker_eq_bot.mpr (shear_injective t))).isEmbedding

private theorem continuous_shear_section : Continuous
    (fun t : ℝ ↦ TotalSpace.mk' (Plane →L[ℝ] Plane)
      (E := fun t ↦ Ambient t →L[ℝ] Ambient t) t (shear t)) := by
  have hadd : Continuous (fun p : (Plane →L[ℝ] Plane) × (Plane →L[ℝ] Plane) ↦
      p.1 + p.2) :=
    (ContinuousLinearMap.isTopologicalAddGroup (σ := RingHom.id ℝ)
      (E := Plane) (F := Plane)).toContinuousAdd.1
  have hshear : Continuous shear := by
    change Continuous (fun t : ℝ ↦ ContinuousLinearMap.id ℝ Plane + t • shearNilpotent)
    exact hadd.comp₂ continuous_const (continuous_id.smul continuous_const)
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! hshear.continuousAt (x := x) using 1
  ext t v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]

/-- The general construction recovers the independently supplied shear metric. -/
private theorem comap_standard_eq_shearMetric :
    standardMetric.comap (G := Plane) shear shear_isEmbedding continuous_shear_section =
      shearMetric := by
  -- Use ContinuousHermitianMetric.ext and ContinuousHermitianMetric.comap_inner_apply,
  -- then ContinuousHermitianMetric.trivial_inner and shearForm_apply.
  apply ContinuousHermitianMetric.ext
  intro t v w
  rw [ContinuousHermitianMetric.comap_inner_apply]
  change (ContinuousHermitianMetric.trivial ℝ ℝ Plane).inner t (shear t v) (shear t w) =
    shearForm t v w
  rw [ContinuousHermitianMetric.trivial_inner, shearForm_apply]

/-- The induced metric varies nontrivially in the original Euclidean geometry. -/
example :
    let g := standardMetric.comap (G := Plane) shear shear_isEmbedding continuous_shear_section
    g.inner 0 ey ey = 1 ∧ g.inner 1 ey ey = 2 ∧
      ¬ ∃ r : ℝ, ∀ v w : Plane, g.inner 1 v w = r * g.inner 0 v w := by
  dsimp only
  rw [comap_standard_eq_shearMetric]
  change shearForm 0 ey ey = 1 ∧ shearForm 1 ey ey = 2 ∧
    ¬ ∃ r : ℝ, ∀ v w : Plane, shearForm 1 v w = r * shearForm 0 v w
  refine ⟨?_, ?_, ?_⟩
  · rw [shearForm_coordinates]
    norm_num [ey]
  · rw [shearForm_coordinates]
    norm_num [ey]
  · rintro ⟨r, hr⟩
    have h := hr ex ey
    rw [shearForm_coordinates, shearForm_coordinates] at h
    norm_num [ex, ey] at h

end ShearMetricComap
