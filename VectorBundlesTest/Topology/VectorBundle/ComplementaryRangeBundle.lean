/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.ProjectorAtlas.SplitFamily
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A complementary line in the real plane

The inclusion of the first coordinate and projection onto it split the trivial real line bundle
inside the trivial plane bundle over `ℝ`. Its complementary projector has the proper, nonzero
vertical line as its range. We use the returned bundle's linear coordinates on a nonzero vertical
vector, and its canonical change of model tag at the base point `2`.
-/

namespace ComplementaryRealLine

noncomputable section

attribute [local instance] VectorBundle.rangeTotalSpaceTopology

private abbrev Plane := ℝ × ℝ
private abbrev Line := Bundle.Trivial ℝ ℝ

private def inclusion : ∀ b : ℝ, Line b →ₗ[ℝ] Plane :=
  fun _ => LinearMap.inl ℝ ℝ ℝ

private def projection : ∀ b : ℝ, Plane →ₗ[ℝ] Line b :=
  fun _ => LinearMap.fst ℝ ℝ ℝ

private def fibreEquiv : ∀ b : ℝ, Line b ≃ₗ[ℝ] ℝ :=
  fun _ => LinearEquiv.refl ℝ ℝ

private theorem projection_inclusion (b : ℝ) (v : Line b) :
    projection b (inclusion b v) = v := rfl

private theorem continuous_inclusion :
    Continuous (fun z : Bundle.TotalSpace ℝ Line => (z.proj, inclusion z.proj z.snd)) := by
  change Continuous (fun z : Bundle.TotalSpace ℝ Line => (z.proj, (z.snd, (0 : ℝ))))
  have h := (Bundle.Trivial.homeomorphProd ℝ ℝ).continuous
  exact (continuous_fst.comp h).prodMk ((continuous_snd.comp h).prodMk continuous_const)

private theorem continuous_projection :
    Continuous (fun y : ℝ × Plane =>
      (Bundle.TotalSpace.mk y.1 (projection y.1 y.2) : Bundle.TotalSpace ℝ Line)) := by
  exact (Bundle.Trivial.homeomorphProd ℝ ℝ).symm.continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))

private abbrev complementaryProjector : ℝ → Plane →ₗ[ℝ] Plane :=
  fun b => LinearMap.id - (inclusion b).comp (projection b)

private abbrev Complement : ℝ → Type :=
  fun b => LinearMap.range (complementaryProjector b)

private abbrev complementRank := Module.finrank ℝ Plane - Module.finrank ℝ ℝ
private abbrev Model := Fin complementRank → ℝ

private theorem complementRank_eq_one : complementRank = 1 := by
  simp [complementRank, Plane, Module.finrank_prod]

private def vertical : Complement (2 : ℝ) :=
  ⟨(0, 1), ⟨(0, 1), by simp [complementaryProjector, inclusion, projection]⟩⟩

private theorem vertical_ne_zero : vertical ≠ 0 := by
  intro h
  have h' : (1 : ℝ) = 0 := congrArg (fun v : Complement (2 : ℝ) => (v : Plane).2) h
  exact one_ne_zero h'

-- The new tag uses the topology transported from the old range graph, not a fresh range graph.
local notation "tP" => (VectorBundle.rangeTotalSpaceTopology (F := ℝ) complementaryProjector)
local notation "tW" => (Bundle.TotalSpace.changeModelTopology ℝ Model Complement tP)

local instance : TopologicalSpace (Bundle.TotalSpace Model Complement) := tW

local instance : FiberBundle Model Complement :=
  VectorBundle.complementaryRangeFiberBundle ℝ ℝ Plane ℝ ℝ Line fibreEquiv
    inclusion projection projection_inclusion continuous_inclusion continuous_projection

local instance : IsModuleTopology ℝ ℝ := IsTopologicalSemiring.toIsModuleTopology ℝ
local instance : IsModuleTopology ℝ Model := IsModuleTopology.instPi

local instance : VectorBundle ℝ Model Complement :=
  VectorBundle.complementaryRangeVectorBundle ℝ ℝ Plane ℝ ℝ Line fibreEquiv
    inclusion projection projection_inclusion continuous_inclusion continuous_projection

local notation "H" =>
  (@Homeomorph.toEquiv _ _ tP tW
    (VectorBundle.complementaryRangeHomeomorph ℝ ℝ Plane ℝ ℝ Line fibreEquiv
      inclusion projection projection_inclusion continuous_inclusion continuous_projection))

/-- The complementary projector for `LinearMap.inl` and `LinearMap.fst` on the real plane
has one-dimensional range. -/
public theorem vertical_range_finrank :
    Module.finrank ℝ (LinearMap.range
      ((LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) -
        (LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.fst ℝ ℝ ℝ))) = 1 := by
  change Module.finrank ℝ (Complement (2 : ℝ)) = 1
  have hsplit : ∀ b : ℝ, (projection b).comp (inclusion b) = LinearMap.id :=
    fun b => LinearMap.ext (fun v => projection_inclusion b v)
  have hrank : Module.finrank ℝ (Complement (2 : ℝ)) = complementRank :=
    LinearMap.finrank_range_id_sub_comp_of_rightInverse_family
      projection inclusion hsplit fibreEquiv 2
  exact hrank.trans complementRank_eq_one

/-- The complementary line has rank one, and its transported vertical vector has nonzero
coordinates in the returned line bundle. -/
private theorem vertical_rank_and_coordinates :
    Module.finrank ℝ (Complement (2 : ℝ)) = 1 ∧
    (H (Bundle.TotalSpace.mk 2 vertical)).proj = 2 ∧
    ((H (Bundle.TotalSpace.mk 2 vertical)).snd : Plane) = (0, 1) ∧
    ((H (Bundle.TotalSpace.mk 2 vertical)).snd : Plane) ≠ 0 ∧
    (VectorBundle.continuousLinearEquivAt ℝ Model Complement
      (H (Bundle.TotalSpace.mk 2 vertical)).proj)
        (H (Bundle.TotalSpace.mk 2 vertical)).snd ≠ 0 := by
  have hnonzero : ((H (Bundle.TotalSpace.mk 2 vertical)).snd : Plane) ≠ 0 := by
    rw [VectorBundle.complementaryRangeHomeomorph_snd]
    intro h
    exact vertical_ne_zero (Subtype.ext h)
  refine ⟨vertical_range_finrank, ?_, ?_, hnonzero, ?_⟩
  · simp only [VectorBundle.complementaryRangeHomeomorph_proj]
  · simp only [VectorBundle.complementaryRangeHomeomorph_snd]
    rfl
  · intro h
    have hzero : (H (Bundle.TotalSpace.mk 2 vertical)).snd = 0 :=
      (VectorBundle.continuousLinearEquivAt ℝ Model Complement
        (H (Bundle.TotalSpace.mk 2 vertical)).proj).injective
        (h.trans (map_zero (VectorBundle.continuousLinearEquivAt ℝ Model Complement
          (H (Bundle.TotalSpace.mk 2 vertical)).proj)).symm)
    exact hnonzero (congrArg
      (fun v : Complement (H (Bundle.TotalSpace.mk 2 vertical)).proj => (v : Plane)) hzero)

end

end ComplementaryRealLine
