/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.Module.ModuleTopology
public import VectorBundles.Topology.VectorBundle.ProjectorAtlas

/-!
# Range atlases in finite-dimensional ambient spaces

A norm-continuous family of idempotents on a finite-dimensional normed space with the module
topology gives a finite-rank atlas on its family of ranges. The ranges retain their subspace
topologies, and their total space carries the range-graph topology. Neither completeness nor
globally constant rank is required.
-/

@[expose] public section

universe uK uA uX uF

namespace ContinuousLinearMap

variable {K : Type uK} [NontriviallyNormedField K]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]

attribute [local instance] VectorBundle.rangeTotalSpaceTopology

/-- A continuous family of idempotents on a finite-dimensional ambient space with the module
topology has a finite-rank atlas on its ranges, with the range-graph total-space topology.
The atlas allows different ranks on different components of the base. -/
noncomputable def finiteRankRangeAtlasOfFiniteDimensional
    [FiniteDimensional K A] [IsModuleTopology K A]
    {X : Type uX} [TopologicalSpace X] (F : Type uF)
    (Q : X → A →L[K] A) (hQ : Continuous Q)
    (hid : ∀ x, IsIdempotentElem (Q x)) :
    Bundle.FiniteRankAtlas K F (fun x ↦ LinearMap.range (Q x).toLinearMap) := by
  exact finiteRankRangeAtlas (K := K) (F := F) Q hQ hid
    (fun _ ↦ inferInstance) (fun x ↦ by
      have hp : IsIdempotentElem (Q x).toLinearMap :=
        congrArg (fun T : A →L[K] A ↦ T.toLinearMap) (hid x)
      exact LinearMap.IsIdempotentElem.isModuleTopology_range hp)

/-- The chart rank is the dimension of the range at its anchor. -/
theorem finiteRankRangeAtlasOfFiniteDimensional_rank
    [FiniteDimensional K A] [IsModuleTopology K A]
    {X : Type uX} [TopologicalSpace X] (F : Type uF)
    (Q : X → A →L[K] A) (hQ : Continuous Q)
    (hid : ∀ x, IsIdempotentElem (Q x)) (c : X) :
    (finiteRankRangeAtlasOfFiniteDimensional F Q hQ hid).rank c =
      Module.finrank K (LinearMap.range (Q c).toLinearMap) := rfl

end ContinuousLinearMap
