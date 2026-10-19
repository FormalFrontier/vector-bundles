/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Scalar dilations of von Neumann bounded sets

Fixed scalar dilations preserve von Neumann boundedness without a continuity assumption on
the scalar action on the module. The module may be an additive commutative monoid.
For a continuous scalar action over a normed field, the dilated set is the image under the
continuous linear map given by the scalar multiple of the identity.

## References

* Moritz Doll, Mathlib's `Analysis.LocallyConvex.Bounded`, for von Neumann boundedness and
  its small-sets characterization.
* Jean Lo and Yury Kudryashov, Mathlib's `Topology.Bornology.Absorbs`.
-/

@[expose] public section

open scoped Pointwise

namespace Bornology

universe uK uX

/-- Fixed scalar dilations of a von Neumann bounded set are von Neumann bounded.
No continuity of the scalar action on the module is required. -/
theorem IsVonNBounded.smul_set {K : Type uK} [NormedDivisionRing K]
    {X : Type uX} [AddCommMonoid X] [Module K X] [TopologicalSpace X]
    {S : Set X} (hS : IsVonNBounded K S) (c : K) : IsVonNBounded K (c • S) := by
  let : AddCommGroup X := Module.addCommMonoidToAddCommGroup K
  apply isVonNBounded_iff_tendsto_smallSets_nhds.mpr
  have hc : Filter.Tendsto (fun ε : K => ε * c) (nhds 0) (nhds 0) := by
    simpa only [zero_mul] using (continuous_mul_const c).tendsto (0 : K)
  simpa only [Function.comp_def, mul_smul] using hS.tendsto_smallSets_nhds.comp hc

/-- With a continuous scalar action, dilation is the image under the scalar multiple of the
continuous linear identity. This identifies the dilation with the input to
`Bornology.IsVonNBounded.image`. -/
theorem smul_set_eq_image_smul_id {K : Type uK} [NormedField K]
    {X : Type uX} [AddCommGroup X] [Module K X] [TopologicalSpace X]
    [ContinuousConstSMul K X] (c : K) (S : Set X) :
    c • S = (c • ContinuousLinearMap.id K X) '' S := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image, smul_apply, ContinuousLinearMap.id_apply]

end Bornology
