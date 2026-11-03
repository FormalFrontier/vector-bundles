/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Restriction to a dense submodule

Restricting a continuous semilinear map to a dense submodule preserves its operator
seminorm. Consequently Mathlib's existing domain-restriction map is an isometry and
uniform inducing, even when the target is not separated. In that generality the
restriction map need not be injective.

The proof uses Mathlib's operator-norm bounds and extends a continuous real norm
inequality from the dense submodule. This is the closed-property argument also used
in Mathlib's operator-extension estimates; restriction needs neither completeness
nor separation, since no map is being extended.
-/

@[expose] public section

universe uK uL uA uG

namespace ContinuousLinearMap

section OperatorSeminorm

variable {K : Type uK} [NontriviallyNormedField K]
variable {L : Type uL} [NontriviallyNormedField L]
variable {σ : K →+* L} [RingHomIsometric σ]
variable {A : Type uA} [SeminormedAddCommGroup A] [NormedSpace K A]
variable {G : Type uG} [SeminormedAddCommGroup G] [NormedSpace L G]

/-- Domain restriction to a dense submodule preserves the operator seminorm.
No completeness, separation, finite dimension or surjectivity of `σ` is required. -/
theorem norm_domRestrict_of_dense (T : A →SL[σ] G) (U : Submodule K A)
    (hdense : Dense (U : Set A)) : ‖T.domRestrict U‖ = ‖T‖ := by
  apply le_antisymm
  · exact (T.domRestrict U).opNorm_le_bound (norm_nonneg T)
      (fun u => T.le_opNorm (u : A))
  · apply T.opNorm_le_bound (norm_nonneg (T.domRestrict U))
    exact isClosed_property hdense.denseRange_val
      (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm))
      (fun u => (T.domRestrict U).le_opNorm u)

/-- Domain restriction to a dense submodule is a pseudometric isometry.
It need not be injective when the target is not separated. -/
theorem isometry_domRestrict_of_dense (U : Submodule K A)
    (hdense : Dense (U : Set A)) :
    Isometry (fun T : A →SL[σ] G => T.domRestrict U) := by
  refine isometry_iff_dist_eq.mpr ?_
  intro T S
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(T - S).domRestrict U‖ = ‖T - S‖
  exact norm_domRestrict_of_dense (T - S) U hdense

end OperatorSeminorm

section Uniformity

variable {K : Type uK} [kK : NontriviallyNormedField K]
variable {L : Type uL} [kL : NormedField L]
variable {σ : K →+* L} [RingHomIsometric σ]
variable {A : Type uA} [sA : SeminormedAddCommGroup A]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable {G : Type uG} [sG : SeminormedAddCommGroup G]
variable [nG : @NormedSpace L G kL sG]

/-- The existing domain-restriction map induces the uniformity from a dense
submodule. The target field need only be normed, and neither injectivity nor
separation is required. -/
theorem isUniformInducing_domRestrict_of_dense (U : Submodule K A)
    (hdense : Dense (U : Set A)) :
    IsUniformInducing (fun T : A →SL[σ] G => T.domRestrict U) := by
  -- Isometry of the scalar homomorphism supplies nontriviality without changing
  -- either normed field or either given normed-space structure.
  let : NontriviallyNormedField L :=
    { toNormedField := kL
      non_trivial := by
        obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
        exact ⟨σ c, by simpa only [RingHomIsometric.norm_map] using hc⟩ }
  exact (isometry_domRestrict_of_dense (σ := σ) (G := G) U hdense).isUniformInducing

end Uniformity

end ContinuousLinearMap
