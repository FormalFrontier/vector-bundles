/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import VectorBundles.Analysis.Normed.Operator.Completion

/-!
# Completing the scalars of a seminormed module

The completion of a seminormed space over a normed field carries a canonical action of the
completed field. `UniformSpace.Completion.smulOverCompletion` constructs this action by joint
dense extension. `UniformSpace.Completion.normedSpaceOverCompletion` bundles its laws without
installing an instance. Both constructions retain the given action on the original space.

`ContinuousLinearMap.completionOverCompletion` equips the usual completed continuous linear map
with linearity over the completed field, without changing its underlying function. Operator-norm
preservation additionally requires a nontrivially normed original field.

## Implementation notes

All completion types, additive structures, norms and topologies are those of Mathlib. The named
scalar-extension structures are not instances: this matters when the vector space has the same
carrier as the field but a different given action. The self-action comparison specializes the
original action to the usual field action. Original spaces need not be separated or complete.

The construction follows Mathlib's joint dense extension of multiplication in
`Mathlib.Topology.Algebra.UniformRing`, using `IsDenseInducing.extend_Z_bilin`. The extension is
jointly continuous, not globally uniformly continuous on the product.
-/

@[expose] public section

noncomputable section

open UniformSpace

universe uK uE uA uG uH

namespace UniformSpace.Completion

variable (K : Type uK) (E : Type uE)
variable [kK : NormedField K] [sE : SeminormedAddCommGroup E]
variable [nE : @NormedSpace K E kK sE]

/-- The action of the completed field on the completed space, obtained by joint dense extension
of the given original scalar multiplication. -/
def smulOverCompletion : Completion K → Completion E → Completion E :=
  Function.curry <|
    (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
      (fun p : K × E => ((p.1 • p.2 : E) : Completion E))

/-- Scalar multiplication over the completed field is jointly continuous. -/
@[fun_prop]
theorem continuous_smulOverCompletion :
    Continuous (fun p : Completion K × Completion E => smulOverCompletion K E p.1 p.2) := by
  let b : K →+ E →+ Completion E :=
    { toFun := fun k =>
        { toFun := fun e => ((k • e : E) : Completion E)
          map_zero' := by simp only [smul_zero, coe_zero]
          map_add' := by intros; simp only [smul_add, coe_add] }
      map_zero' := by
        ext e
        change (((0 : K) • e : E) : Completion E) = 0
        rw [zero_smul, coe_zero]
      map_add' := by
        intro k l
        ext e
        change (((k + l) • e : E) : Completion E) =
          ((k • e : E) : Completion E) + ((l • e : E) : Completion E)
        rw [add_smul, coe_add] }
  have hb : Continuous (fun p : K × E => b p.1 p.2) :=
    (continuous_coe E).comp continuous_smul
  exact (isDenseInducing_toCompl K).extend_Z_bilin (isDenseInducing_toCompl E) hb

/-- On two original inputs the completed action is the given original action. -/
theorem smulOverCompletion_coe_coe (k : K) (e : E) :
    smulOverCompletion K E (k : Completion K) (e : Completion E) = (k • e : E) :=
  (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    ((continuous_coe E).comp continuous_smul) (k, e)

/-- Restricting completed scalars to the original field recovers its existing action on every
completed vector. -/
@[simp]
theorem smulOverCompletion_coe (k : K) (x : Completion E) :
    smulOverCompletion K E (k : Completion K) x = k • x := by
  refine induction_on x (isClosed_eq
    ((continuous_smulOverCompletion K E).comp (continuous_const.prodMk continuous_id))
    (continuous_const_smul k)) ?_
  intro e
  rw [smulOverCompletion_coe_coe, coe_smul]

/-- The completed action preserves the exact scalar norm identity. -/
theorem norm_smulOverCompletion (s : Completion K) (x : Completion E) :
    ‖smulOverCompletion K E s x‖ = ‖s‖ * ‖x‖ := by
  refine induction_on₂ s x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k e
  simp only [smulOverCompletion_coe_coe, norm_coe, norm_smul]

/-- Joint continuity and agreement on original pairs characterize the completed action. -/
theorem smulOverCompletion_unique (h : Completion K → Completion E → Completion E)
    (hc : Continuous (fun p : Completion K × Completion E => h p.1 p.2))
    (he : ∀ (k : K) (e : E), h k e = (k • e : E)) :
    h = smulOverCompletion K E := by
  have hh := (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_unique
    (f := fun p : K × E => ((p.1 • p.2 : E) : Completion E))
    (g := fun p : Completion K × Completion E => h p.1 p.2)
    (fun p : K × E => he p.1 p.2) hc
  exact (congrArg Function.curry hh).symm

/-- A zero completed scalar acts by zero. -/
@[simp]
theorem zero_smulOverCompletion (x : Completion E) :
    smulOverCompletion K E 0 x = 0 := by
  simpa only [coe_zero, zero_smul] using smulOverCompletion_coe K E (0 : K) x

/-- The unit completed scalar acts as the identity. -/
@[simp]
theorem one_smulOverCompletion (x : Completion E) :
    smulOverCompletion K E 1 x = x := by
  simpa only [coe_one, one_smul] using smulOverCompletion_coe K E (1 : K) x

/-- Every completed scalar sends the zero vector to zero. -/
@[simp]
theorem smulOverCompletion_zero (s : Completion K) :
    smulOverCompletion K E s 0 = 0 := by
  refine induction_on s (isClosed_eq (by fun_prop) continuous_const) ?_
  intro k
  simp only [smulOverCompletion_coe, smul_zero]

private theorem smulOverCompletion_add (s : Completion K) (x y : Completion E) :
    smulOverCompletion K E s (x + y) =
      smulOverCompletion K E s x + smulOverCompletion K E s y := by
  refine induction_on₃ s x y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k e f
  simp only [← coe_add, smulOverCompletion_coe_coe, smul_add]

private theorem add_smulOverCompletion (s t : Completion K) (x : Completion E) :
    smulOverCompletion K E (s + t) x =
      smulOverCompletion K E s x + smulOverCompletion K E t x := by
  refine induction_on₃ s t x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k l e
  simp only [← coe_add, smulOverCompletion_coe_coe, add_smul]

private theorem mul_smulOverCompletion (s t : Completion K) (x : Completion E) :
    smulOverCompletion K E (s * t) x =
      smulOverCompletion K E s (smulOverCompletion K E t x) := by
  refine induction_on₃ s t x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k l e
  simp only [← coe_mul, smulOverCompletion_coe_coe, mul_smul]

/-- The normed-space structure over the completed field on the existing completion. Its scalar
operation is `smulOverCompletion`; this named structure is deliberately not an instance. -/
@[instance_reducible]
def normedSpaceOverCompletion : NormedSpace (Completion K) (Completion E) where
  smul := smulOverCompletion K E
  one_smul := one_smulOverCompletion K E
  mul_smul := by exact mul_smulOverCompletion K E
  smul_zero := smulOverCompletion_zero K E
  smul_add := by exact smulOverCompletion_add K E
  add_smul := by exact add_smulOverCompletion K E
  zero_smul := zero_smulOverCompletion K E
  norm_smul_le s x := (norm_smulOverCompletion K E s x).le

/-- The ordinary normed-space structure uses the publicly constructed completed action. -/
@[simp]
theorem normedSpaceOverCompletion_smul (s : Completion K) (x : Completion E) :
    @SMul.smul (Completion K) (Completion E)
      (normedSpaceOverCompletion K E).toSMul s x = smulOverCompletion K E s x := rfl

/-- Compatibility of the scalar-side original action, the completed action, and the vector-side
original action. The three scalar-multiplication dictionaries are specified separately. -/
theorem isScalarTowerOverCompletion :
    @IsScalarTower K (Completion K) (Completion E)
      (inferInstance : SMul K (Completion K))
      (normedSpaceOverCompletion K E).toSMul
      (inferInstance : SMul K (Completion E)) := by
  let := normedSpaceOverCompletion K E
  refine ⟨fun k s x => ?_⟩
  change smulOverCompletion K E (k • s) x = k • smulOverCompletion K E s x
  have hs : k • s = (k : Completion K) * s :=
    (smul_def K K k s).trans (congr_fun (map_smul_eq_mul_coe K K k) s)
  calc
    smulOverCompletion K E (k • s) x =
        smulOverCompletion K E ((k : Completion K) * s) x :=
      congrArg (fun t : Completion K => smulOverCompletion K E t x) hs
    _ = smulOverCompletion K E (k : Completion K) (smulOverCompletion K E s x) := by
      exact mul_smulOverCompletion K E (k : Completion K) s x
    _ = k • smulOverCompletion K E s x :=
      smulOverCompletion_coe K E k (smulOverCompletion K E s x)

/-- For the usual original self-action, the completed action is the existing field multiplication.
This does not identify an arbitrary given action on the field carrier with multiplication. -/
@[simp]
theorem smulOverCompletion_self (s t : Completion K) :
    @smulOverCompletion K K _ (inferInstance : SeminormedAddCommGroup K)
      (@NormedField.toNormedSpace K _) s t = s * t := by
  refine induction_on₂ s t (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k l
  simp only [smulOverCompletion_coe_coe, ← coe_mul, smul_eq_mul]

/-- Completing the usual original self-action gives the usual completed self-action as ordinary
normed-space data, with the existing completed normed field as parent. -/
theorem normedSpaceOverCompletion_self :
    @normedSpaceOverCompletion K K _ (inferInstance : SeminormedAddCommGroup K)
      (@NormedField.toNormedSpace K _) =
      @NormedField.toNormedSpace (Completion K) _ := by
  ext s t
  exact smulOverCompletion_self K s t

end UniformSpace.Completion

namespace ContinuousLinearMap

open UniformSpace.Completion

variable {K : Type uK} {A : Type uA} {G : Type uG}
variable [kK : NormedField K] [sA : SeminormedAddCommGroup A] [sG : SeminormedAddCommGroup G]
variable [nA : @NormedSpace K A kK sA] [nG : @NormedSpace K G kK sG]

private theorem completion_smulOverCompletion
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule)
    (s : Completion K) (x : Completion A) :
    T.completion (smulOverCompletion K A s x) =
      smulOverCompletion K G s (T.completion x) := by
  refine induction_on₂ s x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro k a
  simp only [smulOverCompletion_coe_coe, completion_apply_coe, map_smul]

/-- The usual completed continuous linear map, now linear over the completed field. The two
completed module structures come from their respective given original actions. -/
def completionOverCompletion
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    @ContinuousLinearMap (Completion K) (Completion K) _ _ (RingHom.id (Completion K))
      (Completion A) _ _ (Completion G) _ _
      (normedSpaceOverCompletion K A).toModule (normedSpaceOverCompletion K G).toModule := by
  letI := normedSpaceOverCompletion K A
  letI := normedSpaceOverCompletion K G
  exact
    { toFun := T.completion
      map_add' := T.completion.map_add
      map_smul' := by exact completion_smulOverCompletion T
      cont := T.completion.continuous }

/-- Promotion to completed scalars leaves the stock completed map's function unchanged. -/
@[simp]
theorem coe_completionOverCompletion
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    ⇑(completionOverCompletion T) = ⇑T.completion := rfl

/-- The promoted map extends the original map on the dense original image. -/
@[simp]
theorem completionOverCompletion_apply_coe
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule)
    (a : A) : completionOverCompletion T (a : Completion A) = (T a : G) :=
  T.completion_apply_coe a

/-- Completed-scalar linear maps have compatible original-scalar actions, using the two
separately specified scalar towers. -/
theorem compatibleSMulOverCompletion :
    @LinearMap.CompatibleSMul (Completion A) (Completion G) _ _ K (Completion K) _
      (inferInstance : SMul K (Completion A)) (normedSpaceOverCompletion K A).toModule
      (inferInstance : SMul K (Completion G)) (normedSpaceOverCompletion K G).toModule := by
  let := normedSpaceOverCompletion K A
  let := normedSpaceOverCompletion K G
  let := isScalarTowerOverCompletion K A
  let := isScalarTowerOverCompletion K G
  infer_instance

/-- Restricting the promoted map to the original scalar field gives exactly the stock completion
map, with its existing original-scalar module structures. -/
@[simp]
theorem completionOverCompletion_restrictScalars
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    @ContinuousLinearMap.restrictScalars (Completion K) (Completion A) (Completion G) K _ _
      _ (normedSpaceOverCompletion K A).toModule (inferInstance : Module K (Completion A)) _
      _ (normedSpaceOverCompletion K G).toModule (inferInstance : Module K (Completion G)) _
      (compatibleSMulOverCompletion (K := K) (A := A) (G := G))
      (completionOverCompletion T) = T.completion := by
  ext x
  rfl

/-- A completed-scalar continuous linear map is determined by its values on the original space. -/
theorem completionOverCompletion_unique
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule)
    (S : @ContinuousLinearMap (Completion K) (Completion K) _ _ (RingHom.id (Completion K))
      (Completion A) _ _ (Completion G) _ _
      (normedSpaceOverCompletion K A).toModule (normedSpaceOverCompletion K G).toModule)
    (h : ∀ a : A, S (a : Completion A) = (T a : G)) :
    S = completionOverCompletion T := by
  let := normedSpaceOverCompletion K A
  let := normedSpaceOverCompletion K G
  apply DFunLike.ext S (completionOverCompletion T)
  exact Completion.ext' S.continuous (completionOverCompletion T).continuous
    (fun a => (h a).trans (completionOverCompletion_apply_coe T a).symm)

/-- Scalar promotion of completion preserves the identity map. -/
@[simp]
theorem completionOverCompletion_id :
    completionOverCompletion (ContinuousLinearMap.id K A) =
      @ContinuousLinearMap.id (Completion K) _ (Completion A) _ _
        (normedSpaceOverCompletion K A).toModule := by
  symm
  apply completionOverCompletion_unique
  intro a
  rfl

/-- Scalar promotion of completion preserves composition, with an independently universed target. -/
@[simp]
theorem completionOverCompletion_comp {H : Type uH} [sH : SeminormedAddCommGroup H]
    [nH : @NormedSpace K H kK sH]
    (U : @ContinuousLinearMap K K _ _ (RingHom.id K)
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid
      H sH.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sH.toAddCommGroup.toAddCommMonoid nG.toModule nH.toModule)
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    completionOverCompletion (U.comp T) =
      @ContinuousLinearMap.comp (Completion K) (Completion K) (Completion K) _ _ _
        (RingHom.id _) (RingHom.id _) (RingHom.id _)
        (Completion A) _ _ (Completion G) _ _ (Completion H) _ _
        (normedSpaceOverCompletion K A).toModule (normedSpaceOverCompletion K G).toModule
        (normedSpaceOverCompletion K H).toModule RingHomCompTriple.ids
        (completionOverCompletion U) (completionOverCompletion T) := by
  symm
  apply completionOverCompletion_unique
  intro a
  simp only [comp_apply, completionOverCompletion_apply_coe]

end ContinuousLinearMap

namespace UniformSpace.Completion

/-- The completed field is nontrivially normed when the original field is. This named structure
has the existing completed normed field as its definitional parent and is not an instance. -/
@[instance_reducible]
def nontriviallyNormedField (K : Type uK) [NontriviallyNormedField K] :
    NontriviallyNormedField (Completion K) where
  toNormedField := inferInstance
  non_trivial := by
    obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
    exact ⟨(k : Completion K), by simpa only [norm_coe] using hk⟩

/-- The named nontrivial completed-field structure retains the existing normed field. -/
@[simp]
theorem nontriviallyNormedField_toNormedField (K : Type uK) [NontriviallyNormedField K] :
    (nontriviallyNormedField K).toNormedField =
      (inferInstance : NormedField (Completion K)) := rfl

end UniformSpace.Completion

namespace ContinuousLinearMap

open UniformSpace.Completion

variable {K : Type uK} {A : Type uA} {G : Type uG}
variable [kK : NontriviallyNormedField K]
variable [sA : SeminormedAddCommGroup A] [sG : SeminormedAddCommGroup G]
variable [nA : @NormedSpace K A kK.toNormedField sA]
variable [nG : @NormedSpace K G kK.toNormedField sG]

/-- Promotion to the completed scalar field preserves the original operator norm. The norm uses
the named nontrivial completed field and the two named completed normed-space structures. -/
@[simp]
theorem norm_completionOverCompletion
    (T : @ContinuousLinearMap K K _ _ (RingHom.id K)
      A sA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sA.toAddCommGroup.toAddCommMonoid
      G sG.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      sG.toAddCommGroup.toAddCommMonoid nA.toModule nG.toModule) :
    @Norm.norm _
      (@ContinuousLinearMap.hasOpNorm (Completion K) (Completion K) (Completion A) (Completion G)
        _ _ (nontriviallyNormedField K) (nontriviallyNormedField K)
        (normedSpaceOverCompletion K A) (normedSpaceOverCompletion K G) (RingHom.id _))
      (completionOverCompletion T) = ‖T‖ := by
  change ‖T.completion‖ = ‖T‖
  exact T.norm_completion

end ContinuousLinearMap
