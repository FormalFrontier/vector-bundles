/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import VectorBundles.Topology.VectorBundle.CoordinateMap
import VectorBundles.Topology.VectorBundle.Embedding
public import VectorBundles.Analysis.Normed.Ring.Units

/-!
# Homeomorphisms from fiberwise linear equivalences

A family of algebraic linear equivalences between two vector bundles over the same base induces a
homeomorphism of total spaces as soon as its forward total-space map is continuous, provided the
source model is finite dimensional over a nontrivially normed field and the target model has the
module topology. In particular, this holds over a complete nontrivially normed field.

The resulting `Homeomorph` preserves the base point and restricts to the supplied linear equivalence
on each fiber. No separate structure for bundle isomorphisms is introduced.

## Implementation notes

Only the source model is assumed finite dimensional: at each base point the two trivializations and
the given fiber equivalence identify the target model with the source model. No nonemptiness or
separation hypothesis on the base is required, and zero-dimensional fibers are permitted.
The target chart identifies its model with the range of the given fiber equivalence, equipped
with the original target-fiber subtype topology. The model's module topology therefore gives this
range its module topology. The bundle embedding criterion applies to the forward total-space map;
composing the inverse total-space map with this embedding gives the identity, proving continuity.
Completeness of the scalar field is needed only to recover the module-topology hypothesis for
finite-dimensional normed models at a given base point.

The coordinate and module-topology arguments use Mathlib's vector-bundle APIs by Nicolò Cavalleri,
Sébastien Gouëzel, Heather Macbeth, Patrick Massot and Floris van Doorn, and its module-topology API
by Kevin Buzzard and Will Sawin.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, Lemma 1.1, printed p. 8.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂

open Bundle

namespace VectorBundle

/-- The inverse total-space map of a continuous family of fiberwise algebraic linear equivalences
is continuous when the source model is finite dimensional and the given target model has the
module topology. No scalar completeness or source module-topology hypothesis is imposed.

This generalizes the inverse-continuity assertion in Hatcher, *Vector Bundles and K-Theory*,
Lemma 1.1. The model norms, fiber topologies and bundle dictionaries are unchanged. -/
theorem continuous_totalSpace_symm_of_isModuleTopology
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [FiniteDimensional 𝕜 F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [IsModuleTopology 𝕜 F₂]
    {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
    [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
    [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
    [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    Continuous (fun p : TotalSpace F₂ E₂ =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace F₁ E₁)) := by
  classical
  let φ : ∀ b, E₁ b →ₗ[𝕜] E₂ b := fun b => (e b).toLinearMap
  let : ∀ b, IsModuleTopology 𝕜 (φ b).range := fun b => by
    let c := VectorBundle.continuousLinearEquivAt 𝕜 F₂ E₂ b
    have hmem (v : F₂) : c.symm v ∈ (φ b).range :=
      ⟨(e b).symm (c.symm v), (e b).apply_symm_apply (c.symm v)⟩
    let d : F₂ ≃L[𝕜] (φ b).range :=
      { toLinearEquiv :=
          { toFun := fun v => ⟨c.symm v, hmem v⟩
            invFun := fun v => c v.1
            left_inv := fun v => c.apply_symm_apply v
            right_inv := fun v => Subtype.ext (c.symm_apply_apply v.1)
            map_add' := fun v w => Subtype.ext (map_add c.symm v w)
            map_smul' := fun a v => Subtype.ext (map_smul c.symm a v) }
        continuous_toFun := c.symm.continuous.subtype_mk hmem
        continuous_invFun := c.continuous.comp continuous_subtype_val }
    exact IsModuleTopology.iso d
  have hPhi : Topology.IsEmbedding (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂)) :=
    isEmbedding_of_injective (F := F₁) (G := F₂) φ (fun b => (e b).injective) htotal
  apply hPhi.continuous_iff.mpr
  refine (continuous_id : Continuous (id : TotalSpace F₂ E₂ → TotalSpace F₂ E₂)).congr ?_
  rintro ⟨b, v⟩
  simp only [Function.comp_def, LinearEquiv.apply_symm_apply, id_eq]

section CompleteField

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
  {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The inverse total-space map of a continuous family of fiberwise algebraic linear equivalences
is continuous when the source model is finite dimensional over a complete nontrivially normed field.

This is the inverse-continuity assertion in Hatcher, *Vector Bundles and K-Theory*, Lemma 1.1.
Continuity of the inverse family, including continuity in the base variable, is a conclusion rather
than a hypothesis. -/
theorem continuous_totalSpace_symm
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    Continuous (fun p : TotalSpace F₂ E₂ =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace F₁ E₁)) := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  let c₁ := trivializationAt F₁ E₁ p₀.proj
  let c₂ := trivializationAt F₂ E₂ p₀.proj
  have hb₁ : p₀.proj ∈ c₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
  have hb₂ : p₀.proj ∈ c₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
  let a₀ : F₁ ≃ₗ[𝕜] F₂ :=
    (((c₁.linearEquivAt 𝕜 p₀.proj hb₁).symm.trans (e p₀.proj)).trans
      (c₂.linearEquivAt 𝕜 p₀.proj hb₂))
  let : FiniteDimensional 𝕜 F₂ := a₀.finiteDimensional
  let : IsModuleTopology 𝕜 F₂ := isModuleTopologyOfFiniteDimensional
  exact (continuous_totalSpace_symm_of_isModuleTopology
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).continuousAt

/-- A continuous fiberwise algebraic linear equivalence of finite-rank vector bundles over the same
base, packaged as a homeomorphism of total spaces.

The forward map acts by `e b` on the fiber over `b`, and the inverse acts by `(e b).symm`. Thus both
maps preserve the base point. This gives the bundle isomorphism of Hatcher, *Vector Bundles and
K-Theory*, Lemma 1.1, without introducing an additional bundle-isomorphism structure. -/
noncomputable def homeomorphOfFiberwiseLinearEquiv
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := congrArg (TotalSpace.mk' F₁ p.proj) ((e p.proj).symm_apply_apply p.2)
  right_inv p := congrArg (TotalSpace.mk' F₂ p.proj) ((e p.proj).apply_symm_apply p.2)
  continuous_toFun := htotal
  continuous_invFun := continuous_totalSpace_symm e htotal

variable (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
  (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
    (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂)))

/-- The total-space homeomorphism acts by the supplied linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquiv_apply (p : TotalSpace F₁ E₁) :
    homeomorphOfFiberwiseLinearEquiv e htotal p = ⟨p.proj, e p.proj p.2⟩ := rfl

/-- The inverse total-space homeomorphism acts by the inverse linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquiv_symm_apply (p : TotalSpace F₂ E₂) :
    (homeomorphOfFiberwiseLinearEquiv e htotal).symm p =
      ⟨p.proj, (e p.proj).symm p.2⟩ := rfl

/-- The forward total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquiv_apply_proj (p : TotalSpace F₁ E₁) :
    (homeomorphOfFiberwiseLinearEquiv e htotal p).proj = p.proj := rfl

/-- The inverse total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquiv_symm_apply_proj (p : TotalSpace F₂ E₂) :
    ((homeomorphOfFiberwiseLinearEquiv e htotal).symm p).proj = p.proj := rfl

end CompleteField

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
  {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [IsModuleTopology 𝕜 F₂]
  {E₁ : B → Type uE₁} {E₂ : B → Type uE₂}
  [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- A continuous fiberwise algebraic linear equivalence over the same base, packaged as a
homeomorphism of total spaces when the source model is finite dimensional and the given target
model has the module topology.

The maps are those of Hatcher, *Vector Bundles and K-Theory*, Lemma 1.1: the forward map acts by
`e b` on each fiber and the inverse acts by `(e b).symm`. Both preserve the base point. -/
noncomputable def homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
    (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
    (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂))) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := congrArg (TotalSpace.mk' F₁ p.proj) ((e p.proj).symm_apply_apply p.2)
  right_inv p := congrArg (TotalSpace.mk' F₂ p.proj) ((e p.proj).apply_symm_apply p.2)
  continuous_toFun := htotal
  continuous_invFun := continuous_totalSpace_symm_of_isModuleTopology
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal

variable (e : ∀ b, E₁ b ≃ₗ[𝕜] E₂ b)
  (htotal : Continuous (fun p : TotalSpace F₁ E₁ =>
    (⟨p.proj, e p.proj p.2⟩ : TotalSpace F₂ E₂)))

/-- The total-space homeomorphism acts by the supplied linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_apply (p : TotalSpace F₁ E₁) :
    homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal p =
        ⟨p.proj, e p.proj p.2⟩ := rfl

/-- The inverse total-space homeomorphism acts by the inverse linear equivalence on each fiber. -/
@[simp]
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_symm_apply (p : TotalSpace F₂ E₂) :
    (homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).symm p =
        ⟨p.proj, (e p.proj).symm p.2⟩ := rfl

/-- The forward total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_apply_proj (p : TotalSpace F₁ E₁) :
    (homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal p).proj =
        p.proj := rfl

/-- The inverse total-space homeomorphism preserves the base point. -/
theorem homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_symm_apply_proj (p : TotalSpace F₂ E₂) :
    ((homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) e htotal).symm p).proj =
        p.proj := rfl

end VectorBundle
