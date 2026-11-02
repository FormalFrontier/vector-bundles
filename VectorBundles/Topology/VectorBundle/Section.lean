/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.ContinuousMap.Algebra
public import VectorBundles.Topology.FiberBundle.SeparatedMap

/-!
# Continuous sections of vector bundles

`VectorBundle.continuousSectionSubmodule` is the submodule of dependent functions whose
maps into the total space are continuous. It is also a module over the ring of continuous
scalar functions, acting pointwise on the section subtype. Evaluation is linear over
constant scalars and semilinear over evaluation of scalar functions.

For a trivial bundle, `VectorBundle.continuousSectionTrivialEquiv` identifies this module
with `C(B, F)`, and `VectorBundle.continuousSectionSubmodule_trivial` identifies the
underlying constant-scalar submodule with Mathlib's `continuousSubmodule`.

Only the model fiber is normed; the base is an arbitrary topological space. Neither
finite dimensionality nor completeness is needed. Continuity of scalar multiplication
on the individual fibers is not assumed separately. Scalar functions act on the section
subtype, not on the individual fibers or on the ambient dependent function type.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2, §1.1, motivates sections
  as right inverses. The scalar-function module is a consequence of these definitions.
* Mathlib's vector-bundle trivializations, `FiberBundle.continuousAt_section`, and
  topological support, `continuousSubmodule` and `ContinuousMap` algebra APIs.

## Credits

The section-closure argument is due to Formal Frontier Agents. It checks continuity in a
preferred linear trivialization using Mathlib's `FiberBundle.continuousAt_section`.
The underlying bundle constructions are due to Nicolò Cavalleri, Sébastien Gouëzel,
Heather Macbeth and Floris van Doorn.
-/

@[expose] public section

open Bundle Topology

universe uκ u𝕜 uB uF uE

namespace VectorBundle

/-- A continuous scalar function times a continuous section is a continuous section,
with respect to the given fiber and total-space topologies and bundle structures. -/
theorem continuous_smul_section {κ : Type uκ} [NontriviallyNormedField κ]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace κ F]
    {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle κ F E]
    {c : B → κ} {s : ∀ b, E b}
    (hc : Continuous c) (hs : Continuous (fun b ↦ TotalSpace.mk' F b (s b))) :
    Continuous (fun b ↦ TotalSpace.mk' F b (c b • s b)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [FiberBundle.continuousAt_section]
  have hs' := (FiberBundle.continuousAt_section F x₀).mp hs.continuousAt
  apply (hc.continuousAt.smul hs').congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F E x₀)] with x hx
  exact ((trivializationAt F E x₀).linear κ hx).map_smul (c x) (s x)

end VectorBundle

namespace Bundle.Trivialization

/-- Continuous model-valued coordinates whose closed topological support lies in a
linear chart define a continuous section via its zero-extended linear inverse. -/
theorem continuous_section_symmL_of_tsupport_subset
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (g : B → F) (hcont : Continuous g) (hg : tsupport g ⊆ e.baseSet) :
    Continuous (fun b ↦ TotalSpace.mk' F b (e.symmL 𝕜 b (g b))) := by
  classical
  refine continuous_iff_continuousAt.2 fun b ↦ ?_
  by_cases hb : b ∈ tsupport g
  · have hbe : b ∈ e.baseSet := hg hb
    have hlocal :
        ContinuousOn (fun c ↦ TotalSpace.mk' F c (e.symm c (g c))) e.baseSet :=
      e.continuousOn_symm.comp (continuous_id.prodMk hcont).continuousOn
        (fun c hc ↦ ⟨hc, Set.mem_univ _⟩)
    apply (hlocal.continuousAt (e.open_baseSet.mem_nhds hbe)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hbe] with c hc
    exact congr_arg (TotalSpace.mk' F c) (e.symmL_apply (R := 𝕜) hc (g c))
  · apply (Bundle.Trivialization.continuous_zeroSection (F := F) (E := E)
      𝕜).continuousAt.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hb] with c hc
    have hc0 : g c = (0 : F) := hc
    simp only [Bundle.zeroSection, hc0, map_zero]

end Bundle.Trivialization

namespace VectorBundle

section Closure

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

include 𝕜 in
private theorem continuous_add_section {s t : ∀ x, E x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : Continuous (fun x ↦ TotalSpace.mk' F x (t x))) :
    Continuous (fun x ↦ TotalSpace.mk' F x (s x + t x)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [FiberBundle.continuousAt_section]
  have hs' := (FiberBundle.continuousAt_section F x₀).mp hs.continuousAt
  have ht' := (FiberBundle.continuousAt_section F x₀).mp ht.continuousAt
  apply (hs'.add ht').congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F E x₀)] with x hx
  exact ((trivializationAt F E x₀).linear 𝕜 hx).map_add (s x) (t x)

end Closure

/-- The constant-scalar submodule of dependent sections with continuous total-space graphs.
This generalizes `continuousSubmodule` from a fixed target to a vector bundle. -/
def continuousSectionSubmodule
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
    {B : Type uB} [TopologicalSpace B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type uE) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] : Submodule 𝕜 (∀ x, E x) where
  carrier := {s | Continuous (fun x ↦ TotalSpace.mk' F x (s x))}
  zero_mem' := by exact Bundle.Trivialization.continuous_zeroSection 𝕜
  add_mem' := by exact continuous_add_section (𝕜 := 𝕜)
  smul_mem' a _ hs := by exact continuous_smul_section (continuous_const (y := a)) hs

section Module

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Membership is precisely continuity of the total-space graph. -/
@[simp] theorem mem_continuousSectionSubmodule (s : ∀ x, E x) :
    s ∈ continuousSectionSubmodule 𝕜 F E ↔
      Continuous (fun x ↦ TotalSpace.mk' F x (s x)) := Iff.rfl

/-- A continuous section has a continuous total-space graph. -/
theorem continuous_section (s : continuousSectionSubmodule 𝕜 F E) :
    Continuous (fun x ↦ TotalSpace.mk' F x (s.1 x)) := s.property

/-- Scalar functions act pointwise on the continuous-section subtype. -/
instance continuousSectionSMul : SMul C(B, 𝕜) (continuousSectionSubmodule 𝕜 F E) where
  smul c s := ⟨fun x ↦ c x • s.1 x, by exact continuous_smul_section c.continuous s.property⟩

/-- Continuous sections form a module over continuous scalar functions. -/
instance continuousSectionModule : Module C(B, 𝕜) (continuousSectionSubmodule 𝕜 F E) where
  smul_add c s t := Subtype.ext (funext fun x ↦ smul_add (c x) (s.1 x) (t.1 x))
  add_smul c d s := Subtype.ext (funext fun x ↦ add_smul (c x) (d x) (s.1 x))
  mul_smul c d s := Subtype.ext (funext fun x ↦ mul_smul (c x) (d x) (s.1 x))
  one_smul s := Subtype.ext (funext fun x ↦ one_smul 𝕜 (s.1 x))
  zero_smul s := Subtype.ext (funext fun x ↦ zero_smul 𝕜 (s.1 x))
  smul_zero c := Subtype.ext (funext fun x ↦ smul_zero (c x))

/-- Compatibility of constant scalars with scalar-function multiplication. -/
instance continuousSectionIsScalarTower :
    IsScalarTower 𝕜 C(B, 𝕜) (continuousSectionSubmodule 𝕜 F E) where
  smul_assoc a c s := Subtype.ext (funext fun x ↦ smul_assoc a (c x) (s.1 x))

/-- The constant and function scalar actions commute. -/
instance continuousSectionSMulCommClass :
    SMulCommClass 𝕜 C(B, 𝕜) (continuousSectionSubmodule 𝕜 F E) where
  smul_comm a c s := Subtype.ext (funext fun x ↦ smul_comm a (c x) (s.1 x))

@[simp] theorem continuousSection_zero_apply (x : B) :
    (0 : continuousSectionSubmodule 𝕜 F E).1 x = 0 := rfl

@[simp] theorem continuousSection_add_apply (s t : continuousSectionSubmodule 𝕜 F E) (x : B) :
    (s + t).1 x = s.1 x + t.1 x := rfl

@[simp] theorem continuousSection_const_smul_apply (a : 𝕜)
    (s : continuousSectionSubmodule 𝕜 F E) (x : B) :
    (a • s).1 x = a • s.1 x := rfl

@[simp] theorem continuousSection_smul_apply (c : C(B, 𝕜))
    (s : continuousSectionSubmodule 𝕜 F E) (x : B) :
    (c • s).1 x = c x • s.1 x := rfl

/-- Constant continuous functions recover the inherited scalar action. -/
@[simp] theorem continuousSection_const_smul (a : 𝕜) (s : continuousSectionSubmodule 𝕜 F E) :
    ContinuousMap.const B a • s = a • s := rfl

/-- Evaluation is linear over the constant scalar field. -/
def continuousSectionEval (x : B) : continuousSectionSubmodule 𝕜 F E →ₗ[𝕜] E x where
  toFun s := s.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousSectionEval_apply (x : B) (s : continuousSectionSubmodule 𝕜 F E) :
    continuousSectionEval x s = s.1 x := rfl

/-- Evaluation is semilinear over the ring homomorphism underlying scalar-function evaluation. -/
def continuousSectionEvalₛₗ (x : B) :
    (continuousSectionSubmodule 𝕜 F E) →ₛₗ[(ContinuousMap.evalAlgHom 𝕜 𝕜 x : C(B, 𝕜) →+* 𝕜)]
      E x where
  toFun s := s.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousSectionEvalₛₗ_apply (x : B) (s : continuousSectionSubmodule 𝕜 F E) :
    continuousSectionEvalₛₗ x s = s.1 x := rfl

end Module

section Trivial

variable (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
  (B : Type uB) [TopologicalSpace B]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a trivial bundle the section submodule is Mathlib's fixed-target submodule. -/
theorem continuousSectionSubmodule_trivial :
    continuousSectionSubmodule 𝕜 F (Bundle.Trivial B F) = continuousSubmodule B 𝕜 F := by
  ext s
  constructor
  · intro hs
    exact ((Bundle.Trivial.homeomorphProd B F).continuous.comp hs).snd
  · intro hs
    exact (Bundle.Trivial.homeomorphProd B F).symm.continuous.comp
      (continuous_id.prodMk hs)

/-- Sections of a trivial bundle are continuous maps, linearly over scalar functions. -/
noncomputable def continuousSectionTrivialEquiv :
    continuousSectionSubmodule 𝕜 F (Bundle.Trivial B F) ≃ₗ[C(B, 𝕜)] C(B, F) where
  toFun s := ⟨fun x ↦ s.1 x, by
    exact ((continuousSectionSubmodule_trivial 𝕜 B F).le s.property :
      s.1 ∈ continuousSubmodule B 𝕜 F)⟩
  invFun s := ⟨fun x ↦ s x, by
    rw [continuousSectionSubmodule_trivial]
    exact s.continuous⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := ContinuousMap.ext fun _ ↦ rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousSectionTrivialEquiv_apply
    (s : continuousSectionSubmodule 𝕜 F (Bundle.Trivial B F)) (x : B) :
    continuousSectionTrivialEquiv 𝕜 B F s x = s.1 x := rfl

@[simp] theorem continuousSectionTrivialEquiv_symm_apply (s : C(B, F)) (x : B) :
    ((continuousSectionTrivialEquiv 𝕜 B F).symm s).1 x = s x := rfl

end Trivial
end VectorBundle

namespace VectorBundle

section Equalizer

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type uE} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The zero set of a continuous vector-bundle section is closed. -/
theorem isClosed_zero_continuousSection (s : continuousSectionSubmodule 𝕜 F E) :
    IsClosed {b : B | s.1 b = 0} := by
  simpa only [continuousSection_zero_apply] using
    (FiberBundle.isClosed_eq F (continuous_section s)
      (continuous_section (0 : continuousSectionSubmodule 𝕜 F E)))

/-- The set where a continuous vector-bundle section is nonzero is open. -/
theorem isOpen_ne_zero_continuousSection (s : continuousSectionSubmodule 𝕜 F E) :
    IsOpen {b : B | s.1 b ≠ 0} :=
  (isClosed_zero_continuousSection s).isOpen_compl

end Equalizer
end VectorBundle
