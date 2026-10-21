/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.Isomorphism
public import VectorBundles.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Product-bundle examples for fiberwise linear isomorphisms

The product rank-two identity and the line-bundle map `(b, v) ↦ (b, exp b * v)` satisfy the forward
continuity hypothesis. The zero-dimensional model and the empty base are allowed; over the empty
base the two model spaces need not even have the same dimension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public section

universe uB

open Bundle

namespace VectorBundleIsomorphismTests

noncomputable section

section ProductIdentity

variable {B : Type uB} [TopologicalSpace B]

-- A standard positive-rank product bundle over an arbitrary topological base.
private def productPlaneHomeomorph :
    TotalSpace (Fin 2 → ℝ) (Trivial B (Fin 2 → ℝ)) ≃ₜ
      TotalSpace (Fin 2 → ℝ) (Trivial B (Fin 2 → ℝ)) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquiv (𝕜 := ℝ)
    (fun _ => LinearEquiv.refl ℝ (Fin 2 → ℝ)) continuous_id

-- Rank zero does not require a nontrivial model space or a nonempty base.
private def productZeroHomeomorph :
    TotalSpace (Fin 0 → ℝ) (Trivial B (Fin 0 → ℝ)) ≃ₜ
      TotalSpace (Fin 0 → ℝ) (Trivial B (Fin 0 → ℝ)) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquiv (𝕜 := ℝ)
    (fun _ => LinearEquiv.refl ℝ (Fin 0 → ℝ)) continuous_id

end ProductIdentity

section VaryingScalar

private def expEquiv (b : ℝ) : Trivial ℝ ℝ b ≃ₗ[ℝ] Trivial ℝ ℝ b :=
  LinearEquiv.smulOfNeZero ℝ ℝ (Real.exp b) (Real.exp_ne_zero b)

private theorem continuous_expTotal :
    Continuous (fun p : TotalSpace ℝ (Trivial ℝ ℝ) =>
      (⟨p.proj, expEquiv p.proj p.2⟩ : TotalSpace ℝ (Trivial ℝ ℝ))) := by
  have hproj : Continuous (fun p : TotalSpace ℝ (Trivial ℝ ℝ) => p.proj) :=
    (Trivial.homeomorphProd ℝ ℝ).continuous.fst
  have hsnd : Continuous (fun p : TotalSpace ℝ (Trivial ℝ ℝ) => p.2) :=
    (Trivial.homeomorphProd ℝ ℝ).continuous.snd
  change Continuous ((Trivial.homeomorphProd ℝ ℝ).symm ∘
    fun p : TotalSpace ℝ (Trivial ℝ ℝ) => (p.proj, Real.exp p.proj * p.2))
  exact (Trivial.homeomorphProd ℝ ℝ).symm.continuous.comp
    (hproj.prodMk ((Real.continuous_exp.comp hproj).mul hsnd))

private def expBundleHomeomorphAux :
    TotalSpace ℝ (Trivial ℝ ℝ) ≃ₜ TotalSpace ℝ (Trivial ℝ ℝ) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquiv expEquiv continuous_expTotal

-- The constructor packages a genuinely base-dependent, nonidentity fiber map.
private theorem expBundleHomeomorphAux_apply (b v : ℝ) :
    expBundleHomeomorphAux ⟨b, v⟩ = ⟨b, Real.exp b * v⟩ := by
  simp [expBundleHomeomorphAux, expEquiv, smul_eq_mul]

-- Only forward continuity was supplied; the theorem gives inverse total-space continuity.
private theorem continuous_expTotal_symm :
    Continuous (fun p : TotalSpace ℝ (Trivial ℝ ℝ) =>
      (⟨p.proj, (expEquiv p.proj).symm p.2⟩ : TotalSpace ℝ (Trivial ℝ ℝ))) :=
  VectorBundle.continuous_totalSpace_symm expEquiv continuous_expTotal

/-- A real line-bundle homeomorphism given by exponential fiber scaling. -/
@[no_expose]
def expBundleHomeomorph :
    TotalSpace ℝ (Trivial ℝ ℝ) ≃ₜ TotalSpace ℝ (Trivial ℝ ℝ) :=
  expBundleHomeomorphAux

/-- The constructor packages a genuinely base-dependent, nonidentity fiber map. -/
theorem expBundleHomeomorph_apply (b v : ℝ) :
    expBundleHomeomorph ⟨b, v⟩ = ⟨b, Real.exp b * v⟩ :=
  expBundleHomeomorphAux_apply b v

end VaryingScalar

-- The empty-base case deliberately uses source rank zero and target rank one.
private def emptyZeroLineHomeomorph :
    TotalSpace (Fin 0 → ℝ) (Trivial Empty (Fin 0 → ℝ)) ≃ₜ
      TotalSpace ℝ (Trivial Empty ℝ) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquiv (𝕜 := ℝ)
    (fun b => nomatch b)
    (continuous_iff_continuousAt.mpr fun p => nomatch p.proj)

end

end VectorBundleIsomorphismTests

/-!
## A rational rank-two shear

The base and scalar field are `ℚ` with their usual topology, and the model `ℚ × ℚ` has its
usual product norm. The finite-dimensional and module-topology instances come from the scalar
and product instances. The fiber map `(x, y) ↦ (x + b * y, y)` varies with the base point `b`.

The algebraic family and its forward total-space continuity are the inputs for the total-space
homeomorphism construction. The expected forward formula is `(b, (x, y)) ↦ (b, (x + b * y, y))`,
and the algebraic inverse formula is `(b, (x, y)) ↦ (b, (x - b * y, y))`. Only forward continuity
is supplied to the constructor; the target module topology gives inverse continuity over the
incomplete field `ℚ`. The units examples also recover continuity of a unit-valued map from continuity
of its value, and apply the value embedding to the rational plane and rank-zero endomorphism rings.
-/

namespace VectorBundleIsomorphismTests

noncomputable section

section RationalShear

-- Use the stock trivial-bundle dictionaries for the total space and its bundle structures.
local instance : TopologicalSpace (TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ))) :=
  Trivial.topologicalSpace ℚ (ℚ × ℚ)

local instance : FiberBundle (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) :=
  Trivial.fiberBundle ℚ (ℚ × ℚ)

local instance : VectorBundle ℚ (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) :=
  Trivial.vectorBundle ℚ ℚ (ℚ × ℚ)

private def rationalShearEquiv (b : ℚ) :
    Trivial ℚ (ℚ × ℚ) b ≃ₗ[ℚ] Trivial ℚ (ℚ × ℚ) b where
  toFun v := (v.1 + b * v.2, v.2)
  invFun v := (v.1 - b * v.2, v.2)
  left_inv v := by
    apply Prod.ext <;> simp
  right_inv v := by
    apply Prod.ext <;> simp
  map_add' v w := by
    apply Prod.ext
    · change (v.1 + w.1) + b * (v.2 + w.2) =
        (v.1 + b * v.2) + (w.1 + b * w.2)
      rw [mul_add, add_add_add_comm]
    · rfl
  map_smul' a v := by
    apply Prod.ext
    · change a * v.1 + b * (a * v.2) = a * (v.1 + b * v.2)
      rw [mul_add, mul_left_comm b a v.2]
    · rfl

private theorem rationalShearEquiv_apply (b : ℚ) (v : ℚ × ℚ) :
    rationalShearEquiv b v = (v.1 + b * v.2, v.2) := rfl

private theorem rationalShearEquiv_symm_apply (b : ℚ) (v : ℚ × ℚ) :
    (rationalShearEquiv b).symm v = (v.1 - b * v.2, v.2) := rfl

-- Forward continuity uses only the product coordinates on the trivial bundle.
private theorem continuous_rationalShearTotal :
    Continuous (fun p : TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) =>
      (⟨p.proj, rationalShearEquiv p.proj p.2⟩ :
        TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)))) := by
  have hproj : Continuous (fun p : TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) => p.proj) :=
    (Trivial.homeomorphProd ℚ (ℚ × ℚ)).continuous.fst
  have hsnd : Continuous (fun p : TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) => p.2) :=
    (Trivial.homeomorphProd ℚ (ℚ × ℚ)).continuous.snd
  change Continuous ((Trivial.homeomorphProd ℚ (ℚ × ℚ)).symm ∘
    fun p : TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) =>
      (p.proj, (p.2.1 + p.proj * p.2.2, p.2.2)))
  exact (Trivial.homeomorphProd ℚ (ℚ × ℚ)).symm.continuous.comp
    (hproj.prodMk ((hsnd.fst.add (hproj.mul hsnd.snd)).prodMk hsnd.snd))

-- A nonzero vector is moved nontrivially in the fiber over 1.
private theorem rationalShearEquiv_one :
    rationalShearEquiv 1 (1, 2) = (3, 2) := by
  norm_num [rationalShearEquiv_apply]

-- The image of a fixed vector records the moving coefficient.
private theorem rationalShearEquiv_moving (b : ℚ) :
    rationalShearEquiv b (0, 1) = (b, 1) := by
  simp [rationalShearEquiv_apply]

-- The target module topology and forward continuity give a homeomorphism with continuous inverse,
-- without a separate continuity proof for the explicit inverse formula.
private def rationalShearHomeomorph :
    TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) ≃ₜ
      TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology
    rationalShearEquiv continuous_rationalShearTotal

private theorem continuous_rationalShearTotal_symm :
    Continuous (fun p : TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)) =>
      (⟨p.proj, (rationalShearEquiv p.proj).symm p.2⟩ :
        TotalSpace (ℚ × ℚ) (Trivial ℚ (ℚ × ℚ)))) :=
  VectorBundle.continuous_totalSpace_symm_of_isModuleTopology
    rationalShearEquiv continuous_rationalShearTotal

private theorem rationalShearHomeomorph_apply (b : ℚ) (v : ℚ × ℚ) :
    rationalShearHomeomorph ⟨b, v⟩ = ⟨b, (v.1 + b * v.2, v.2)⟩ := by
  simp only [rationalShearHomeomorph,
    VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_apply,
    rationalShearEquiv_apply]

private theorem rationalShearHomeomorph_symm_apply (b : ℚ) (v : ℚ × ℚ) :
    rationalShearHomeomorph.symm ⟨b, v⟩ = ⟨b, (v.1 - b * v.2, v.2)⟩ := by
  simp only [rationalShearHomeomorph,
    VectorBundle.homeomorphOfFiberwiseLinearEquivOfIsModuleTopology_symm_apply,
    rationalShearEquiv_symm_apply]

-- The returned homeomorphism moves a nonzero vector, not just an algebraic witness.
private theorem rationalShearHomeomorph_one :
    rationalShearHomeomorph ⟨1, (1, 2)⟩ = ⟨1, (3, 2)⟩ := by
  rw [rationalShearHomeomorph_apply]
  norm_num

private theorem rationalShearHomeomorph_moving (b : ℚ) :
    rationalShearHomeomorph ⟨b, (0, 1)⟩ = ⟨b, (b, 1)⟩ := by
  simp [rationalShearHomeomorph_apply]

end RationalShear

section UnitEmbeddings

-- Under summable geometric series, the embedding agrees with the open embedding.
private theorem isEmbedding_units_val_eq_isOpenEmbedding_val
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] :
    Units.isEmbedding_val_seminormedRing (R := R) =
      (Units.isOpenEmbedding_val (R := R)).isEmbedding := by
  apply Subsingleton.elim

-- Forward continuity alone gives continuity into the existing units topology.
private theorem continuous_units_of_continuous_val
    {R : Type*} [SeminormedRing R] {X : Type*} [TopologicalSpace X]
    (f : X → Rˣ) (hf : Continuous (Units.val ∘ f)) : Continuous f :=
  (Units.isEmbedding_val_seminormedRing (R := R)).continuous_iff.mpr hf

private theorem rationalPlaneEnd_isEmbedding_units_val :
    Topology.IsEmbedding (Units.val : ((ℚ × ℚ) →L[ℚ] (ℚ × ℚ))ˣ →
      ((ℚ × ℚ) →L[ℚ] (ℚ × ℚ))) :=
  Units.isEmbedding_val_seminormedRing (R := (ℚ × ℚ) →L[ℚ] (ℚ × ℚ))

-- The zero-dimensional endomorphism ring requires neither Nontrivial nor NormOneClass.
private theorem rationalZeroEnd_isEmbedding_units_val :
    Topology.IsEmbedding (Units.val : ((Fin 0 → ℚ) →L[ℚ] (Fin 0 → ℚ))ˣ →
      ((Fin 0 → ℚ) →L[ℚ] (Fin 0 → ℚ))) :=
  Units.isEmbedding_val_seminormedRing (R := (Fin 0 → ℚ) →L[ℚ] (Fin 0 → ℚ))

end UnitEmbeddings

section EmptyTarget

universe uG

-- The old constructor must not demand finite dimension or a module topology on the target.
private def emptyZeroTargetHomeomorph
    (G : Type uG) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    TotalSpace (Fin 0 → ℝ) (Trivial Empty (Fin 0 → ℝ)) ≃ₜ
      TotalSpace G (Trivial Empty G) :=
  VectorBundle.homeomorphOfFiberwiseLinearEquiv (𝕜 := ℝ)
    (fun b => nomatch b)
    (continuous_iff_continuousAt.mpr fun p => nomatch p.proj)

end EmptyTarget

end

end VectorBundleIsomorphismTests
