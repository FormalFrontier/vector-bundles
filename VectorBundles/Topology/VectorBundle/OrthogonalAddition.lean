/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Topology.VectorBundle.OrthogonalComplement
public import Mathlib.Topology.VectorBundle.Constructions
import VectorBundles.Topology.VectorBundle.Isomorphism
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Addition of an intrinsic subbundle and its orthogonal complement

A supplied continuous Hermitian metric determines the orthogonal family of an
embedded intrinsic submodule bundle. Addition is the prescribed forward function
from the total space of their fiberwise product to the original ambient total space.
The complement has its original fiber subtype topologies and ambient-induced total
topology. The product uses Mathlib's fiberwise-product total topology: the topology
induced by the equal-base inclusion into the product of the two total spaces.
In particular, the intrinsic topology on the first summand is retained, not replaced.

Only the ambient model is assumed finite-dimensional. The subbundle model is
finite-dimensional at any base point, by `VectorBundle.finiteDimensional_of_submodule`;
there is no restriction on that model when the base is empty. No base separation,
paracompactness, model inner product, projection, or adapted chart is assumed.

## Implementation notes

Fiberwise bijectivity uses Mathlib's orthogonal-complement and complementary-submodule
product equivalences. Continuity of addition is checked in the original ambient
bundle charts. Inverse continuity follows from the finite-source fiberwise linear
isomorphism criterion, deriving model finiteness at each target point rather than
assuming a nonempty base or a finite-dimensional subbundle model globally.

This is the given-metric decomposition assertion. The paracompact-base complement
assertion of Proposition 1.3 and the stable-triviality assertion of Proposition 1.4
are not stated here. Projection formulas and isometric trivializations are not supplied.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.3, p. 12. The assertion here isolates addition for a given metric
  and generalizes the scalar field to `RCLike`.
* Mathlib's fiberwise-product bundle topology and vector-bundle constructions,
  by Floris van Doorn and Heather Macbeth, and its orthogonal-complement and
  complementary-submodule product equivalences.
-/

@[expose] public section

open Bundle

namespace Bundle.ContinuousHermitianMetric

universe u𝕜 uB uF uG uE

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]

local notation "C" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g b)) (S b))
local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))
local notation "tC" => TopologicalSpace.induced
  (fun p : TotalSpace H C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance
local notation "tProd" => @FiberBundle.Prod.topologicalSpace B G (fun b ↦ S b) H C
  inferInstance tC

/-- A submodule and its orthogonal family for a supplied Hermitian metric are
algebraic complements in each fiber of a finite-rank ambient vector bundle. -/
theorem orthogonal_isCompl [FiniteDimensional 𝕜 F] (b : B) :
    IsCompl (S b) (C b) := by
  let := VectorBundle.finiteDimensional 𝕜 F E b
  -- The metric norm is used only for this algebraic complement calculation.
  let : NormedAddCommGroup (E b) := (g.toHermitianMetric.toCore b).toNormedAddCommGroup
  let : InnerProductSpace 𝕜 (E b) :=
    .ofCore (g.toHermitianMetric.toCore b).toCore
  have hc : C b = (S b).orthogonal := Submodule.orthogonalBilin_innerSL (S b)
  rw [hc]
  exact (S b).isCompl_orthogonal

private noncomputable def orthogonalAdditionLinearEquiv [FiniteDimensional 𝕜 F] (b : B) :
    (S b × C b) ≃ₗ[𝕜] E b :=
  (S b).prodEquivOfIsCompl (C b) (orthogonal_isCompl g S b)

omit [TopologicalSpace (TotalSpace G (fun b ↦ S b))] in
private theorem orthogonalAddition_bijective [FiniteDimensional 𝕜 F] :
    Function.Bijective (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' F p.proj ((p.2.1 : E p.proj) + (p.2.2 : E p.proj))) := by
  constructor
  · rintro ⟨b, v⟩ ⟨b', w⟩ h
    have hb : b = b' := congrArg TotalSpace.proj h
    subst b'
    apply congrArg (TotalSpace.mk' (G × H) b)
    exact (orthogonalAdditionLinearEquiv g S b).injective (TotalSpace.mk_inj.mp h)
  · rintro ⟨b, v⟩
    obtain ⟨w, hw⟩ := (orthogonalAdditionLinearEquiv g S b).surjective v
    exact ⟨⟨b, w⟩, congrArg (TotalSpace.mk' F b) hw⟩

private theorem continuous_orthogonalAddition
    (hS : Topology.IsEmbedding
      (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj))) :
    @Continuous (TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C)) (TotalSpace F E)
      tProd inferInstance
      (fun p ↦ TotalSpace.mk' F p.proj ((p.2.1 : E p.proj) + (p.2.2 : E p.proj))) := by
  let : TopologicalSpace (TotalSpace H C) := tC
  let : TopologicalSpace (TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C)) := tProd
  have hdiag := (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous
  have hs : Continuous (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' F p.proj (p.2.1 : E p.proj)) := hS.continuous.comp hdiag.fst
  have hj : Topology.IsInducing (fun p : TotalSpace H C ↦
      TotalSpace.mk' F p.proj (p.2 : E p.proj)) := ⟨rfl⟩
  have hc : Continuous (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
      TotalSpace.mk' F p.proj (p.2.2 : E p.proj)) := hj.continuous.comp hdiag.snd
  have hp : Continuous (π (G × H) ((fun b ↦ S b) ×ᵇ C)) :=
    (FiberBundle.continuous_proj F E).comp hs
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  let e := trivializationAt F E p₀.proj
  have he : p₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p₀.proj
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hp.continuousAt, ?_⟩
  have hsc := (e.continuousAt (e.mem_source.mpr he)).comp hs.continuousAt
  have hcc := (e.continuousAt (e.mem_source.mpr he)).comp hc.continuousAt
  apply (hsc.snd.add hcc.snd).congr_of_eventuallyEq
  filter_upwards [hp.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with p hb
  change p.proj ∈ e.baseSet at hb
  change (e ⟨p.proj, (p.2.1 : E p.proj) + (p.2.2 : E p.proj)⟩).2 =
    (e ⟨p.proj, (p.2.1 : E p.proj)⟩).2 + (e ⟨p.proj, (p.2.2 : E p.proj)⟩).2
  simpa only [Trivialization.linearMapAt_apply, ite_eq_left hb] using
    (e.linearMapAt 𝕜 p.proj).map_add (p.2.1 : E p.proj) (p.2.2 : E p.proj)

/-- Addition identifies the fiberwise product of an embedded intrinsic submodule
bundle and its metric orthogonal family with the ambient total space. The domain
has Mathlib's fiberwise-product total topology, using the given intrinsic topology
on the submodule bundle and the ambient-induced topology on the orthogonal family.
The target retains the original ambient topology.

The forward function sends `(b, (s, c))` to `(b, s + c)`. This is the given-metric
addition assertion from Hatcher's Proposition 1.3, over `RCLike` scalars. -/
noncomputable def orthogonalAdditionHomeomorph [FiniteDimensional 𝕜 F]
    [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
    (hS : Topology.IsEmbedding
      (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj))) :
    @Homeomorph (TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C)) (TotalSpace F E)
      tProd inferInstance := by
  letI : TopologicalSpace (TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C)) := tProd
  exact
    { toEquiv := Equiv.ofBijective
        (fun p ↦ TotalSpace.mk' F p.proj ((p.2.1 : E p.proj) + (p.2.2 : E p.proj)))
        (by exact orthogonalAddition_bijective g S)
      continuous_toFun := by exact continuous_orthogonalAddition g S hS
      continuous_invFun := by
        let : TopologicalSpace (TotalSpace H C) := tC
        let o := g.orthogonalBundle S hS
        let : FiberBundle H C := o.1
        let : VectorBundle 𝕜 H C := o.2
        let e := orthogonalAdditionLinearEquiv g S
        have ht : Continuous (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
            (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)) :=
          continuous_orthogonalAddition g S hS
        have hi : Continuous (fun p : TotalSpace F E ↦
            (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C))) := by
          refine continuous_iff_continuousAt.2 fun p ↦ ?_
          -- A target point supplies model finiteness; the empty base is vacuous.
          let : FiniteDimensional 𝕜 G :=
            VectorBundle.finiteDimensional_of_submodule (F := F) S p.proj
          exact (VectorBundle.continuous_totalSpace_symm e ht).continuousAt
        apply hi.congr
        intro p
        apply (orthogonalAddition_bijective g S).injective
        change (⟨p.proj, e p.proj ((e p.proj).symm p.2)⟩ : TotalSpace F E) = _
        rw [(e p.proj).apply_symm_apply]
        exact ((Equiv.ofBijective _ (orthogonalAddition_bijective g S)).apply_symm_apply p).symm }

variable [FiniteDimensional 𝕜 F]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
  (hS : Topology.IsEmbedding
    (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))

/-- The orthogonal-addition homeomorphism has the prescribed addition function. -/
@[simp]
theorem orthogonalAdditionHomeomorph_apply
    (p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C)) :
    g.orthogonalAdditionHomeomorph S hS p =
      TotalSpace.mk' F p.proj ((p.2.1 : E p.proj) + (p.2.2 : E p.proj)) := rfl

end Bundle.ContinuousHermitianMetric
