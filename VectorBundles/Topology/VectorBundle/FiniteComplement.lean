/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Topology.Separation.Regular

import VectorBundles.Topology.VectorBundle.FiniteEmbedding
import VectorBundles.Topology.VectorBundle.Range
import VectorBundles.Topology.VectorBundle.OrthogonalAddition
import VectorBundles.Topology.VectorBundle.MetricModel
import VectorBundles.Topology.VectorBundle.TrivialMetric

/-!
# Finite complementary vector bundles

A finite-dimensional vector bundle over a compact normal space has a finite-dimensional
complement whose fiberwise product with the original bundle is globally linearly trivial.
The complement is a family of submodules of a finite power of the original model. Its
fibers have their subspace topologies, and its total topology is induced by inclusion in
the product of the base and that finite power. The original bundle is not retopologized.
The submodule realization does not specify an embedding of the original bundle into that
power, or assert orthogonality or complementarity to a prescribed ambient embedding.

`VectorBundle.finiteComplement` returns all the choices together. Its projections in the
namespace `VectorBundle.finiteComplement` give the complement, its bundle structures, and
a global fiberwise-linear trivialization for the fiberwise-product topology.
The target model is the product of the original model and a Euclidean complement model;
it is finite-dimensional, and hence linearly equivalent to a finite scalar power.

## Construction

A finite fiberwise-linear total-space embedding is padded to have a positive number of
model copies. A compatible Hermitian form on that finite power extends constantly over
the base. The orthogonal family to the embedded range gives the complement, and addition
followed by a fixed model equivalence gives the global linear trivialization.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Proposition 1.4, p. 13, using the complement argument of Proposition 1.3, pp. 12–13.
  Here compact normal bases replace compact Hausdorff bases, and the scalars are `RCLike`.
* Mathlib's fiberwise products, linear bundle trivializations, and finite-dimensional
  Euclidean spaces.
-/

@[expose] public section

open Bundle

namespace VectorBundle

universe u𝕜 uB uF uE

variable (𝕜 : Type u𝕜) [RCLike 𝕜]
  {B : Type uB} [TopologicalSpace B]
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type uE)
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)]

local notation "G[" m "]" =>
  EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 (Fin m → F) - Module.finrank 𝕜 F))
local notation "tC[" m ", " C "]" => TopologicalSpace.induced
  (fun p : TotalSpace G[m] (fun b ↦ C b) ↦
    (TotalSpace.proj p, (TotalSpace.snd p : Fin m → F)))
  (inferInstance : TopologicalSpace (B × (Fin m → F)))
local notation "tP[" m ", " C "]" => @FiberBundle.Prod.topologicalSpace B F E G[m]
  (fun b ↦ C b) inferInstance tC[m, C]

/-- Pad a finite trivial-bundle embedding with a zero coordinate so its number of
model copies is positive, even for an empty base or a zero-dimensional model. -/
private noncomputable def positiveFiniteTrivialEmbedding
    [CompactSpace B] [NormalSpace B]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Σ' m : ℕ, Σ' L : (∀ b, E b →ₗ[𝕜] (Fin m → F)),
      { f : C(TotalSpace F E, B × (Fin m → F)) //
          0 < m ∧ Topology.IsEmbedding f ∧
          ∀ b v, f (TotalSpace.mk' F b v) = (b, L b v) } := by
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  obtain ⟨m, L, f, hf, hL⟩ := finiteTrivialEmbedding 𝕜 F E
  let P : (Fin m → F) →ₗ[𝕜] (Fin (m + 1) → F) :=
    LinearMap.pi (Fin.cons 0 (fun i => LinearMap.proj i))
  have hP (v : Fin m → F) : P v = Fin.cons 0 v := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  let pad : C(B × (Fin m → F), B × (Fin (m + 1) → F)) :=
    ⟨fun z => (z.1, Fin.cons 0 z.2),
      continuous_fst.prodMk (continuous_const.finCons continuous_snd)⟩
  have hpad : Topology.IsEmbedding pad := by
    have hleft : Function.LeftInverse
        (fun z : B × (Fin (m + 1) → F) => (z.1, Fin.tail z.2)) pad := by
      intro z
      exact Prod.ext rfl (by ext i; rfl)
    exact hleft.isEmbedding
      (continuous_fst.prodMk continuous_snd.finTail) pad.continuous
  refine ⟨m + 1, (fun b => P.comp (L b)), pad.comp f,
    Nat.succ_pos m, hpad.comp hf, ?_⟩
  intro b v
  change pad (f (TotalSpace.mk' F b v)) = (b, P (L b v))
  rw [hL, hP]
  rfl

/- The following assembly is conditional only on implementation data: a finite total
embedding and a metric on its trivial target. It does not use the public constructor. -/

private theorem finiteComplement_inducedTopology (m : ℕ)
    (C : B → Submodule 𝕜 (Fin m → F)) :
    TopologicalSpace.induced
      (fun p : TotalSpace G[m] (fun b ↦ C b) ↦
        TotalSpace.mk' (Fin m → F) p.proj (p.2 : Fin m → F))
      (inferInstance : TopologicalSpace
        (TotalSpace (Fin m → F) (Trivial B (Fin m → F)))) = tC[m, C] := by
  rw [(Trivial.homeomorphProd B (Fin m → F)).isInducing.eq_induced,
    induced_compose]
  rfl

-- Both products retain the model F × G[m]; only the first fiber is transported.
private noncomputable def finiteComplement_rangeProductHomeomorph (m : ℕ)
    (C : B → Submodule 𝕜 (Fin m → F))
    (L : ∀ b, E b →ₗ[𝕜] (Fin m → F))
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2))) :
    @Homeomorph (TotalSpace (F × G[m]) (E ×ᵇ (fun b ↦ C b)))
      (TotalSpace (F × G[m]) ((fun b ↦ (L b).range) ×ᵇ (fun b ↦ C b)))
      tP[m, C]
      (@FiberBundle.Prod.topologicalSpace B F (fun b ↦ (L b).range) G[m]
        (fun b ↦ C b) (rangeTotalSpaceTopology L) tC[m, C]) := by
  letI := rangeTotalSpaceTopology (F := F) L
  letI : TopologicalSpace (TotalSpace G[m] (fun b ↦ C b)) := tC[m, C]
  let r := imageHomeomorph L hI
  refine
    { toFun := fun p ↦ ⟨p.proj, (rangeLinearEquiv L hI p.proj p.2.1, p.2.2)⟩
      invFun := fun p ↦ ⟨p.proj, ((rangeLinearEquiv L hI p.proj).symm p.2.1, p.2.2)⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rintro ⟨b, v, c⟩
    simp
  · rintro ⟨b, v, c⟩
    simp
  · apply (FiberBundle.Prod.isInducing_diag F (fun b ↦ (L b).range) G[m]
      (fun b ↦ C b)).continuous_iff.mpr
    exact (r.continuous.comp (FiberBundle.Prod.isInducing_diag F E G[m]
      (fun b ↦ C b)).continuous.fst).prodMk
        (FiberBundle.Prod.isInducing_diag F E G[m] (fun b ↦ C b)).continuous.snd
  · apply (FiberBundle.Prod.isInducing_diag F E G[m] (fun b ↦ C b)).continuous_iff.mpr
    exact (r.symm.continuous.comp (FiberBundle.Prod.isInducing_diag F
      (fun b ↦ (L b).range) G[m] (fun b ↦ C b)).continuous.fst).prodMk
        (FiberBundle.Prod.isInducing_diag F (fun b ↦ (L b).range) G[m]
          (fun b ↦ C b)).continuous.snd

-- Positivity gives the rank inequality without selecting a point of the base.
private noncomputable def finiteComplement_ambientEquiv [FiniteDimensional 𝕜 F]
    (m : ℕ) (hm : 0 < m) : (Fin m → F) ≃L[𝕜] (F × G[m]) := by
  apply ContinuousLinearEquiv.ofFinrankEq
  rw [Module.finrank_prod, finrank_euclideanSpace_fin]
  apply (Nat.add_sub_of_le ?_).symm
  simpa [Module.finrank_pi_fintype] using
    Nat.mul_le_mul_right (Module.finrank 𝕜 F) hm

private noncomputable def finiteComplement_globalTrivialization (m : ℕ)
    (C : B → Submodule 𝕜 (Fin m → F))
    (h : @Homeomorph (TotalSpace (F × G[m]) (E ×ᵇ (fun b ↦ C b)))
      (B × (F × G[m])) tP[m, C] inferInstance)
    (hp : ∀ p, (h p).1 = p.proj) :
    @Trivialization B (F × G[m]) _ _ _ tP[m, C]
      (π (F × G[m]) (E ×ᵇ (fun b ↦ C b))) := by
  letI := tP[m, C]
  exact
    { toOpenPartialHomeomorph := h.toOpenPartialHomeomorph
      baseSet := Set.univ
      open_baseSet := isOpen_univ
      source_eq := rfl
      target_eq := Set.univ_prod_univ.symm
      proj_toFun := fun p _ ↦ hp p }

/- Fixed-m assembly of the exact inner constructor result. The complement is the
metric orthogonal of range L, and the resulting chart sends (b, (v, c)) to
(b, ψ (L b v + c)). No nonemptiness, separation, or metric on the original model
is used. -/
private noncomputable def finiteComplementOfEmbedding
    [FiniteDimensional 𝕜 F]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (m : ℕ) (hm : 0 < m)
    (L : ∀ b, E b →ₗ[𝕜] (Fin m → F))
    (hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)))
    (g : Bundle.ContinuousHermitianMetric 𝕜 (Fin m → F) (Trivial B (Fin m → F))) :
    Σ' C : B → Submodule 𝕜 (Fin m → F),
      Σ' fb : @FiberBundle B G[m] _ _ (fun b ↦ C b) tC[m, C] _,
      Σ' _vb : @VectorBundle 𝕜 B G[m] (fun b ↦ C b) _ _ _ _ _ _ tC[m, C] _ fb,
      Σ' e : @Trivialization B (F × G[m]) _ _ _ tP[m, C]
        (π (F × G[m]) (E ×ᵇ (fun b ↦ C b))),
        @Trivialization.baseSet B (F × G[m]) _ _ _ tP[m, C] _ e = Set.univ ∧
        @Trivialization.IsLinear 𝕜 B (F × G[m]) (E ×ᵇ (fun b ↦ C b))
          _ _ _ tP[m, C] _ _ _ _ e := by
  letI := rangeTotalSpaceTopology (F := F) L
  let s := rangeBundle L hI
  letI := s.1
  letI := s.2
  let S := fun b ↦ (L b).range
  have hS : Topology.IsEmbedding (fun p : TotalSpace F (fun b ↦ S b) ↦
      (TotalSpace.mk' (Fin m → F) p.proj (p.2 : Fin m → F) :
        TotalSpace (Fin m → F) (Trivial B (Fin m → F)))) :=
    (Trivial.homeomorphProd B (Fin m → F)).symm.isEmbedding.comp
      (rangeInclusion_isEmbedding (F := F) L)
  let C := fun b ↦ Submodule.orthogonalBilin
    (ContinuousLinearMap.toLinearMap₁₂ (g.inner b)) (S b)
  have ht := finiteComplement_inducedTopology 𝕜 F m C
  let o : Σ' fb : @FiberBundle B G[m] _ _ (fun b ↦ C b) tC[m, C] _,
      @VectorBundle 𝕜 B G[m] (fun b ↦ C b) _ _ _ _ _ _ tC[m, C] _ fb := by
    have o := g.orthogonalBundle S hS
    rw [ht] at o
    exact o
  letI tCA : TopologicalSpace (TotalSpace G[m] (fun b ↦ C b)) :=
    TopologicalSpace.induced
      (fun p : TotalSpace G[m] (fun b ↦ C b) ↦
        TotalSpace.mk' (Fin m → F) p.proj (p.2 : Fin m → F))
      (inferInstance : TopologicalSpace
        (TotalSpace (Fin m → F) (Trivial B (Fin m → F))))
  let a₀ := g.orthogonalAdditionHomeomorph S hS
  let ea := @Homeomorph.toEquiv _ _ _ _ a₀
  -- Transport only the continuity proofs, so the forward function is unchanged.
  have hca := @Homeomorph.continuous_toFun _ _ _ _ a₀
  have hcai := @Homeomorph.continuous_invFun _ _ _ _ a₀
  change @Continuous _ _ _ _ ea at hca
  change @Continuous _ _ _ _ ea.symm at hcai
  -- The product topology uses the same complement topology as the returned bundle data.
  have htP : @FiberBundle.Prod.topologicalSpace B F (fun b ↦ S b) G[m]
      (fun b ↦ C b) inferInstance tCA =
      @FiberBundle.Prod.topologicalSpace B F (fun b ↦ S b) G[m]
        (fun b ↦ C b) inferInstance tC[m, C] :=
    congrArg (fun t ↦ @FiberBundle.Prod.topologicalSpace B F (fun b ↦ S b) G[m]
      (fun b ↦ C b) inferInstance t) ht
  have hca' := Eq.mp (congrArg (fun t ↦ @Continuous _ _ t _ ea) htP) hca
  have hcai' := Eq.mp (congrArg (fun t ↦ @Continuous _ _ _ t ea.symm) htP) hcai
  letI : TopologicalSpace (TotalSpace G[m] (fun b ↦ C b)) := tC[m, C]
  letI := o.1
  letI := o.2
  let a : TotalSpace (F × G[m]) ((fun b ↦ S b) ×ᵇ (fun b ↦ C b)) ≃ₜ
      TotalSpace (Fin m → F) (Trivial B (Fin m → F)) :=
    { toEquiv := ea
      continuous_toFun := hca'
      continuous_invFun := hcai' }
  have ha (p : TotalSpace (F × G[m]) ((fun b ↦ S b) ×ᵇ (fun b ↦ C b))) :
      a p = TotalSpace.mk' (Fin m → F) p.proj
        ((p.2.1 : Fin m → F) + (p.2.2 : Fin m → F)) :=
    g.orthogonalAdditionHomeomorph_apply S hS p
  let ψ := finiteComplement_ambientEquiv 𝕜 F m hm
  let h := ((finiteComplement_rangeProductHomeomorph 𝕜 F E m C L hI).trans a).trans
    ((Trivial.homeomorphProd B (Fin m → F)).trans
      ((Homeomorph.refl B).prodCongr ψ.toHomeomorph))
  have hh (b : B) (v : E b) (c : C b) :
      h (TotalSpace.mk' (F × G[m]) b (v, c)) = (b, ψ (L b v + (c : Fin m → F))) := by
    dsimp only [h, Homeomorph.trans_apply]
    rw [ha]
    rfl
  have hp : ∀ p, (h p).1 = p.proj := by
    rintro ⟨b, v, c⟩
    rw [hh]
  let e := finiteComplement_globalTrivialization 𝕜 F E m C h hp
  refine ⟨C, o.1, o.2, e, rfl, ?_⟩
  constructor
  intro b _
  change IsLinearMap 𝕜 (fun v : E b × C b ↦ (h (TotalSpace.mk' (F × G[m]) b v)).2)
  simpa only [hh, LinearMap.coe_comp, LinearMap.coprod_apply,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    Function.comp_def, Submodule.subtype_apply] using
      (ψ.toLinearMap.comp ((L b).coprod (C b).subtype)).isLinear

/-- A finite complementary bundle and a global linear trivialization of its product
with the given bundle, over a compact normal base. This is the complement conclusion
of Hatcher's Proposition 1.4, generalized from compact Hausdorff bases to compact normal
bases and to `RCLike` scalars.

The complement fibers are the submodules `C b` of `Fin m → F`, with inherited algebra
and subspace topologies. Their total topology is induced by `(b, c) ↦ (b, ↑c)`.
The returned bundle structures and trivialization belong to this same choice of `m`
and `C`. The product total topology is the fiberwise-product topology, and the
trivialization's model is `F × EuclideanSpace 𝕜 (Fin (finrank 𝕜 (Fin m → F) - finrank 𝕜 F))`.
In particular no change of the original fiber or total-space topology is implicit.
The conclusion is linear triviality of `E ×ᵇ C`, not a statement that `C` is orthogonal
to, or complementary to the range of, a prescribed embedding of `E` in `Fin m → F`.

The construction uses a finite embedding, a constant compatible Hermitian metric on its
trivial target, and the orthogonal decomposition of the embedded range. -/
@[no_expose] noncomputable def finiteComplement
    [CompactSpace B] [NormalSpace B] [FiniteDimensional 𝕜 F]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Σ' m : ℕ, Σ' C : B → Submodule 𝕜 (Fin m → F),
      Σ' fb : @FiberBundle B G[m] _ _ (fun b ↦ C b) tC[m, C] _,
      Σ' _vb : @VectorBundle 𝕜 B G[m] (fun b ↦ C b) _ _ _ _ _ _ tC[m, C] _ fb,
      Σ' e : @Trivialization B (F × G[m]) _ _ _ tP[m, C]
        (π (F × G[m]) (E ×ᵇ (fun b ↦ C b))),
        @Trivialization.baseSet B (F × G[m]) _ _ _ tP[m, C] _ e = Set.univ ∧
        @Trivialization.IsLinear 𝕜 B (F × G[m]) (E ×ᵇ (fun b ↦ C b))
          _ _ _ tP[m, C] _ _ _ _ e := by
  obtain ⟨m, L, f, hm, hf, hL⟩ := positiveFiniteTrivialEmbedding 𝕜 F E
  have hI : Topology.IsEmbedding (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)) := by
    have h : (fun p : TotalSpace F E ↦ (p.proj, L p.proj p.2)) =
        (f : TotalSpace F E → B × (Fin m → F)) := by
      funext p
      exact (hL p.proj p.2).symm
    rw [h]
    exact hf
  let g : Bundle.ContinuousHermitianMetric 𝕜 (Fin m → F) (Trivial B (Fin m → F)) :=
    Bundle.ContinuousHermitianMetric.trivialOfHermitianMetric 𝕜 B (Fin m → F)
      (Bundle.HermitianMetric.ofFiniteDimensional 𝕜 (Fin m → F))
  exact ⟨m, finiteComplementOfEmbedding 𝕜 F E m hm L hI g⟩

variable [CompactSpace B] [NormalSpace B] [FiniteDimensional 𝕜 F]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]

namespace finiteComplement

/-- The number of copies of the original model used for the complement's ambient space. -/
noncomputable def count : ℕ := (finiteComplement 𝕜 F E).1

/-- The chosen family of complementary submodules of a finite power of the model. -/
noncomputable def submodule (b : B) : Submodule 𝕜 (Fin (count 𝕜 F E) → F) :=
  (finiteComplement 𝕜 F E).2.1 b

/-- The fixed finite-dimensional model of the complementary bundle. -/
noncomputable abbrev model : Type u𝕜 := G[count 𝕜 F E]

/-- The fibers of the complementary bundle, with their submodule algebra and topology. -/
noncomputable abbrev fiber (b : B) : Type uF := submodule 𝕜 F E b

/-- The complement's total topology, induced by its inclusion in the ambient product. -/
@[instance_reducible] noncomputable def totalSpaceTopology :
    TopologicalSpace (TotalSpace (model 𝕜 F E) (fiber 𝕜 F E)) :=
  tC[count 𝕜 F E, submodule 𝕜 F E]

/-- The fiber-bundle structure on the chosen complement, for its induced total topology. -/
@[instance_reducible] noncomputable def fiberBundle :
    @FiberBundle B (model 𝕜 F E) _ _ (fiber 𝕜 F E) (totalSpaceTopology 𝕜 F E) _ :=
  (finiteComplement 𝕜 F E).2.2.1

/-- The vector-bundle structure on the chosen complement, using `fiberBundle`. -/
instance vectorBundle :
    @VectorBundle 𝕜 B (model 𝕜 F E) (fiber 𝕜 F E) _ _ _ _ _ _
      (totalSpaceTopology 𝕜 F E) _ (fiberBundle 𝕜 F E) :=
  (finiteComplement 𝕜 F E).2.2.2.1

/-- A global trivialization of the product with the chosen complement, for the
fiberwise-product total topology and the finite-dimensional model `F × model 𝕜 F E`. -/
noncomputable def trivialization :
    @Trivialization B (F × model 𝕜 F E) _ _ _
      (@FiberBundle.Prod.topologicalSpace B F E (model 𝕜 F E) (fiber 𝕜 F E)
        inferInstance (totalSpaceTopology 𝕜 F E))
      (π (F × model 𝕜 F E) (E ×ᵇ fiber 𝕜 F E)) :=
  (finiteComplement 𝕜 F E).2.2.2.2.1

/-- The chosen product trivialization is defined over every point of the base. -/
@[simp] theorem trivialization_baseSet :
    @Trivialization.baseSet B (F × model 𝕜 F E)
      (TotalSpace (F × model 𝕜 F E) (E ×ᵇ fiber 𝕜 F E))
      inferInstance inferInstance
      (@FiberBundle.Prod.topologicalSpace B F E (model 𝕜 F E) (fiber 𝕜 F E)
        inferInstance (totalSpaceTopology 𝕜 F E))
      (π (F × model 𝕜 F E) (E ×ᵇ fiber 𝕜 F E)) (trivialization 𝕜 F E) = Set.univ :=
  (finiteComplement 𝕜 F E).2.2.2.2.2.1

/-- The chosen global product trivialization is linear on each fiber. -/
instance trivialization_isLinear :
    @Trivialization.IsLinear 𝕜 B (F × model 𝕜 F E) (E ×ᵇ fiber 𝕜 F E) _ _ _
      (@FiberBundle.Prod.topologicalSpace B F E (model 𝕜 F E) (fiber 𝕜 F E)
        inferInstance (totalSpaceTopology 𝕜 F E)) _ _ _ _ (trivialization 𝕜 F E) :=
  (finiteComplement 𝕜 F E).2.2.2.2.2.2

end finiteComplement

end VectorBundle
