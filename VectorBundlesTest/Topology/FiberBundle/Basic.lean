/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import VectorBundles.Topology.FiberBundle.Basic

/-!
# Emptiness examples for trivial fiber bundles

The trivial real-line bundle over the real line has nonempty total space. Empty bases and
empty models give empty total spaces, even when the other factor is the real line.
-/

@[expose] public section

example : ¬ IsEmpty (Bundle.TotalSpace ℝ (Bundle.Trivial ℝ ℝ)) := by
  intro h
  rcases (FiberBundle.isEmpty_totalSpace_iff ℝ (Bundle.Trivial ℝ ℝ)).mp h with hB | hF
  · exact (not_nonempty_iff.mpr hB) (inferInstance : Nonempty ℝ)
  · exact (not_nonempty_iff.mpr hF) (inferInstance : Nonempty ℝ)

example : IsEmpty (Bundle.TotalSpace ℝ (Bundle.Trivial Empty ℝ)) := by
  exact (FiberBundle.isEmpty_totalSpace_iff ℝ (Bundle.Trivial Empty ℝ)).mpr
    (Or.inl (inferInstance : IsEmpty Empty))

example : IsEmpty (Bundle.TotalSpace Empty (Bundle.Trivial ℝ Empty)) := by
  exact (FiberBundle.isEmpty_totalSpace_iff Empty (Bundle.Trivial ℝ Empty)).mpr
    (Or.inr (inferInstance : IsEmpty Empty))
