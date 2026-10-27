/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundles.Analysis.InnerProductSpace.PositiveForm
public import VectorBundles.Analysis.Normed.Ring.Units
public import VectorBundles.Topology.Algebra.GroupWithZero
public import VectorBundles.Topology.Algebra.Module.FiniteDimensionalOperator
public import VectorBundles.Topology.Algebra.Module.OpenMap
public import VectorBundles.Topology.ContinuousMap.Algebra
public import VectorBundles.Topology.Compactness.CountablyCompact
public import VectorBundles.Topology.Compactness.Lindelof
public import VectorBundles.Topology.Compactness.Paracompact
public import VectorBundles.Topology.Compactness.SigmaCompact
public import VectorBundles.Topology.LocallyFinite
public import VectorBundles.Topology.CompactOpen
public import VectorBundles.Topology.Connected.Basic
public import VectorBundles.Topology.Separable.Basic
public import VectorBundles.Topology.FiberBundle.Basic
public import VectorBundles.Topology.FiberBundle.Connected
public import VectorBundles.Topology.FiberBundle.Separable
public import VectorBundles.Topology.FiberBundle.Projection
public import VectorBundles.Topology.FiberBundle.Proper
public import VectorBundles.Topology.FiberBundle.LocallyCompact
public import VectorBundles.Topology.FiberBundle.Countability
public import VectorBundles.Topology.FiberBundle.Metrizable
public import VectorBundles.Topology.FiberBundle.SigmaCompact
public import VectorBundles.Topology.FiberBundle.Trivialization.SigmaCompact
public import VectorBundles.Topology.FiberBundle.SigmaCompact.LocallyCompactBase
public import VectorBundles.Topology.FiberBundle.SigmaCompact.Proper
public import VectorBundles.Topology.FiberBundle.Lindelof
public import VectorBundles.Topology.FiberBundle.Trivialization.Lindelof
public import VectorBundles.Topology.FiberBundle.Lindelof.LocallyCompactBase
public import VectorBundles.Topology.FiberBundle.Lindelof.Proper
public import VectorBundles.Topology.FiberBundle.Lindelof.Reflection
public import VectorBundles.Topology.FiberBundle.Paracompact
public import VectorBundles.Topology.FiberBundle.CoordChange
public import VectorBundles.Topology.Maps.Proper
public import VectorBundles.Topology.VectorBundle.CoordinateMap
public import VectorBundles.Topology.VectorBundle.FiniteSum
public import VectorBundles.Topology.VectorBundle.HermitianMetric
public import VectorBundles.Topology.Bornology.Inducing
public import VectorBundles.Topology.VectorBundle.Hom
public import VectorBundles.Topology.VectorBundle.MetricComap
public import VectorBundles.Topology.VectorBundle.Isomorphism
public import VectorBundles.Topology.VectorBundle.Metric
public import VectorBundles.Topology.VectorBundle.MetricPullback
public import VectorBundles.Topology.VectorBundle.MetricExistence
public import VectorBundles.Topology.VectorBundle.MetricModel
public import VectorBundles.Topology.VectorBundle.OpenMap
public import VectorBundles.Topology.VectorBundle.OrthogonalAddition
public import VectorBundles.Topology.VectorBundle.OrthogonalComplement
public import VectorBundles.Topology.VectorBundle.OrthogonalComparison
public import VectorBundles.Topology.VectorBundle.OrthogonalProjection
public import VectorBundles.Topology.VectorBundle.OrthonormalTrivialization
public import VectorBundles.Topology.VectorBundle.ScalarEnd
public import VectorBundles.Topology.VectorBundle.SemilinearEvaluation
public import VectorBundles.Topology.VectorBundle.WeightedForm

public import VectorBundles.Analysis.Normed.Operator.Factorization
public import VectorBundles.Analysis.Normed.Operator.LowerBound
public import VectorBundles.Data.Bundle
public import VectorBundles.Topology.FiberBundle.ClosedCylinder
public import VectorBundles.Topology.FiberBundle.Prod
public import VectorBundles.Topology.FiberBundle.Pullback
public import VectorBundles.Topology.FiberBundle.Pullback.Proper
public import VectorBundles.Topology.FiberBundle.SupportedTransport
public import VectorBundles.Topology.MetricSpace.Antilipschitz
public import VectorBundles.Topology.VectorBundle.Cylinder
public import VectorBundles.Topology.VectorBundle.Embedding
public import VectorBundles.Topology.VectorBundle.FiniteComplement
public import VectorBundles.Topology.VectorBundle.FiniteEmbedding
public import VectorBundles.Topology.VectorBundle.Frame
public import VectorBundles.Topology.VectorBundle.KernelProjection
public import VectorBundles.Topology.VectorBundle.Range
public import VectorBundles.Topology.VectorBundle.TrivialMetric

public import VectorBundles.Topology.Bornology.Bounded
public import VectorBundles.Topology.VectorBundle.Section
public import VectorBundles.Topology.VectorBundle.HermitianMetric.Operations

/-!
# Geometry of topological vector bundles

This root reexports bundle metrics, orthogonal splitting, fiberwise isomorphisms,
products, pullbacks, cylinder charts, frames, finite embeddings, ranges and complements,
together with pullbacks of supplied Hermitian metrics and canonical comparisons of their
orthogonal complements. The projection modules give open-embedding criteria by subsingleton
fibers, canonical projection homeomorphisms when every fiber is also nonempty, and the
proper-projection criterion by compactness of every fiber.
-/
