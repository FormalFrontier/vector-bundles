/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import VectorBundlesTest.Topology.FiberBundle.Connected
public import VectorBundlesTest.Topology.FiberBundle.Projection
public import VectorBundlesTest.Topology.FiberBundle.Proper
public import VectorBundlesTest.Topology.FiberBundle.LocallyCompact
public import VectorBundlesTest.Topology.FiberBundle.Countability
public import VectorBundlesTest.Topology.FiberBundle.Metrizable
public import VectorBundlesTest.Topology.VectorBundle.HermitianMetric
public import VectorBundlesTest.Topology.VectorBundle.Isomorphism
public import VectorBundlesTest.Topology.VectorBundle.Metric
public import VectorBundlesTest.Topology.VectorBundle.MetricPullback
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalAddition
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalComplement
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalComparison
public import VectorBundlesTest.Topology.VectorBundle.OrthogonalProjection
public import VectorBundlesTest.Topology.VectorBundle.OrthonormalTrivialization
public import VectorBundlesTest.Topology.VectorBundle.SemilinearEvaluation

public import VectorBundlesTest.Topology.FiberBundle.ClosedCylinder
public import VectorBundlesTest.Topology.FiberBundle.Prod
public import VectorBundlesTest.Topology.FiberBundle.Pullback
public import VectorBundlesTest.Topology.FiberBundle.Pullback.Proper
public import VectorBundlesTest.Topology.FiberBundle.SupportedTransport
public import VectorBundlesTest.Topology.VectorBundle.Cylinder
public import VectorBundlesTest.Topology.VectorBundle.FiniteComplement
public import VectorBundlesTest.Topology.VectorBundle.FiniteEmbedding
public import VectorBundlesTest.Topology.VectorBundle.Frame
public import VectorBundlesTest.Topology.VectorBundle.Range
public import VectorBundlesTest.Topology.VectorBundle.TrivialMetric

public import VectorBundlesTest.Topology.VectorBundle.HermitianMetric.Operations

/-!
# Examples of topological vector-bundle geometry

The examples use the library interfaces for metrics, splitting, products, pullbacks,
cylinder charts, frames, embeddings, ranges and complements, including standard, varying-metric,
zero-rank and empty-base bundles. They include the canonical projection inverse and its relation
to the zero section, proper-projection compactness and empty-base boundaries, pullback pairings,
and moving complements for a shear metric.
-/
