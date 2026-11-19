/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/

module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Defs
public import LeanPool.StableManifold.LocalSets
public import LeanPool.StableManifold.Linear.Spectral
public import LeanPool.StableManifold.Linear.Subspaces
public import LeanPool.StableManifold.Linear.Splitting
public import LeanPool.StableManifold.Linear.HyperbolicSplitting
public import LeanPool.StableManifold.Sequence.Superpose
public import LeanPool.StableManifold.Sequence.SuperposeContDiff
public import LeanPool.StableManifold.Perron.Operator
public import LeanPool.StableManifold.Perron.Graph
public import LeanPool.StableManifold.Perron.Smooth
public import LeanPool.StableManifold.Local.Cutoff
public import LeanPool.StableManifold.Local.StableSet
public import LeanPool.StableManifold.Theorem

/-!
# The stable manifold theorem for hyperbolic fixed points

Source: url:https://github.com/vltanh/lean4-stable-manifold/tree/4909ed2eb6bdc504f86ccb455e544315f11d3860
Authors: The-Anh Vu-Le
Status: verified
Main declarations: `Function.exists_nhds_localStableSet_localUnstableSet_eq_graph`,
  `Function.exists_nhds_localStableSet_localUnstableSet_eq_setOf`,
  `ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`, `StableManifold.contDiff_superpose`
Tags: dynamical-systems, invariant-manifolds, functional-analysis
MSC: 37C25, 37D10, 47H10
-/
