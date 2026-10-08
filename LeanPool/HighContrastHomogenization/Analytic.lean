/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains
public import LeanPool.HighContrastHomogenization.Analytic.NormComparison
public import LeanPool.HighContrastHomogenization.Analytic.SingularKernel
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Analytic.AntiVacuityInstances
public import LeanPool.HighContrastHomogenization.Analytic.DualNormJunk
public import LeanPool.HighContrastHomogenization.Analytic.CenteringInvariance
public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing
public import LeanPool.HighContrastHomogenization.Analytic.WeightedEnergy
public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty
public import LeanPool.HighContrastHomogenization.Analytic.ClassCounterexample
public import LeanPool.HighContrastHomogenization.Analytic.ClassPairing
public import LeanPool.HighContrastHomogenization.Analytic.LocalIntegrability
public import LeanPool.HighContrastHomogenization.Analytic.WeakGradientClosure
public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a
public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Analytic.NormEquivalence
public import LeanPool.HighContrastHomogenization.Analytic.ScaledCoeff

/-!
# High-contrast homogenization: Analytic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The analytic provider layer for the homogenization theorem

The proofs standing behind the conclusion of
`t.random.homogenization`: the fail-closed behaviour of the
normalized dual norms, the convex domains and the shape datum carried by the
Dirichlet estimate, the weighted Sobolev classes and the absolute convergence of
their pairings, and the membership classes they are read on.

These modules sit below the frozen statement and are imported by no frozen file,
so they may be extended without moving any frozen declaration's pin.
-/
