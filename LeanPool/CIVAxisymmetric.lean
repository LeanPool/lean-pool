/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/



module

public import LeanPool.CIVAxisymmetric.Statements.MainTheorem
public import LeanPool.CIVAxisymmetric.Statements.AxisymmetricTheorem
public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallnessProp
public import LeanPool.CIVAxisymmetric.Statements.ForceUnderCore
public import LeanPool.CIVAxisymmetric.Statements.InteriorAnalyticity
public import LeanPool.CIVAxisymmetric.Statements.AxisMaximumPrinciple
public import LeanPool.CIVAxisymmetric.Statements.RegularAnnulus
public import LeanPool.CIVAxisymmetric.Statements.Comparison
public import LeanPool.CIVAxisymmetric.Statements.ComparisonAncient
public import LeanPool.CIVAxisymmetric.Statements.ClosureLemma
public import LeanPool.CIVAxisymmetric.Statements.SerrinInteriorEstimates
public import LeanPool.CIVAxisymmetric.Statements.GktCriterion
public import LeanPool.CIVAxisymmetric.Statements.TimeZeroSingularSetNull
public import LeanPool.CIVAxisymmetric.Identities.ForceSymmetry
public import LeanPool.CIVAxisymmetric.Reduction.ExteriorNonanalyticUnconditional

/-!
# Regularity of asymptotically axisymmetric Navier–Stokes solutions

Source: arxiv:2609.20803,
url:https://github.com/scottnarmstrong/CIVAxisymmetric/tree/9f539dc7bf7ddd414d3ef81df539e1bef229f681
Authors: Scott Armstrong, Vlad Vicol
Status: verified
Main declarations: `CIV.mainTheorem`, `CIV.axisymmetricTheorem`, `CIV.meridionalSmallness`,
`CIV.interiorAnalyticity`, `CIV.forceUnderCore`
Tags: Navier–Stokes, axisymmetry, partial differential equations, regularity
MSC: 35Q30, 35B65, 35B33
-/
