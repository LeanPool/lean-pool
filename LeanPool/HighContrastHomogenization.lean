/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

-- Project aggregator: the frozen exports (each pulls in exactly its provider
-- chain) and the consistency checks of the definitions, which no export imports.
public import LeanPool.HighContrastHomogenization.Analytic
public import LeanPool.HighContrastHomogenization.Annealed.Witness
public import LeanPool.HighContrastHomogenization.Basic
public import LeanPool.HighContrastHomogenization.Consistency
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Frozen.PolynomialEntry
public import LeanPool.HighContrastHomogenization.Frozen.PolynomialEntryBridge
public import LeanPool.HighContrastHomogenization.Frozen.PolynomialHomogenization
public import LeanPool.HighContrastHomogenization.Frozen.QuenchedConvergence
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.MainResults

-- The polynomial-entry route: the sixteen printed propositions whose statements the
-- entry theorem is assembled from, and the three statements carried in
-- CoarseGraining's own vocabulary.  `HCPoly.Entry.Statements.PolynomialEntry` itself
-- arrives through `HCPoly.Frozen.PolynomialEntryBridge`.
public import LeanPool.HighContrastHomogenization.Entry.CG.Anchors.ResponseFiniteDefect
public import LeanPool.HighContrastHomogenization.Entry.CG.Anchors.ResponseSubadditiveCountable
public import LeanPool.HighContrastHomogenization.Entry.CG.Anchors.ResponseSummable
public import LeanPool.HighContrastHomogenization.Entry.Statements.GlobalSelection
public import LeanPool.HighContrastHomogenization.Entry.Statements.InitialFixedGridScale
public import LeanPool.HighContrastHomogenization.Entry.Statements.MatrixAveraging
public import LeanPool.HighContrastHomogenization.Entry.Statements.OneGridPropagation
public import LeanPool.HighContrastHomogenization.Entry.Statements.ParentChildRecurrence
public import LeanPool.HighContrastHomogenization.Entry.Statements.PositiveGap
public import LeanPool.HighContrastHomogenization.Entry.Statements.ProjectiveStep
public import LeanPool.HighContrastHomogenization.Entry.Statements.ResponseTransfer
public import LeanPool.HighContrastHomogenization.Entry.Statements.ScaleSelection
public import LeanPool.HighContrastHomogenization.Entry.Statements.SourceWhitney
public import LeanPool.HighContrastHomogenization.Entry.Statements.SuccessfulShortBridge
public import LeanPool.HighContrastHomogenization.Entry.Statements.TwoGridTransport
public import LeanPool.HighContrastHomogenization.Entry.Statements.TwoGridWhitney

/-!
# Homogenization at a polynomial scale in high contrast

Source: arxiv:2609.27647,
url:https://github.com/scottnarmstrong/HighContrastHomogenization/tree/7a13dbcd8d6609264a713373f5c69ceeac870472
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
Status: verified
Main declarations: `HCPoly.polynomial_entry`, `HCPoly.algebraic_convergence`,
`HCPoly.uniform_homogenization`, `HCPoly.polynomial_homogenization`, `HCPoly.quenched_convergence`
Tags: homogenization, elliptic-equations, stochastic-pde, high-contrast, quantitative-regularity
MSC: 35B27, 35J15, 60K37
-/

public section
