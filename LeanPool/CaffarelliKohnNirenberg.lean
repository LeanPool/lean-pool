/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

/-!
# Caffarelli–Kohn–Nirenberg partial regularity

Source: url:https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/tree/381d658ead0f03a18361965cc0427ce3fa5844ab
Authors: Scott Armstrong, Vlad Vicol
Status: verified
Main declarations: `CKN.caffarelliKohnNirenberg`, `CKN.epsilonRegularityL3`
Tags: Navier–Stokes, partial differential equations, harmonic analysis
MSC: 35Q30, 35B65, 42B20, 28A78
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ExtendedSupport
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremA
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremB
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremC
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowSuitable
public import LeanPool.CaffarelliKohnNirenberg.Witnesses.TrivialSolution
