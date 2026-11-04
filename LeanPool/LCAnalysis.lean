/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import LeanPool.LCAnalysis.BoundedBelow
public import LeanPool.LCAnalysis.MackeyLipschitz
public import LeanPool.LCAnalysis.Rules

/-!
# Michal–Bastiani Calculus on Locally Convex Spaces

Source: arxiv:2602.12362, url:https://github.com/glaroton/LCAnalysis
Authors: Gabriel Larotonda
Status: verified
Main declarations: `LCAnalysis.ContDiffMBOn.comp`,
  `LCAnalysis.ContDiffMBOn.exists_iteratedDMB_multilinear`, `LCAnalysis.smoothMBOn_iff_contDiffOn`,
  `LCAnalysis.exists_hasWeakIntegral`, `LCAnalysis.mackeyComplete_iff_integratesLipschitzCurves`,
  `LCAnalysis.ContDiffMBOn.of_comp_of_boundedBelow`
Tags: functional-analysis, locally-convex-spaces, calculus, weak-integrals
MSC: 46T20, 46A03, 58B10
-/
