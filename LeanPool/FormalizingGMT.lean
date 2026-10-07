/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/

module

public import LeanPool.FormalizingGMT.Densities.Basic
public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityOutside
public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityOutsideLemmas
public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityInside
public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityInsideLemmas
public import LeanPool.FormalizingGMT.RadonMeasures.Basic
public import LeanPool.FormalizingGMT.RadonMeasures.HausdorffMeasure
public import LeanPool.FormalizingGMT.MarstrandTheorem
public import LeanPool.FormalizingGMT.RadonMeasures.RestrictionFiniteMeasure
public import LeanPool.FormalizingGMT.TangentMeasures.TangentMeasures
public import LeanPool.FormalizingGMT.WeakConvergence.CompactnessCriterion
public import LeanPool.FormalizingGMT.Densities.SingularIntegralDensities
public import LeanPool.FormalizingGMT.Covering.VariantVitali

/-!
# Formalizing geometric measure theory

Source: url:https://github.com/uw-math-ai/FormalizingGMT
Authors: Theodore Meek, Ignacio Tejeda, Annie Cao, Nathan Pao
Status: verified
Main declarations: `mattila_14_10`, `mattila_14_11`
Tags: geometric-measure-theory, Hausdorff-measure, tangent-measures, weak-convergence
MSC: 28A75, 28A78, 49Q15
-/

/-!
# FormalizingGMT

This is the root import for the FormalizingGMT project.
-/
