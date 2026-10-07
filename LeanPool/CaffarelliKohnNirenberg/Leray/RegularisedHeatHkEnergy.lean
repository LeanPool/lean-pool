/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedOrderedDerivative
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedOrderedDerivativeFrechet
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportDivergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportCutoff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Diffusive Sobolev energy pairing

The whole-space integration-by-parts identity gives the dissipative term
for each ordered spatial derivative of the regularized equation.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The classical spatial Laplacian on a scalar field, written as the sum
of its three coordinate second derivatives. -/
@[expose]
def regularisedScalarLaplacian (f : Vec3 → ℝ) : Vec3 → ℝ := fun x =>
  ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ f y (CKN.basisVec i)) x
      (CKN.basisVec i)

end CKN.Leray

end
