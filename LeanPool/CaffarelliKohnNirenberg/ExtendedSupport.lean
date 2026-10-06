/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ForceSlotNumericalScaling
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.ThetaDecayAbsoluteConstant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceLocalMoments
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAOneRound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.CollarCover
public import LeanPool.CaffarelliKohnNirenberg.Foundation.DyadicCells
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.HeatKernelFundamentalSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.IntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SobolevEmbeddingR3
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierLemmaAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierProfileStandard
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDirectRoute
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageDistribution
public import LeanPool.CaffarelliKohnNirenberg.Leray.Stability
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryFaithful
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PressureDecompositionRiesz
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialGradientSqENorm
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Statements.AssociatedPressure

/-!
# Additional CKN support for Navier–Stokes regularity imports

Imports the Leray, pressure and linear regularity dependency closure required
by the Escauriaza–Seregin–Šverák and CIV axisymmetric developments.
The additional source is CaffarelliKohnNirenberg commit
`381d658ead0f03a18361965cc0427ce3fa5844ab` (Apache-2.0).
The previously pooled partial regularity proofs are retained.
-/
