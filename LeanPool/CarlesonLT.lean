/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

module

public import LeanPool.CarlesonLT.Auto.ModelOperator
public import LeanPool.CarlesonLT.Auto.AnisotropicCarleson
public import LeanPool.CarlesonLT.Auto.ParametricIntegralContDiff
public import LeanPool.CarlesonLT.Auto.HardyLittlewoodMaximal
public import LeanPool.CarlesonLT.Auto.ClassicalCarleson
public import LeanPool.CarlesonLT.Defs
public import LeanPool.CarlesonLT.Theorems

/-!
# Anisotropic Carleson bounds and almost-everywhere Fourier convergence

Source: arxiv:1710.10962, doi:10.1007/s00041-018-09657-7, url:https://github.com/roos-j/lean-lt-carleson
Authors: Joris Roos
Status: verified
Main declarations: `CarlesonLT.anisotropic_carleson`, `CarlesonLT.classical_carleson`
Tags: harmonic-analysis, fourier-series, time-frequency-analysis, maximal-operators
MSC: 42A20, 42B20, 42B25
-/
