/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.Triangular.Auto.TriangularHT
public import LeanPool.Triangular.Theorems

/-!
# The symmetric triangular Hilbert form

Source: url:https://github.com/roos-j/lean-triangular/tree/9edcdf82f32466c0275ba6d67f5b37876c23ed0c
Authors: Joris Roos
Status: verified
Main declarations: `Triangular.triangular_ht_bound`, `Triangular.Auto.tendsto_truncatedForm`,
  `Triangular.Auto.triangularHilbert_unique_extension`
Tags: harmonic-analysis, singular-integrals, fourier-series
MSC: 42B20, 42A20

As an application, `Triangular.classical_carleson` gives an alternative proof of
almost-everywhere Fourier convergence for continuous one-periodic functions.
`CarlesonLT.Auto.carleson_fourierSeries` in Lean Pool proves a stronger result.
-/
