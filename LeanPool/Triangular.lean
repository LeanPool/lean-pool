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
-/

/-! ## Application to Fourier convergence

In `LeanPool.Triangular.Auto.Carleson`, `Triangular.Auto.carleson_of_triangular_bound`
deduces almost-everywhere Fourier convergence for continuous one-periodic functions.
The proof of `Triangular.Auto.triangularHilbert_main` supplies the estimate used in this
application. `CarlesonLT.Auto.carleson_fourierSeries` proves convergence for periodic
functions that are square-integrable on a period.
-/
