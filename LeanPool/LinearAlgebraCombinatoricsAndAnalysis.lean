/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.AeNormSqLeOfInner
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.ChoosePrimePowSubOne
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.ContDiffIsMeagreImage
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.CurryR1Space
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.DetPascalMatrix
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.MatrixDetFinTwoCauchyBinet
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.MatrixElementarySubgroup
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.MatrixTraceSubPowOdd
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.MonoidRightZero
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.MulPowCommutator
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.QBinomial
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.QuasiSoberPiCoreCompact
public import LeanPool.LinearAlgebraCombinatoricsAndAnalysis.SingularValuesSigmaTwo

/-!
# Singular values, minors and elementary matrices, with lemmas in combinatorics and analysis

Source: url:https://doi.org/10.1073/pnas.37.11.760
Authors: Michel Hua
Status: verified
Main declarations: `LinearMap.sum_powersetCard_two_prod_singularValues_add_le`, `Matrix.det_pascal`,
  `Monoid.exists_forall_mul_eq_self_iff_of_finite`, `Homeomorph.curryOfR1Space`,
  `ContDiffOn.isMeagre_image`
Tags: singular-values, ky-fan-inequality, cauchy-binet, elementary-matrices, whitehead-lemma
MSC: 15A18, 15A15, 15A42, 19B10, 05A30, 11B65, 20F12, 20M10, 54C35, 54E52

The singular-value extension claimed here is the σ₂ addition inequality. The included
maximum-principle upper bound is supporting: it follows from the pool's existing
contraction-family bound and finite-dimensional gauge identity, using a unit-scalar
rotation and prefix monotonicity. It is not a new headline or an attainment theorem.
-/
