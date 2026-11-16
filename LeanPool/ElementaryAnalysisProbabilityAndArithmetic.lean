/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.AdjacentSequences
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.BinomialCLT
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.HyperplaneDistance
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.LinearODE
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.PeriodicDigits
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.SolidOfRevolution
public import LeanPool.ElementaryAnalysisProbabilityAndArithmetic.SquarefreePowers

/-!
# Classical results of elementary analysis, probability and arithmetic

Source: url:https://github.com/leanprover-community/mathlib4/pull/44770
Authors: Michel Hua
Status: verified
Main declarations: `ProbabilityTheory.tendstoInDistribution_binomial`,
  `ProbabilityTheory.tendsto_binomial_real_setOf_le`, `eq_exp_smul_mul_integral_of_hasDerivAt`,
  `EuclideanSpace.volume_solidOfRevolution`,
  `MeasureTheory.Measure.volume_prod_convexJoin_singleton_prod`,
  `Monotone.exists_tendsto_of_antitone_of_tendsto_sub`,
  `Real.exists_ratCast_eq_iff_digits_eventually_periodic`,
  `Nat.squarefree_iff_forall_zmod_pow_carmichael_add_one`,
  `EuclideanGeometry.dist_orthogonalProjection_eq_abs_inner_div_norm`
Tags: de-moivre-laplace, variation-of-constants, solid-of-revolution, periodic-digits
MSC: 60F05, 34A30, 28A75, 40A05, 11A63, 11A07, 51N20
-/
