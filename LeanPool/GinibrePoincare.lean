/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNine

/-!
# Sharp symmetric Poincaré inequality for the complex Ginibre log-gas

Source: arxiv:2608.19358v2, url:https://github.com/djalilchafai/ginibre-poincare/tree/a1b2ba84e7dad8ba11b5c49a18b986a762a00a41
Authors: Djalil Chafaï
Status: verified
Main declarations: `GinibrePoincare.ginibre_symmetric_weak_poincare`,
  `GinibrePoincare.ginibreEquality_full_weak_affine_iff`, `GinibrePoincare.fullTheoremOneNine_named`
Tags: ginibre-ensemble, poincare-inequality, weak-gradients, hermite-polynomials, equality-cases
MSC: 60E15, 60B20, 46E35
-/
