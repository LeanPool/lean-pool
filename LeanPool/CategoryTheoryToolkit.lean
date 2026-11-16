/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.CategoryTheoryToolkit.AbelianCommSqExact
public import LeanPool.CategoryTheoryToolkit.AdjunctionIdempotent
public import LeanPool.CategoryTheoryToolkit.BiprodShear
public import LeanPool.CategoryTheoryToolkit.KaroubiAdditiveFunctors
public import LeanPool.CategoryTheoryToolkit.MonadicityIff
public import LeanPool.CategoryTheoryToolkit.RepResFunctor
public import LeanPool.CategoryTheoryToolkit.SemiCartesianSquare
public import LeanPool.CategoryTheoryToolkit.SemiSimplexCategoryReedy

/-!
# Category theory toolkit

Source: url:https://ncatlab.org/nlab/show/idempotent+adjunction
Authors: Michel Hua
Status: verified
Main declarations: `CategoryTheory.Adjunction.fixedEquiv`,
  `CategoryTheory.Adjunction.idempotent_tfae`, `CategoryTheory.Adjunction.fixedLeftReflective`,
  `CategoryTheory.Monad.isEquivalence_comparison_iff`,
  `CategoryTheory.Idempotents.karoubiUniversalAdditive`, `Rep.isEquivalence_resFunctor_iff`,
  `CategoryTheory.CommSq.isSemiCartesian_iff_exists_factorisation`,
  `CategoryTheory.SemiadditiveOfBinaryBiproducts.preadditiveOfWeakMonoEpiInvertible`
Tags: adjunctions, monadicity, karoubi-envelope, reedy, representations, abelian-categories
MSC: 18A40, 18C15, 18E10, 18E05, 18N40, 20C99
-/
