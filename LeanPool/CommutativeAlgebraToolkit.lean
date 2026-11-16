/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.CommutativeAlgebraToolkit.DerivationLeibnizProd
public import LeanPool.CommutativeAlgebraToolkit.DerivationLieMulLeft
public import LeanPool.CommutativeAlgebraToolkit.FinitePresentationPiRightHomBijective
public import LeanPool.CommutativeAlgebraToolkit.FlatAssociatedPrimes
public import LeanPool.CommutativeAlgebraToolkit.FlatProdPi
public import LeanPool.CommutativeAlgebraToolkit.FormallySmoothMapBaseChange
public import LeanPool.CommutativeAlgebraToolkit.FractionRingQuotient
public import LeanPool.CommutativeAlgebraToolkit.FrobeniusRangePow
public import LeanPool.CommutativeAlgebraToolkit.HasseDerivXPowMul
public import LeanPool.CommutativeAlgebraToolkit.InjectiveIffDivisible
public import LeanPool.CommutativeAlgebraToolkit.IsAdicCompleteOfIsNilpotent
public import LeanPool.CommutativeAlgebraToolkit.IsNoetherianRingIffFinitePresentation
public import LeanPool.CommutativeAlgebraToolkit.IsPerfectNormalClosure
public import LeanPool.CommutativeAlgebraToolkit.IsSimpleModuleTrace
public import LeanPool.CommutativeAlgebraToolkit.MonoidGroupCompletion
public import LeanPool.CommutativeAlgebraToolkit.NoetherianIsOpenOfStableUnderGeneralization
public import LeanPool.CommutativeAlgebraToolkit.PolynomialIntegerValued
public import LeanPool.CommutativeAlgebraToolkit.PolynomialIsCoprimeX
public import LeanPool.CommutativeAlgebraToolkit.PrimaryComponentInjective
public import LeanPool.CommutativeAlgebraToolkit.RatSmulMemIndivisible
public import LeanPool.CommutativeAlgebraToolkit.ResultantProdXSubC
public import LeanPool.CommutativeAlgebraToolkit.SemilocalStableRange
public import LeanPool.CommutativeAlgebraToolkit.SubalgebraIsUnitOfIsIntegral
public import LeanPool.CommutativeAlgebraToolkit.TensorProductMemRangeRTensorBasis

/-!
# Commutative algebra toolkit

Source: url:https://stacks.math.columbia.edu
Authors: Michel Hua
Status: verified
Main declarations: `Polynomial.intValuedBasis`, `Polynomial.exists_eq_sum_intCast_smul_choose`,
  `isNoetherianRing_iff_forall_finitePresentation`, `Module.injective_iff_smul_surjective`,
  `IsSimpleModule.nonempty_linearEquiv_of_trace_eq`,
  `Polynomial.forall_hasseDeriv_eq_zero_iff_exists_expand`,
  `Module.FinitePresentation.piRightHom_bijective`, `Submodule.IsAssociatedPrime.comap_eq_of_flat`
Tags: commutative-algebra, integer-valued-polynomials, injective-modules, hasse-derivatives
MSC: 13C11, 13E05, 13F20, 13N15, 11C08
-/
