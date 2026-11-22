/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.MonicLocalization
public import LeanPool.QuillenSuslin.QuillenLemmaTwo
public import LeanPool.QuillenSuslin.Extended
public import LeanPool.QuillenSuslin.Glue
public import LeanPool.QuillenSuslin.Dilation
public import LeanPool.QuillenSuslin.EndPolynomial
public import LeanPool.QuillenSuslin.Fibre
public import LeanPool.QuillenSuslin.Transition
public import LeanPool.QuillenSuslin.GlueMaps
public import LeanPool.QuillenSuslin.PatchingCore
public import LeanPool.QuillenSuslin.PatchingTwo
public import LeanPool.QuillenSuslin.QuillenIdeal
public import LeanPool.QuillenSuslin.QuillenPatching
public import LeanPool.QuillenSuslin.PatchingDescent
public import LeanPool.QuillenSuslin.MvTransport
public import LeanPool.QuillenSuslin.QuillenPatchingMv

/-!
# Projective modules over polynomial rings (Quillen patching)

Source: doi:10.1007/BF01390008, url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/2295
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.QuillenSuslin.isPrincipalIdealRing_monicLocalization`,
  `LeanPool.QuillenSuslin.isField_monicLocalization`,
  `LeanPool.QuillenSuslin.isExtendedFrom_iff_evalZero`,
  `LeanPool.QuillenSuslin.exists_unit_lift_dilation`,
  `LeanPool.QuillenSuslin.exists_finite_projective_glue`,
  `LeanPool.QuillenSuslin.exists_ideal_isExtendedAfter_away`,
  `LeanPool.QuillenSuslin.isExtendedFrom_of_forall_isMaximal`,
  `LeanPool.QuillenSuslin.isExtendedFrom_mvPolynomial_of_forall_isMaximal`
Tags: commutative-algebra, projective-modules, polynomial-rings, quillen-suslin, quillen-patching
MSC: 13C10, 13B30, 19A13
-/
