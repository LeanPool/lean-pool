/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part002

/-! NF weak partition development: NAR4H5C095M3Part003. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_fresh_027 (x : Var) (R : Class) :
    (nb095_alpha_dummy_262 x R) ∉
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_262] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))).fv)
      0

theorem nb095_fresh_028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_329 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_329] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_029 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_305 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_305] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_030 (f : Var) :
    (nb095_alpha_dummy_330 f) ∉
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_330] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_297 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_031 (f : Var) :
    (nb095_alpha_dummy_306 f) ∉
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_306] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))).fv)
      0

theorem nb095_fresh_032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_375 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_375] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_033 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_351 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_351] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_034 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_376 u S_cls) ∉
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_347 u S_cls)
            (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_376] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_347 u S_cls)
            (syn_wrex (nb095_alpha_dummy_348 u S_cls) (Class.cv (nb095_alpha_dummy_341 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_035 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_352 u S_cls) ∉
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_352] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))).fv)
      0

theorem nb095_fresh_036 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_399 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_399] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_037 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_423 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_423] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_038 (f : Var) :
    (nb095_alpha_dummy_400 f) ∉
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_400] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))).fv)
      0

theorem nb095_fresh_039 (f : Var) :
    (nb095_alpha_dummy_424 f) ∉
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_424] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_040 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_435 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_435] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_041 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_459 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_459] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_042 (f : Var) :
    (nb095_alpha_dummy_436 f) ∉
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_436] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))).fv)
      0

theorem nb095_fresh_043 (f : Var) :
    (nb095_alpha_dummy_460 f) ∉
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_460] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_477 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_477] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_045 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_501 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_501] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_046 (f : Var) :
    (nb095_alpha_dummy_478 f) ∉
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_478] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))).fv)
      0

theorem nb095_fresh_047 (f : Var) :
    (nb095_alpha_dummy_502 f) ∉
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_502] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_048 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_537 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_537] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_049 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_513 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_513] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_050 (f : Var) :
    (nb095_alpha_dummy_538 f) ∉
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_538] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_051 (f : Var) :
    (nb095_alpha_dummy_514 f) ∉
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_514] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))).fv)
      0

theorem nb095_fresh_052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_573 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_573] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_053 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_549 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_549] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_054 (f : Var) :
    (nb095_alpha_dummy_574 f) ∉
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_574] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_389 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_055 (f : Var) :
    (nb095_alpha_dummy_550 f) ∉
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_550] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))).fv)
      0

theorem nb095_fresh_056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_585 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_585] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_057 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_609 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_609] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_058 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_586 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_586] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_059 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_610 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_610] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_631 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_631] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_061 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_655 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_655] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_062 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_632 x D R) ∉
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_632] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))).fv)
      0

theorem nb095_fresh_063 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_656 x D R) ∉
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_627 x D R)
            (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_656] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_627 x D R)
            (syn_wrex (nb095_alpha_dummy_628 x D R) (Class.cv (nb095_alpha_dummy_622 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_667 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_667] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_065 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_737 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_737] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_066 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_668 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_668] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_067 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_738 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_738] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_068 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_673 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_673] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_069 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_674 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_674] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_070 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_673 D R S_cls E) ≠ (nb095_alpha_dummy_674 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_673, nb095_alpha_dummy_674] using
    (freshVar_injective (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_071 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_675 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_675] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv)
      0

theorem nb095_fresh_072 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_676 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_676] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv)
      1

theorem nb095_distinct_073 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_675 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_676 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_675, nb095_alpha_dummy_676] using
    (freshVar_injective (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_074 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_683 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_683] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_075 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_707 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_707] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_fresh_076 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_684 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_684] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_077 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_708 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_708] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_078 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_743 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_743] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_079 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_744 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_744] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_080 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_743 D R S_cls E) ≠ (nb095_alpha_dummy_744 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_743, nb095_alpha_dummy_744] using
    (freshVar_injective (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_081 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_745 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_745] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv)
      0

theorem nb095_fresh_082 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_746 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_746] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv)
      1

theorem nb095_distinct_083 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_745 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_746 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_745, nb095_alpha_dummy_746] using
    (freshVar_injective (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_084 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_753 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_753] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_085 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_777 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_777] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_086 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_754 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_754] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_087 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_778 x u D R S_cls f E) ∉
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_778] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_088 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_805 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_805] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_089 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_829 D R S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_829] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_090 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_806 u S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_806] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv)
      0

theorem nb095_fresh_091 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_830 u S_cls E) ∉
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_830] using
    freshVar_not_mem
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb095_fresh_092 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_091] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) 0

theorem nb095_fresh_093 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_092 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_092] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) 1

theorem nb095_distinct_094 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_092 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_091, nb095_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_095 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_669 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_669] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv)
      0

theorem nb095_fresh_096 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_739 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_739] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv)
      0

theorem nb095_fresh_097 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      0

theorem nb095_fresh_098 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      1

theorem nb095_fresh_099 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_013 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      2

theorem nb095_distinct_100 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_012 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_011, nb095_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_101 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_013 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_011, nb095_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_102 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_013 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_012, nb095_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_103 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_003] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_104 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_105 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_004 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_003, nb095_alpha_dummy_004] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R
                  (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_106 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_295 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb095_alpha_dummy_295] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) 0

theorem nb095_fresh_107 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_296 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb095_alpha_dummy_296] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) 1

theorem nb095_distinct_108 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_295 D R S_cls E) ≠ (nb095_alpha_dummy_296 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_295, nb095_alpha_dummy_296] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cvv)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_109 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_343 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_001 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_343] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_001 D R S_cls E))).fv) 0

theorem nb095_fresh_110 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_253 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_002 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_253] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_002 D R S_cls E))).fv) 0

theorem nb095_fresh_111 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_579 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_579] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv)
      0

theorem nb095_fresh_112 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_580 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_580] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv)
      1

theorem nb095_distinct_113 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_579 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_579, nb095_alpha_dummy_580] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_114 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_677 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_677] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv)
      0

theorem nb095_fresh_115 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_678 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_678] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv)
      1

theorem nb095_distinct_116 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_677 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_677, nb095_alpha_dummy_678] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_117 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_747 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_747] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv)
      0

theorem nb095_fresh_118 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_748 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_748] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv)
      1

theorem nb095_distinct_119 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_747 D R S_cls E) ≠ (nb095_alpha_dummy_748 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_747, nb095_alpha_dummy_748] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_120 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_581 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_581] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_121 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_582 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_582] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_122 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_581 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_582 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_581, nb095_alpha_dummy_582] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_123 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_679 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_679] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_124 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_680 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_680] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_125 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_679 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_680 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_679, nb095_alpha_dummy_680] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_126 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_749 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_749] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_127 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_750 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_750] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_128 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_749 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_750 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_749, nb095_alpha_dummy_750] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_129 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_019 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_019] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
      0

theorem nb095_fresh_130 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_020 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
      1

theorem nb095_distinct_131 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_019 D R S_cls E) ≠ (nb095_alpha_dummy_020 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_019, nb095_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_132 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_055 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv)
      0

theorem nb095_fresh_133 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_056 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_056] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv)
      1

theorem nb095_distinct_134 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_055 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_055, nb095_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_135 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_169 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
      0

theorem nb095_fresh_136 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_170 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
      1

theorem nb095_distinct_137 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_169 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_169, nb095_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_138 (f : Var) :
    (nb095_alpha_dummy_021 f) ∉
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_021] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
      0

theorem nb095_fresh_139 (f : Var) :
    (nb095_alpha_dummy_022 f) ∉
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_022] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
      1

theorem nb095_distinct_140 (f : Var) :
    (nb095_alpha_dummy_021 f) ≠ (nb095_alpha_dummy_022 f) := by
  simpa only [nb095_alpha_dummy_021, nb095_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_141 (f : Var) :
    (nb095_alpha_dummy_057 f) ∉
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_057] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv)
      0

theorem nb095_fresh_142 (f : Var) :
    (nb095_alpha_dummy_058 f) ∉
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_058] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv)
      1

theorem nb095_distinct_143 (f : Var) :
    (nb095_alpha_dummy_057 f) ≠ (nb095_alpha_dummy_058 f) := by
  simpa only [nb095_alpha_dummy_057, nb095_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_016 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_144 (f : Var) :
    (nb095_alpha_dummy_171 f) ∉
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_171] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
      0

theorem nb095_fresh_145 (f : Var) :
    (nb095_alpha_dummy_172 f) ∉
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_172] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
      1

theorem nb095_distinct_146 (f : Var) :
    (nb095_alpha_dummy_171 f) ≠ (nb095_alpha_dummy_172 f) := by
  simpa only [nb095_alpha_dummy_171, nb095_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_147 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_027 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) 0

theorem nb095_fresh_148 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_028 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) 1

theorem nb095_distinct_149 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_027 D R S_cls E) ≠ (nb095_alpha_dummy_028 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_027, nb095_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_150 (f : Var) :
    (nb095_alpha_dummy_029 f) ∉ (((Class.cv (nb095_alpha_dummy_022 f))).fv) := by
  simpa only [nb095_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_022 f))).fv) 0

theorem nb095_fresh_151 (f : Var) :
    (nb095_alpha_dummy_030 f) ∉ (((Class.cv (nb095_alpha_dummy_022 f))).fv) := by
  simpa only [nb095_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_022 f))).fv) 1

theorem nb095_distinct_152 (f : Var) :
    (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_030 f) := by
  simpa only [nb095_alpha_dummy_029, nb095_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_022 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_153 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_033 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_154 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_155 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_035 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_156 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_033 D R S_cls E) ≠ (nb095_alpha_dummy_034 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_033, nb095_alpha_dummy_034] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_157 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_033 D R S_cls E) ≠ (nb095_alpha_dummy_035 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_033, nb095_alpha_dummy_035] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_158 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_035 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_034, nb095_alpha_dummy_035] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_159 (f : Var) :
    (nb095_alpha_dummy_036 f) ∉
      (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_036] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_160 (f : Var) :
    (nb095_alpha_dummy_037 f) ∉
      (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_037] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_161 (f : Var) :
    (nb095_alpha_dummy_038 f) ∉
      (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_038] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_162 (f : Var) :
    (nb095_alpha_dummy_036 f) ≠ (nb095_alpha_dummy_037 f) := by
  simpa only [nb095_alpha_dummy_036, nb095_alpha_dummy_037] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_163 (f : Var) :
    (nb095_alpha_dummy_036 f) ≠ (nb095_alpha_dummy_038 f) := by
  simpa only [nb095_alpha_dummy_036, nb095_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_164 (f : Var) :
    (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_038 f) := by
  simpa only [nb095_alpha_dummy_037, nb095_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_165 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_045 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv)
      0

theorem nb095_fresh_166 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_041 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_034 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv)
      0

theorem nb095_fresh_167 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_047 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_035 D R S_cls E))).fv)
      0

theorem nb095_fresh_168 (f : Var) :
    (nb095_alpha_dummy_046 f) ∉
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_037 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_037 f))).fv)
      0

theorem nb095_fresh_169 (f : Var) :
    (nb095_alpha_dummy_042 f) ∉
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_037 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv)
      0

theorem nb095_fresh_170 (f : Var) :
    (nb095_alpha_dummy_048 f) ∉
      (((Class.cv (nb095_alpha_dummy_038 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_038 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_038 f))).fv)
      0

theorem nb095_fresh_171 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_063 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) 0

theorem nb095_fresh_172 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_064 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) 1

theorem nb095_distinct_173 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_064 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_063, nb095_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_174 (f : Var) :
    (nb095_alpha_dummy_065 f) ∉ (((Class.cv (nb095_alpha_dummy_058 f))).fv) := by
  simpa only [nb095_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_058 f))).fv) 0

theorem nb095_fresh_175 (f : Var) :
    (nb095_alpha_dummy_066 f) ∉ (((Class.cv (nb095_alpha_dummy_058 f))).fv) := by
  simpa only [nb095_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_058 f))).fv) 1

theorem nb095_distinct_176 (f : Var) :
    (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_066 f) := by
  simpa only [nb095_alpha_dummy_065, nb095_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_058 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_177 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_069 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_178 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_179 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_071 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_180 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_069 D R S_cls E) ≠ (nb095_alpha_dummy_070 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_069, nb095_alpha_dummy_070] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_181 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_069 D R S_cls E) ≠ (nb095_alpha_dummy_071 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_069, nb095_alpha_dummy_071] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_182 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_071 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_070, nb095_alpha_dummy_071] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_183 (f : Var) :
    (nb095_alpha_dummy_072 f) ∉
      (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_184 (f : Var) :
    (nb095_alpha_dummy_073 f) ∉
      (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_185 (f : Var) :
    (nb095_alpha_dummy_074 f) ∉
      (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_074] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_186 (f : Var) :
    (nb095_alpha_dummy_072 f) ≠ (nb095_alpha_dummy_073 f) := by
  simpa only [nb095_alpha_dummy_072, nb095_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_187 (f : Var) :
    (nb095_alpha_dummy_072 f) ≠ (nb095_alpha_dummy_074 f) := by
  simpa only [nb095_alpha_dummy_072, nb095_alpha_dummy_074] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_188 (f : Var) :
    (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_074 f) := by
  simpa only [nb095_alpha_dummy_073, nb095_alpha_dummy_074] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_189 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_081 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv)
      0

theorem nb095_fresh_190 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_077 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_077] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_070 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv)
      0

theorem nb095_fresh_191 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_083 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_071 D R S_cls E))).fv)
      0

theorem nb095_fresh_192 (f : Var) :
    (nb095_alpha_dummy_082 f) ∉
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_073 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_073 f))).fv)
      0

theorem nb095_fresh_193 (f : Var) :
    (nb095_alpha_dummy_078 f) ∉
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_073 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv)
      0

theorem nb095_fresh_194 (f : Var) :
    (nb095_alpha_dummy_084 f) ∉
      (((Class.cv (nb095_alpha_dummy_074 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_074 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_074 f))).fv)
      0

theorem nb095_fresh_195 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_097 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv)
      0

theorem nb095_fresh_196 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_098 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv)
      1

theorem nb095_distinct_197 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_097 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_097, nb095_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_198 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_133 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb095_fresh_199 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_134 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv)
      1

theorem nb095_distinct_200 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_133 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_133, nb095_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_201 (f : Var) :
    (nb095_alpha_dummy_099 f) ∉
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_099] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv)
      0

theorem nb095_fresh_202 (f : Var) :
    (nb095_alpha_dummy_100 f) ∉
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_094 f))).fv)
      1

theorem nb095_distinct_203 (f : Var) :
    (nb095_alpha_dummy_099 f) ≠ (nb095_alpha_dummy_100 f) := by
  simpa only [nb095_alpha_dummy_099, nb095_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_094 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_204 (f : Var) :
    (nb095_alpha_dummy_135 f) ∉
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_135] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv)
      0

theorem nb095_fresh_205 (f : Var) :
    (nb095_alpha_dummy_136 f) ∉
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_136] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv)
      1

theorem nb095_distinct_206 (f : Var) :
    (nb095_alpha_dummy_135 f) ≠ (nb095_alpha_dummy_136 f) := by
  simpa only [nb095_alpha_dummy_135, nb095_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_207 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_105 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) 0

theorem nb095_fresh_208 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_106 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) 1

theorem nb095_distinct_209 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_106 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_105, nb095_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_210 (f : Var) :
    (nb095_alpha_dummy_107 f) ∉ (((Class.cv (nb095_alpha_dummy_100 f))).fv) := by
  simpa only [nb095_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_100 f))).fv) 0

theorem nb095_fresh_211 (f : Var) :
    (nb095_alpha_dummy_108 f) ∉ (((Class.cv (nb095_alpha_dummy_100 f))).fv) := by
  simpa only [nb095_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_100 f))).fv) 1

theorem nb095_distinct_212 (f : Var) :
    (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_108 f) := by
  simpa only [nb095_alpha_dummy_107, nb095_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_213 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_111 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_214 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_112] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_215 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_113 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_216 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_111 D R S_cls E) ≠ (nb095_alpha_dummy_112 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_111, nb095_alpha_dummy_112] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_217 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_111 D R S_cls E) ≠ (nb095_alpha_dummy_113 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_111, nb095_alpha_dummy_113] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_218 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_113 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_112, nb095_alpha_dummy_113] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_219 (f : Var) :
    (nb095_alpha_dummy_114 f) ∉
      (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_114] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_220 (f : Var) :
    (nb095_alpha_dummy_115 f) ∉
      (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_115] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_221 (f : Var) :
    (nb095_alpha_dummy_116 f) ∉
      (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_116] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_222 (f : Var) :
    (nb095_alpha_dummy_114 f) ≠ (nb095_alpha_dummy_115 f) := by
  simpa only [nb095_alpha_dummy_114, nb095_alpha_dummy_115] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_223 (f : Var) :
    (nb095_alpha_dummy_114 f) ≠ (nb095_alpha_dummy_116 f) := by
  simpa only [nb095_alpha_dummy_114, nb095_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_224 (f : Var) :
    (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_116 f) := by
  simpa only [nb095_alpha_dummy_115, nb095_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_225 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_123 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv)
      0

theorem nb095_fresh_226 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_119 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_112 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv)
      0

theorem nb095_fresh_227 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_125 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_113 D R S_cls E))).fv)
      0

theorem nb095_fresh_228 (f : Var) :
    (nb095_alpha_dummy_124 f) ∉
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_115 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_115 f))).fv)
      0

theorem nb095_fresh_229 (f : Var) :
    (nb095_alpha_dummy_120 f) ∉
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_115 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv)
      0

theorem nb095_fresh_230 (f : Var) :
    (nb095_alpha_dummy_126 f) ∉
      (((Class.cv (nb095_alpha_dummy_116 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_116 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_116 f))).fv)
      0

theorem nb095_fresh_231 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_141 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) 0

theorem nb095_fresh_232 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_142 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) 1

theorem nb095_distinct_233 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_142 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_141, nb095_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_234 (f : Var) :
    (nb095_alpha_dummy_143 f) ∉ (((Class.cv (nb095_alpha_dummy_136 f))).fv) := by
  simpa only [nb095_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_136 f))).fv) 0

theorem nb095_fresh_235 (f : Var) :
    (nb095_alpha_dummy_144 f) ∉ (((Class.cv (nb095_alpha_dummy_136 f))).fv) := by
  simpa only [nb095_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_136 f))).fv) 1

theorem nb095_distinct_236 (f : Var) :
    (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_144 f) := by
  simpa only [nb095_alpha_dummy_143, nb095_alpha_dummy_144] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_136 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_237 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_147 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_238 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_148] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_239 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_149 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_240 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_147 D R S_cls E) ≠ (nb095_alpha_dummy_148 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_147, nb095_alpha_dummy_148] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_241 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_147 D R S_cls E) ≠ (nb095_alpha_dummy_149 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_147, nb095_alpha_dummy_149] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_242 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_149 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_148, nb095_alpha_dummy_149] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_243 (f : Var) :
    (nb095_alpha_dummy_150 f) ∉
      (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_150] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_244 (f : Var) :
    (nb095_alpha_dummy_151 f) ∉
      (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_151] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_245 (f : Var) :
    (nb095_alpha_dummy_152 f) ∉
      (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_152] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_246 (f : Var) :
    (nb095_alpha_dummy_150 f) ≠ (nb095_alpha_dummy_151 f) := by
  simpa only [nb095_alpha_dummy_150, nb095_alpha_dummy_151] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_247 (f : Var) :
    (nb095_alpha_dummy_150 f) ≠ (nb095_alpha_dummy_152 f) := by
  simpa only [nb095_alpha_dummy_150, nb095_alpha_dummy_152] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_248 (f : Var) :
    (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_152 f) := by
  simpa only [nb095_alpha_dummy_151, nb095_alpha_dummy_152] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_249 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_159 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_159] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv)
      0

theorem nb095_fresh_250 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_155 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_148 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv)
      0

theorem nb095_fresh_251 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_161 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_149 D R S_cls E))).fv)
      0

theorem nb095_fresh_252 (f : Var) :
    (nb095_alpha_dummy_160 f) ∉
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_151 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_160] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_151 f))).fv)
      0

theorem nb095_fresh_253 (f : Var) :
    (nb095_alpha_dummy_156 f) ∉
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_151 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv)
      0

theorem nb095_fresh_254 (f : Var) :
    (nb095_alpha_dummy_162 f) ∉
      (((Class.cv (nb095_alpha_dummy_152 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_162] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_152 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_152 f))).fv)
      0

theorem nb095_fresh_255 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_177 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) 0

theorem nb095_fresh_256 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_178 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_178] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) 1

theorem nb095_distinct_257 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_178 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_177, nb095_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_258 (f : Var) :
    (nb095_alpha_dummy_179 f) ∉ (((Class.cv (nb095_alpha_dummy_172 f))).fv) := by
  simpa only [nb095_alpha_dummy_179] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_172 f))).fv) 0

theorem nb095_fresh_259 (f : Var) :
    (nb095_alpha_dummy_180 f) ∉ (((Class.cv (nb095_alpha_dummy_172 f))).fv) := by
  simpa only [nb095_alpha_dummy_180] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_172 f))).fv) 1

theorem nb095_distinct_260 (f : Var) :
    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_180 f) := by
  simpa only [nb095_alpha_dummy_179, nb095_alpha_dummy_180] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_172 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_261 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_183 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_183] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_262 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_184] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_263 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_185 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_185] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_264 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_183 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_183, nb095_alpha_dummy_184] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_265 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_183 D R S_cls E) ≠ (nb095_alpha_dummy_185 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_183, nb095_alpha_dummy_185] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_266 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_185 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_184, nb095_alpha_dummy_185] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_267 (f : Var) :
    (nb095_alpha_dummy_186 f) ∉
      (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_186] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_268 (f : Var) :
    (nb095_alpha_dummy_187 f) ∉
      (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_187] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_269 (f : Var) :
    (nb095_alpha_dummy_188 f) ∉
      (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_188] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_270 (f : Var) :
    (nb095_alpha_dummy_186 f) ≠ (nb095_alpha_dummy_187 f) := by
  simpa only [nb095_alpha_dummy_186, nb095_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_271 (f : Var) :
    (nb095_alpha_dummy_186 f) ≠ (nb095_alpha_dummy_188 f) := by
  simpa only [nb095_alpha_dummy_186, nb095_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_272 (f : Var) :
    (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_188 f) := by
  simpa only [nb095_alpha_dummy_187, nb095_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_273 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_195 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_195] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv)
      0

theorem nb095_fresh_274 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_191 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_191] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_184 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv)
      0

theorem nb095_fresh_275 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_197 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_185 D R S_cls E))).fv)
      0

theorem nb095_fresh_276 (f : Var) :
    (nb095_alpha_dummy_196 f) ∉
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_187 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_196] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_187 f))).fv)
      0

theorem nb095_fresh_277 (f : Var) :
    (nb095_alpha_dummy_192 f) ∉
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_192] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv)
      0

theorem nb095_fresh_278 (f : Var) :
    (nb095_alpha_dummy_198 f) ∉
      (((Class.cv (nb095_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_198] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_188 f))).fv)
      0

theorem nb095_fresh_279 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_209 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv)
      0

theorem nb095_fresh_280 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_210 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv)
      1

theorem nb095_distinct_281 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_209 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_209, nb095_alpha_dummy_210] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_282 (f : Var) :
    (nb095_alpha_dummy_211 f) ∉
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_211] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv)
      0

theorem nb095_fresh_283 (f : Var) :
    (nb095_alpha_dummy_212 f) ∉
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_212] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_207 f))).fv)
      1

theorem nb095_distinct_284 (f : Var) :
    (nb095_alpha_dummy_211 f) ≠ (nb095_alpha_dummy_212 f) := by
  simpa only [nb095_alpha_dummy_211, nb095_alpha_dummy_212] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_207 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_285 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_217 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_217] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) 0

theorem nb095_fresh_286 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_218 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_218] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) 1

theorem nb095_distinct_287 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_218 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_217, nb095_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_288 (f : Var) :
    (nb095_alpha_dummy_219 f) ∉ (((Class.cv (nb095_alpha_dummy_212 f))).fv) := by
  simpa only [nb095_alpha_dummy_219] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_212 f))).fv) 0

theorem nb095_fresh_289 (f : Var) :
    (nb095_alpha_dummy_220 f) ∉ (((Class.cv (nb095_alpha_dummy_212 f))).fv) := by
  simpa only [nb095_alpha_dummy_220] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_212 f))).fv) 1

theorem nb095_distinct_290 (f : Var) :
    (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_220 f) := by
  simpa only [nb095_alpha_dummy_219, nb095_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_212 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_291 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_223 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_223] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_292 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_224] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_293 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_225 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_225] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_294 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_223 D R S_cls E) ≠ (nb095_alpha_dummy_224 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_223, nb095_alpha_dummy_224] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_295 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_223 D R S_cls E) ≠ (nb095_alpha_dummy_225 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_223, nb095_alpha_dummy_225] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_296 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_225 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_224, nb095_alpha_dummy_225] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_297 (f : Var) :
    (nb095_alpha_dummy_226 f) ∉
      (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_226] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_298 (f : Var) :
    (nb095_alpha_dummy_227 f) ∉
      (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_227] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_299 (f : Var) :
    (nb095_alpha_dummy_228 f) ∉
      (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_228] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_300 (f : Var) :
    (nb095_alpha_dummy_226 f) ≠ (nb095_alpha_dummy_227 f) := by
  simpa only [nb095_alpha_dummy_226, nb095_alpha_dummy_227] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_301 (f : Var) :
    (nb095_alpha_dummy_226 f) ≠ (nb095_alpha_dummy_228 f) := by
  simpa only [nb095_alpha_dummy_226, nb095_alpha_dummy_228] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_302 (f : Var) :
    (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_228 f) := by
  simpa only [nb095_alpha_dummy_227, nb095_alpha_dummy_228] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_303 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_235 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_235] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv)
      0

theorem nb095_fresh_304 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_231 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_231] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_224 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv)
      0

theorem nb095_fresh_305 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_237 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_237] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_225 D R S_cls E))).fv)
      0

theorem nb095_fresh_306 (f : Var) :
    (nb095_alpha_dummy_236 f) ∉
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_227 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_236] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_227 f))).fv)
      0

theorem nb095_fresh_307 (f : Var) :
    (nb095_alpha_dummy_232 f) ∉
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_232] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_227 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv)
      0

theorem nb095_fresh_308 (f : Var) :
    (nb095_alpha_dummy_238 f) ∉
      (((Class.cv (nb095_alpha_dummy_228 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_238] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_228 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_228 f))).fv)
      0

theorem nb095_fresh_309 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_255 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_255] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv)
      0

theorem nb095_fresh_310 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_256 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_256] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv)
      1

theorem nb095_distinct_311 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_255 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_255, nb095_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_312 (x : Var) (R : Class) :
    (nb095_alpha_dummy_257 x R) ∉
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_257] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv)
      0

theorem nb095_fresh_313 (x : Var) (R : Class) :
    (nb095_alpha_dummy_258 x R) ∉
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_258] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv)
      1

theorem nb095_distinct_314 (x : Var) (R : Class) :
    (nb095_alpha_dummy_257 x R) ≠ (nb095_alpha_dummy_258 x R) := by
  simpa only [nb095_alpha_dummy_257, nb095_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_315 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_263 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_263] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) 0

theorem nb095_fresh_316 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_264 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_264] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) 1

theorem nb095_distinct_317 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_264 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_263, nb095_alpha_dummy_264] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_318 (x : Var) (R : Class) :
    (nb095_alpha_dummy_265 x R) ∉ (((Class.cv (nb095_alpha_dummy_258 x R))).fv) := by
  simpa only [nb095_alpha_dummy_265] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_258 x R))).fv) 0

theorem nb095_fresh_319 (x : Var) (R : Class) :
    (nb095_alpha_dummy_266 x R) ∉ (((Class.cv (nb095_alpha_dummy_258 x R))).fv) := by
  simpa only [nb095_alpha_dummy_266] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_258 x R))).fv) 1

theorem nb095_distinct_320 (x : Var) (R : Class) :
    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_266 x R) := by
  simpa only [nb095_alpha_dummy_265, nb095_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_258 x R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_321 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_269 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_322 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_323 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_271 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_271] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_324 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_269 D R S_cls E) ≠ (nb095_alpha_dummy_270 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_269, nb095_alpha_dummy_270] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_325 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_269 D R S_cls E) ≠ (nb095_alpha_dummy_271 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_269, nb095_alpha_dummy_271] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_326 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_271 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_270, nb095_alpha_dummy_271] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_327 (x : Var) (R : Class) :
    (nb095_alpha_dummy_272 x R) ∉
      (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_272] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_328 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ∉
      (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_273] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_329 (x : Var) (R : Class) :
    (nb095_alpha_dummy_274 x R) ∉
      (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_274] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_330 (x : Var) (R : Class) :
    (nb095_alpha_dummy_272 x R) ≠ (nb095_alpha_dummy_273 x R) := by
  simpa only [nb095_alpha_dummy_272, nb095_alpha_dummy_273] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_331 (x : Var) (R : Class) :
    (nb095_alpha_dummy_272 x R) ≠ (nb095_alpha_dummy_274 x R) := by
  simpa only [nb095_alpha_dummy_272, nb095_alpha_dummy_274] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_332 (x : Var) (R : Class) :
    (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_274 x R) := by
  simpa only [nb095_alpha_dummy_273, nb095_alpha_dummy_274] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_333 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_281 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_281] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv)
      0

theorem nb095_fresh_334 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_277 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_277] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_270 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv)
      0

theorem nb095_fresh_335 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_283 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_283] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_271 D R S_cls E))).fv)
      0

theorem nb095_fresh_336 (x : Var) (R : Class) :
    (nb095_alpha_dummy_282 x R) ∉
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_273 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_282] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_273 x R))).fv)
      0

theorem nb095_fresh_337 (x : Var) (R : Class) :
    (nb095_alpha_dummy_278 x R) ∉
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_278] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_273 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv)
      0

theorem nb095_fresh_338 (x : Var) (R : Class) :
    (nb095_alpha_dummy_284 x R) ∉
      (((Class.cv (nb095_alpha_dummy_274 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_284] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_274 x R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_274 x R))).fv)
      0

theorem nb095_fresh_339 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_299 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_299] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv)
      0

theorem nb095_fresh_340 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_300 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_300] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv)
      1

theorem nb095_distinct_341 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_299 D R S_cls E) ≠ (nb095_alpha_dummy_300 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_299, nb095_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_342 (f : Var) :
    (nb095_alpha_dummy_301 f) ∉
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_301] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv)
      0

theorem nb095_fresh_343 (f : Var) :
    (nb095_alpha_dummy_302 f) ∉
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_302] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_297 f))).fv)
      1

theorem nb095_distinct_344 (f : Var) :
    (nb095_alpha_dummy_301 f) ≠ (nb095_alpha_dummy_302 f) := by
  simpa only [nb095_alpha_dummy_301, nb095_alpha_dummy_302] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_297 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_345 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_307 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_307] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) 0

theorem nb095_fresh_346 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_308 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_308] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) 1

theorem nb095_distinct_347 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_308 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_307, nb095_alpha_dummy_308] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_348 (f : Var) :
    (nb095_alpha_dummy_309 f) ∉ (((Class.cv (nb095_alpha_dummy_302 f))).fv) := by
  simpa only [nb095_alpha_dummy_309] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_302 f))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
