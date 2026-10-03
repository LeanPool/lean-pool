/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part003

/-! NF weak partition development: NAR4H5C095M3Part004. -/


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

theorem nb095_fresh_349 (f : Var) :
    (nb095_alpha_dummy_310 f) ∉ (((Class.cv (nb095_alpha_dummy_302 f))).fv) := by
  simpa only [nb095_alpha_dummy_310] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_302 f))).fv) 1

theorem nb095_distinct_350 (f : Var) :
    (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_310 f) := by
  simpa only [nb095_alpha_dummy_309, nb095_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_302 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_351 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_313 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_313] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_352 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_314] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_353 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_315 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_315] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_354 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_313 D R S_cls E) ≠ (nb095_alpha_dummy_314 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_313, nb095_alpha_dummy_314] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_355 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_313 D R S_cls E) ≠ (nb095_alpha_dummy_315 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_313, nb095_alpha_dummy_315] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_356 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_315 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_314, nb095_alpha_dummy_315] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_357 (f : Var) :
    (nb095_alpha_dummy_316 f) ∉
      (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_316] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_358 (f : Var) :
    (nb095_alpha_dummy_317 f) ∉
      (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_317] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_359 (f : Var) :
    (nb095_alpha_dummy_318 f) ∉
      (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_318] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_360 (f : Var) :
    (nb095_alpha_dummy_316 f) ≠ (nb095_alpha_dummy_317 f) := by
  simpa only [nb095_alpha_dummy_316, nb095_alpha_dummy_317] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_361 (f : Var) :
    (nb095_alpha_dummy_316 f) ≠ (nb095_alpha_dummy_318 f) := by
  simpa only [nb095_alpha_dummy_316, nb095_alpha_dummy_318] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_362 (f : Var) :
    (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_318 f) := by
  simpa only [nb095_alpha_dummy_317, nb095_alpha_dummy_318] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_363 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_325 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_325] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv)
      0

theorem nb095_fresh_364 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_321 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_321] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_314 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv)
      0

theorem nb095_fresh_365 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_327 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_327] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_315 D R S_cls E))).fv)
      0

theorem nb095_fresh_366 (f : Var) :
    (nb095_alpha_dummy_326 f) ∉
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_317 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_326] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_317 f))).fv)
      0

theorem nb095_fresh_367 (f : Var) :
    (nb095_alpha_dummy_322 f) ∉
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_322] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_317 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv)
      0

theorem nb095_fresh_368 (f : Var) :
    (nb095_alpha_dummy_328 f) ∉
      (((Class.cv (nb095_alpha_dummy_318 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_328] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_318 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_318 f))).fv)
      0

theorem nb095_fresh_369 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_345 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_345] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv)
      0

theorem nb095_fresh_370 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_346 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_346] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv)
      1

theorem nb095_distinct_371 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_345 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_345, nb095_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_372 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_347 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_347] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv)
      0

theorem nb095_fresh_373 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_348 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_348] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv)
      1

theorem nb095_distinct_374 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_347 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) := by
  simpa only [nb095_alpha_dummy_347, nb095_alpha_dummy_348] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_375 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_353 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_353] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) 0

theorem nb095_fresh_376 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_354 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_354] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) 1

theorem nb095_distinct_377 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_354 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_353, nb095_alpha_dummy_354] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_378 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_355 u S_cls) ∉ (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_355] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) 0

theorem nb095_fresh_379 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_356 u S_cls) ∉ (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_356] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) 1

theorem nb095_distinct_380 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_356 u S_cls) := by
  simpa only [nb095_alpha_dummy_355, nb095_alpha_dummy_356] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_fresh_381 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_359 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_359] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_382 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_360] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_383 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_361 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_361] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_384 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_359 D R S_cls E) ≠ (nb095_alpha_dummy_360 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_359, nb095_alpha_dummy_360] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_385 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_359 D R S_cls E) ≠ (nb095_alpha_dummy_361 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_359, nb095_alpha_dummy_361] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_386 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_361 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_360, nb095_alpha_dummy_361] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_387 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_362 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_362] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_388 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_363] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_389 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_364 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_364] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_390 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_362 u S_cls) ≠ (nb095_alpha_dummy_363 u S_cls) := by
  simpa only [nb095_alpha_dummy_362, nb095_alpha_dummy_363] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_391 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_362 u S_cls) ≠ (nb095_alpha_dummy_364 u S_cls) := by
  simpa only [nb095_alpha_dummy_362, nb095_alpha_dummy_364] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_392 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_364 u S_cls) := by
  simpa only [nb095_alpha_dummy_363, nb095_alpha_dummy_364] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_393 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_371 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_371] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv)
      0

theorem nb095_fresh_394 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_367 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_367] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_360 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv)
      0

theorem nb095_fresh_395 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_373 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_373] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_361 D R S_cls E))).fv)
      0

theorem nb095_fresh_396 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_372 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_372] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv)
      0

theorem nb095_fresh_397 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_368 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_368] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_363 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv)
      0

theorem nb095_fresh_398 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_374 u S_cls) ∉
      (((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_374] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv ∪
        ((Class.cv (nb095_alpha_dummy_364 u S_cls))).fv)
      0

theorem nb095_fresh_399 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_393 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_393] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv)
      0

theorem nb095_fresh_400 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_394 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_394] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv)
      1

theorem nb095_distinct_401 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_393 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_393, nb095_alpha_dummy_394] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_402 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_429 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_429] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv)
      0

theorem nb095_fresh_403 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_430 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_430] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv)
      1

theorem nb095_distinct_404 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_429 D R S_cls E) ≠ (nb095_alpha_dummy_430 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_429, nb095_alpha_dummy_430] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_405 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_543 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_543] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv)
      0

theorem nb095_fresh_406 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_544 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_544] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv)
      1

theorem nb095_distinct_407 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_543 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_543, nb095_alpha_dummy_544] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_408 (f : Var) :
    (nb095_alpha_dummy_395 f) ∉
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_395] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv)
      0

theorem nb095_fresh_409 (f : Var) :
    (nb095_alpha_dummy_396 f) ∉
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_396] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv)
      1

theorem nb095_distinct_410 (f : Var) :
    (nb095_alpha_dummy_395 f) ≠ (nb095_alpha_dummy_396 f) := by
  simpa only [nb095_alpha_dummy_395, nb095_alpha_dummy_396] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_389 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_411 (f : Var) :
    (nb095_alpha_dummy_431 f) ∉
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_431] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv)
      0

theorem nb095_fresh_412 (f : Var) :
    (nb095_alpha_dummy_432 f) ∉
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_432] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_390 f))).fv)
      1

theorem nb095_distinct_413 (f : Var) :
    (nb095_alpha_dummy_431 f) ≠ (nb095_alpha_dummy_432 f) := by
  simpa only [nb095_alpha_dummy_431, nb095_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_390 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_414 (f : Var) :
    (nb095_alpha_dummy_545 f) ∉
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_545] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv)
      0

theorem nb095_fresh_415 (f : Var) :
    (nb095_alpha_dummy_546 f) ∉
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_546] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv)
      1

theorem nb095_distinct_416 (f : Var) :
    (nb095_alpha_dummy_545 f) ≠ (nb095_alpha_dummy_546 f) := by
  simpa only [nb095_alpha_dummy_545, nb095_alpha_dummy_546] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_389 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_417 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_401 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_401] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) 0

theorem nb095_fresh_418 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_402 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_402] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) 1

theorem nb095_distinct_419 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_402 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_401, nb095_alpha_dummy_402] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_420 (f : Var) :
    (nb095_alpha_dummy_403 f) ∉ (((Class.cv (nb095_alpha_dummy_396 f))).fv) := by
  simpa only [nb095_alpha_dummy_403] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_396 f))).fv) 0

theorem nb095_fresh_421 (f : Var) :
    (nb095_alpha_dummy_404 f) ∉ (((Class.cv (nb095_alpha_dummy_396 f))).fv) := by
  simpa only [nb095_alpha_dummy_404] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_396 f))).fv) 1

theorem nb095_distinct_422 (f : Var) :
    (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_404 f) := by
  simpa only [nb095_alpha_dummy_403, nb095_alpha_dummy_404] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_396 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_423 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_407 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_407] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_424 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_408] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_425 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_409 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_409] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_426 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_407 D R S_cls E) ≠ (nb095_alpha_dummy_408 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_407, nb095_alpha_dummy_408] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_427 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_407 D R S_cls E) ≠ (nb095_alpha_dummy_409 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_407, nb095_alpha_dummy_409] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_428 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_409 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_408, nb095_alpha_dummy_409] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_429 (f : Var) :
    (nb095_alpha_dummy_410 f) ∉
      (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_410] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_430 (f : Var) :
    (nb095_alpha_dummy_411 f) ∉
      (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_411] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_431 (f : Var) :
    (nb095_alpha_dummy_412 f) ∉
      (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_412] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_432 (f : Var) :
    (nb095_alpha_dummy_410 f) ≠ (nb095_alpha_dummy_411 f) := by
  simpa only [nb095_alpha_dummy_410, nb095_alpha_dummy_411] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_433 (f : Var) :
    (nb095_alpha_dummy_410 f) ≠ (nb095_alpha_dummy_412 f) := by
  simpa only [nb095_alpha_dummy_410, nb095_alpha_dummy_412] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_434 (f : Var) :
    (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_412 f) := by
  simpa only [nb095_alpha_dummy_411, nb095_alpha_dummy_412] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_435 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_419 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_419] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv)
      0

theorem nb095_fresh_436 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_415 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_415] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_408 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv)
      0

theorem nb095_fresh_437 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_421 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_421] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_409 D R S_cls E))).fv)
      0

theorem nb095_fresh_438 (f : Var) :
    (nb095_alpha_dummy_420 f) ∉
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_411 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_420] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_411 f))).fv)
      0

theorem nb095_fresh_439 (f : Var) :
    (nb095_alpha_dummy_416 f) ∉
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_416] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_411 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv)
      0

theorem nb095_fresh_440 (f : Var) :
    (nb095_alpha_dummy_422 f) ∉
      (((Class.cv (nb095_alpha_dummy_412 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_422] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_412 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_412 f))).fv)
      0

theorem nb095_fresh_441 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_437 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_437] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) 0

theorem nb095_fresh_442 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_438 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_438] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) 1

theorem nb095_distinct_443 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_438 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_437, nb095_alpha_dummy_438] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_444 (f : Var) :
    (nb095_alpha_dummy_439 f) ∉ (((Class.cv (nb095_alpha_dummy_432 f))).fv) := by
  simpa only [nb095_alpha_dummy_439] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_432 f))).fv) 0

theorem nb095_fresh_445 (f : Var) :
    (nb095_alpha_dummy_440 f) ∉ (((Class.cv (nb095_alpha_dummy_432 f))).fv) := by
  simpa only [nb095_alpha_dummy_440] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_432 f))).fv) 1

theorem nb095_distinct_446 (f : Var) :
    (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_440 f) := by
  simpa only [nb095_alpha_dummy_439, nb095_alpha_dummy_440] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_432 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_447 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_443 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_443] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_448 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_444] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_449 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_445 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_445] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_450 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_443 D R S_cls E) ≠ (nb095_alpha_dummy_444 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_443, nb095_alpha_dummy_444] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_451 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_443 D R S_cls E) ≠ (nb095_alpha_dummy_445 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_443, nb095_alpha_dummy_445] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_452 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_445 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_444, nb095_alpha_dummy_445] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_453 (f : Var) :
    (nb095_alpha_dummy_446 f) ∉
      (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_446] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_454 (f : Var) :
    (nb095_alpha_dummy_447 f) ∉
      (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_447] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_455 (f : Var) :
    (nb095_alpha_dummy_448 f) ∉
      (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_448] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_456 (f : Var) :
    (nb095_alpha_dummy_446 f) ≠ (nb095_alpha_dummy_447 f) := by
  simpa only [nb095_alpha_dummy_446, nb095_alpha_dummy_447] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_457 (f : Var) :
    (nb095_alpha_dummy_446 f) ≠ (nb095_alpha_dummy_448 f) := by
  simpa only [nb095_alpha_dummy_446, nb095_alpha_dummy_448] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_458 (f : Var) :
    (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_448 f) := by
  simpa only [nb095_alpha_dummy_447, nb095_alpha_dummy_448] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_459 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_455 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_455] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv)
      0

theorem nb095_fresh_460 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_451 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_451] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_444 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv)
      0

theorem nb095_fresh_461 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_457 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_457] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_445 D R S_cls E))).fv)
      0

theorem nb095_fresh_462 (f : Var) :
    (nb095_alpha_dummy_456 f) ∉
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_447 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_456] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_447 f))).fv)
      0

theorem nb095_fresh_463 (f : Var) :
    (nb095_alpha_dummy_452 f) ∉
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_452] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_447 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv)
      0

theorem nb095_fresh_464 (f : Var) :
    (nb095_alpha_dummy_458 f) ∉
      (((Class.cv (nb095_alpha_dummy_448 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_458] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_448 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_448 f))).fv)
      0

theorem nb095_fresh_465 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_471 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_471] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv)
      0

theorem nb095_fresh_466 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_472 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_472] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv)
      1

theorem nb095_distinct_467 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_471 D R S_cls E) ≠ (nb095_alpha_dummy_472 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_471, nb095_alpha_dummy_472] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_468 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_507 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_507] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv)
      0

theorem nb095_fresh_469 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_508 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_508] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv)
      1

theorem nb095_distinct_470 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_507 D R S_cls E) ≠ (nb095_alpha_dummy_508 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_507, nb095_alpha_dummy_508] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_471 (f : Var) :
    (nb095_alpha_dummy_473 f) ∉
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_473] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv)
      0

theorem nb095_fresh_472 (f : Var) :
    (nb095_alpha_dummy_474 f) ∉
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_474] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_468 f))).fv)
      1

theorem nb095_distinct_473 (f : Var) :
    (nb095_alpha_dummy_473 f) ≠ (nb095_alpha_dummy_474 f) := by
  simpa only [nb095_alpha_dummy_473, nb095_alpha_dummy_474] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_468 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_474 (f : Var) :
    (nb095_alpha_dummy_509 f) ∉
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_509] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv)
      0

theorem nb095_fresh_475 (f : Var) :
    (nb095_alpha_dummy_510 f) ∉
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_510] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_467 f))).fv)
      1

theorem nb095_distinct_476 (f : Var) :
    (nb095_alpha_dummy_509 f) ≠ (nb095_alpha_dummy_510 f) := by
  simpa only [nb095_alpha_dummy_509, nb095_alpha_dummy_510] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_467 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_477 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_479 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_479] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) 0

theorem nb095_fresh_478 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_480 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_480] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) 1

theorem nb095_distinct_479 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_480 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_479, nb095_alpha_dummy_480] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_480 (f : Var) :
    (nb095_alpha_dummy_481 f) ∉ (((Class.cv (nb095_alpha_dummy_474 f))).fv) := by
  simpa only [nb095_alpha_dummy_481] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_474 f))).fv) 0

theorem nb095_fresh_481 (f : Var) :
    (nb095_alpha_dummy_482 f) ∉ (((Class.cv (nb095_alpha_dummy_474 f))).fv) := by
  simpa only [nb095_alpha_dummy_482] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_474 f))).fv) 1

theorem nb095_distinct_482 (f : Var) :
    (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_482 f) := by
  simpa only [nb095_alpha_dummy_481, nb095_alpha_dummy_482] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_474 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_483 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_485 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_485] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_484 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_486] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_485 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_487 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_487] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_486 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_485 D R S_cls E) ≠ (nb095_alpha_dummy_486 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_485, nb095_alpha_dummy_486] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_487 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_485 D R S_cls E) ≠ (nb095_alpha_dummy_487 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_485, nb095_alpha_dummy_487] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_487 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_486, nb095_alpha_dummy_487] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_489 (f : Var) :
    (nb095_alpha_dummy_488 f) ∉
      (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_488] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_490 (f : Var) :
    (nb095_alpha_dummy_489 f) ∉
      (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_489] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_491 (f : Var) :
    (nb095_alpha_dummy_490 f) ∉
      (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_490] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_492 (f : Var) :
    (nb095_alpha_dummy_488 f) ≠ (nb095_alpha_dummy_489 f) := by
  simpa only [nb095_alpha_dummy_488, nb095_alpha_dummy_489] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_493 (f : Var) :
    (nb095_alpha_dummy_488 f) ≠ (nb095_alpha_dummy_490 f) := by
  simpa only [nb095_alpha_dummy_488, nb095_alpha_dummy_490] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_494 (f : Var) :
    (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_490 f) := by
  simpa only [nb095_alpha_dummy_489, nb095_alpha_dummy_490] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_495 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_497 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_497] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv)
      0

theorem nb095_fresh_496 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_493 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_493] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_486 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv)
      0

theorem nb095_fresh_497 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_499 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_499] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_487 D R S_cls E))).fv)
      0

theorem nb095_fresh_498 (f : Var) :
    (nb095_alpha_dummy_498 f) ∉
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_489 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_498] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_489 f))).fv)
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

theorem nb095_fresh_499 (f : Var) :
    (nb095_alpha_dummy_494 f) ∉
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_494] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_489 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv)
      0

theorem nb095_fresh_500 (f : Var) :
    (nb095_alpha_dummy_500 f) ∉
      (((Class.cv (nb095_alpha_dummy_490 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_500] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_490 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_490 f))).fv)
      0

theorem nb095_fresh_501 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_515 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_515] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) 0

theorem nb095_fresh_502 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_516 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_516] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) 1

theorem nb095_distinct_503 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_516 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_515, nb095_alpha_dummy_516] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_504 (f : Var) :
    (nb095_alpha_dummy_517 f) ∉ (((Class.cv (nb095_alpha_dummy_510 f))).fv) := by
  simpa only [nb095_alpha_dummy_517] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_510 f))).fv) 0

theorem nb095_fresh_505 (f : Var) :
    (nb095_alpha_dummy_518 f) ∉ (((Class.cv (nb095_alpha_dummy_510 f))).fv) := by
  simpa only [nb095_alpha_dummy_518] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_510 f))).fv) 1

theorem nb095_distinct_506 (f : Var) :
    (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_518 f) := by
  simpa only [nb095_alpha_dummy_517, nb095_alpha_dummy_518] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_510 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_507 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_521 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_521] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_522] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_509 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_523 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_523] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_521 D R S_cls E) ≠ (nb095_alpha_dummy_522 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_521, nb095_alpha_dummy_522] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_511 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_521 D R S_cls E) ≠ (nb095_alpha_dummy_523 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_521, nb095_alpha_dummy_523] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_523 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_522, nb095_alpha_dummy_523] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_513 (f : Var) :
    (nb095_alpha_dummy_524 f) ∉
      (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_524] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_514 (f : Var) :
    (nb095_alpha_dummy_525 f) ∉
      (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_525] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_515 (f : Var) :
    (nb095_alpha_dummy_526 f) ∉
      (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_526] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_516 (f : Var) :
    (nb095_alpha_dummy_524 f) ≠ (nb095_alpha_dummy_525 f) := by
  simpa only [nb095_alpha_dummy_524, nb095_alpha_dummy_525] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_517 (f : Var) :
    (nb095_alpha_dummy_524 f) ≠ (nb095_alpha_dummy_526 f) := by
  simpa only [nb095_alpha_dummy_524, nb095_alpha_dummy_526] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_518 (f : Var) :
    (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_526 f) := by
  simpa only [nb095_alpha_dummy_525, nb095_alpha_dummy_526] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_519 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_533 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_533] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv)
      0

theorem nb095_fresh_520 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_529 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_529] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_522 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv)
      0

theorem nb095_fresh_521 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_535 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_535] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_523 D R S_cls E))).fv)
      0

theorem nb095_fresh_522 (f : Var) :
    (nb095_alpha_dummy_534 f) ∉
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_525 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_534] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_525 f))).fv)
      0

theorem nb095_fresh_523 (f : Var) :
    (nb095_alpha_dummy_530 f) ∉
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_530] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_525 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv)
      0

theorem nb095_fresh_524 (f : Var) :
    (nb095_alpha_dummy_536 f) ∉
      (((Class.cv (nb095_alpha_dummy_526 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_536] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_526 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_526 f))).fv)
      0

theorem nb095_fresh_525 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_551 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_551] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) 0

theorem nb095_fresh_526 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_552 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_552] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) 1

theorem nb095_distinct_527 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_552 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_551, nb095_alpha_dummy_552] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_528 (f : Var) :
    (nb095_alpha_dummy_553 f) ∉ (((Class.cv (nb095_alpha_dummy_546 f))).fv) := by
  simpa only [nb095_alpha_dummy_553] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_546 f))).fv) 0

theorem nb095_fresh_529 (f : Var) :
    (nb095_alpha_dummy_554 f) ∉ (((Class.cv (nb095_alpha_dummy_546 f))).fv) := by
  simpa only [nb095_alpha_dummy_554] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_546 f))).fv) 1

theorem nb095_distinct_530 (f : Var) :
    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_554 f) := by
  simpa only [nb095_alpha_dummy_553, nb095_alpha_dummy_554] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_546 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_531 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_557 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_557] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_532 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_558] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_533 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_559 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_559] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_534 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_557 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_557, nb095_alpha_dummy_558] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_535 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_557 D R S_cls E) ≠ (nb095_alpha_dummy_559 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_557, nb095_alpha_dummy_559] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_536 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_559 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_558, nb095_alpha_dummy_559] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_537 (f : Var) :
    (nb095_alpha_dummy_560 f) ∉
      (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_560] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_538 (f : Var) :
    (nb095_alpha_dummy_561 f) ∉
      (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_561] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_539 (f : Var) :
    (nb095_alpha_dummy_562 f) ∉
      (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_562] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_540 (f : Var) :
    (nb095_alpha_dummy_560 f) ≠ (nb095_alpha_dummy_561 f) := by
  simpa only [nb095_alpha_dummy_560, nb095_alpha_dummy_561] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_541 (f : Var) :
    (nb095_alpha_dummy_560 f) ≠ (nb095_alpha_dummy_562 f) := by
  simpa only [nb095_alpha_dummy_560, nb095_alpha_dummy_562] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_542 (f : Var) :
    (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_562 f) := by
  simpa only [nb095_alpha_dummy_561, nb095_alpha_dummy_562] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_543 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_569 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_569] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv)
      0

theorem nb095_fresh_544 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_565 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_565] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_558 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv)
      0

theorem nb095_fresh_545 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_571 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_571] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_559 D R S_cls E))).fv)
      0

theorem nb095_fresh_546 (f : Var) :
    (nb095_alpha_dummy_570 f) ∉
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_561 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_570] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_561 f))).fv)
      0

theorem nb095_fresh_547 (f : Var) :
    (nb095_alpha_dummy_566 f) ∉
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_566] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_561 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv)
      0

theorem nb095_fresh_548 (f : Var) :
    (nb095_alpha_dummy_572 f) ∉
      (((Class.cv (nb095_alpha_dummy_562 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_572] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_562 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_562 f))).fv)
      0

theorem nb095_fresh_549 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_587 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_587] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) 0

theorem nb095_fresh_550 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_588 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_588] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) 1

theorem nb095_distinct_551 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_587 D R S_cls E) ≠ (nb095_alpha_dummy_588 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_587, nb095_alpha_dummy_588] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_552 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_589 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_589] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_553 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_590 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_590] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_554 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_590 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_589, nb095_alpha_dummy_590] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_555 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_593 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_593] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_556 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_594] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_557 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_595 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_595] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_558 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_593 D R S_cls E) ≠ (nb095_alpha_dummy_594 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_593, nb095_alpha_dummy_594] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_559 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_593 D R S_cls E) ≠ (nb095_alpha_dummy_595 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_593, nb095_alpha_dummy_595] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_560 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_594 D R S_cls E) ≠ (nb095_alpha_dummy_595 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_594, nb095_alpha_dummy_595] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_561 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_596 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_596] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_562 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_597] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_563 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_598 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_598] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_564 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_596 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_597 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_596, nb095_alpha_dummy_597] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_565 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_596 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_598 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_596, nb095_alpha_dummy_598] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_566 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_597 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_598 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_597, nb095_alpha_dummy_598] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_567 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_605 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_605] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv)
      0

theorem nb095_fresh_568 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_601 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_601] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_594 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv)
      0

theorem nb095_fresh_569 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_607 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_607] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_595 D R S_cls E))).fv)
      0

theorem nb095_fresh_570 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_606 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_606] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_571 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_602 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_602] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_597 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_572 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_608 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_608] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_598 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_573 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_625 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_625] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv)
      0

theorem nb095_fresh_574 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_626 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_626] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv)
      1

theorem nb095_distinct_575 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_625 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_625, nb095_alpha_dummy_626] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_576 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_627 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_627] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv)
      0

theorem nb095_fresh_577 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_628 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_628] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv)
      1

theorem nb095_distinct_578 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_627 x D R) ≠ (nb095_alpha_dummy_628 x D R) := by
  simpa only [nb095_alpha_dummy_627, nb095_alpha_dummy_628] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_579 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_633 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_633] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) 0

theorem nb095_fresh_580 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_634 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_634] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) 1

theorem nb095_distinct_581 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_633 D R S_cls E) ≠ (nb095_alpha_dummy_634 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_633, nb095_alpha_dummy_634] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_582 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_635 x D R) ∉ (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) := by
  simpa only [nb095_alpha_dummy_635] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) 0

theorem nb095_fresh_583 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_636 x D R) ∉ (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) := by
  simpa only [nb095_alpha_dummy_636] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) 1

theorem nb095_distinct_584 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_636 x D R) := by
  simpa only [nb095_alpha_dummy_635, nb095_alpha_dummy_636] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_585 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_639 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_639] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_586 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_640] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_587 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_641 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_641] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_588 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_639 D R S_cls E) ≠ (nb095_alpha_dummy_640 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_639, nb095_alpha_dummy_640] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_589 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_639 D R S_cls E) ≠ (nb095_alpha_dummy_641 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_639, nb095_alpha_dummy_641] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_590 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_641 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_640, nb095_alpha_dummy_641] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_591 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_642 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_642] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_592 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_643] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_593 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_644 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_644] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_594 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_642 x D R) ≠ (nb095_alpha_dummy_643 x D R) := by
  simpa only [nb095_alpha_dummy_642, nb095_alpha_dummy_643] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_595 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_642 x D R) ≠ (nb095_alpha_dummy_644 x D R) := by
  simpa only [nb095_alpha_dummy_642, nb095_alpha_dummy_644] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_596 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_644 x D R) := by
  simpa only [nb095_alpha_dummy_643, nb095_alpha_dummy_644] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_597 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_651 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_651] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv)
      0

theorem nb095_fresh_598 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_647 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_647] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_640 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv)
      0

theorem nb095_fresh_599 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_653 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_653] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_641 D R S_cls E))).fv)
      0

theorem nb095_fresh_600 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_652 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_643 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_652] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_643 x D R))).fv)
      0

theorem nb095_fresh_601 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_648 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_648] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_643 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv)
      0

theorem nb095_fresh_602 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_654 x D R) ∉
      (((Class.cv (nb095_alpha_dummy_644 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_654] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_644 x D R))).fv ∪
        ((Class.cv (nb095_alpha_dummy_644 x D R))).fv)
      0

theorem nb095_fresh_603 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_715 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_715] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) 0

theorem nb095_fresh_604 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_716 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_716] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) 1

theorem nb095_distinct_605 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_715 D R S_cls E) ≠ (nb095_alpha_dummy_716 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_715, nb095_alpha_dummy_716] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_606 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_717 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_717] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_607 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_718 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_718] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_608 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_718 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_717, nb095_alpha_dummy_718] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_609 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_713 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_671 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_713] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_671 D R S_cls E))).fv) 0

theorem nb095_fresh_610 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_714 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_714] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_611 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_685 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_685] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) 0

theorem nb095_fresh_612 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_686 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_686] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) 1

theorem nb095_distinct_613 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_685 D R S_cls E) ≠ (nb095_alpha_dummy_686 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_685, nb095_alpha_dummy_686] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_614 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_687 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_687] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_615 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_688 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_688] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_616 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_688 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_687, nb095_alpha_dummy_688] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_617 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_691 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_691] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_692] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_619 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_693 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_693] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_691 D R S_cls E) ≠ (nb095_alpha_dummy_692 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_691, nb095_alpha_dummy_692] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_621 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_691 D R S_cls E) ≠ (nb095_alpha_dummy_693 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_691, nb095_alpha_dummy_693] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_622 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_693 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_692, nb095_alpha_dummy_693] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_623 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_694 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_694] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_624 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_695] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_625 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_696 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_696] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_626 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_694 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_695 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_694, nb095_alpha_dummy_695] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_627 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_694 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_696 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_694, nb095_alpha_dummy_696] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_628 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_696 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_695, nb095_alpha_dummy_696] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_629 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_703 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_703] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv)
      0

theorem nb095_fresh_630 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_699 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_699] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_692 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv)
      0

theorem nb095_fresh_631 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_705 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_705] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv)
      0

theorem nb095_fresh_632 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_704 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_704] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_633 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_700 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_700] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_634 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_706 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_706] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_635 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_721 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_721] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_636 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_722] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_637 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_723 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_723] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_638 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_721 D R S_cls E) ≠ (nb095_alpha_dummy_722 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_721, nb095_alpha_dummy_722] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_639 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_721 D R S_cls E) ≠ (nb095_alpha_dummy_723 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_721, nb095_alpha_dummy_723] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_640 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ≠ (nb095_alpha_dummy_723 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_722, nb095_alpha_dummy_723] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_641 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_724 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_724] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_642 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_725] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_643 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_726 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_726] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_644 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_724 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_725 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_724, nb095_alpha_dummy_725] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_645 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_724 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_726 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_724, nb095_alpha_dummy_726] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_646 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_726 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_725, nb095_alpha_dummy_726] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_647 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_733 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_733] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv)
      0

theorem nb095_fresh_648 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_729 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_729] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv)
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

theorem nb095_fresh_649 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_735 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_735] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv)
      0

theorem nb095_fresh_650 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_734 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_734] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_651 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_730 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_730] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_652 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_736 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_736] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_653 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_783 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_741 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_783] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_741 D R S_cls E))).fv) 0

theorem nb095_fresh_654 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_784 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_784] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_655 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_755 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_755] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) 0

theorem nb095_fresh_656 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_756 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_756] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) 1

theorem nb095_distinct_657 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_755 D R S_cls E) ≠ (nb095_alpha_dummy_756 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_755, nb095_alpha_dummy_756] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_658 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_757 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_757] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_659 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_758 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_758] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) 1

theorem nb095_distinct_660 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_758 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_757, nb095_alpha_dummy_758] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_fresh_661 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_761 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_761] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_662 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_762] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_663 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_763 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_763] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_664 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_761 D R S_cls E) ≠ (nb095_alpha_dummy_762 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_761, nb095_alpha_dummy_762] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_665 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_761 D R S_cls E) ≠ (nb095_alpha_dummy_763 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_761, nb095_alpha_dummy_763] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_666 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_763 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_762, nb095_alpha_dummy_763] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_667 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_764 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_764] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_668 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_765] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_669 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_766 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_766] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_670 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_764 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_765 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_764, nb095_alpha_dummy_765] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_671 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_764 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_766 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_764, nb095_alpha_dummy_766] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_672 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_766 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_765, nb095_alpha_dummy_766] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_673 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_773 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_773] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv)
      0

theorem nb095_fresh_674 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_769 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_769] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv)
      0

theorem nb095_fresh_675 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_775 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_775] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv)
      0

theorem nb095_fresh_676 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_774 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_774] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_677 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_770 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_770] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_678 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_776 x u D R S_cls f E) ∉
      (((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_776] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_679 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_799 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_799] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv)
      0

theorem nb095_fresh_680 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_800 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_800] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv)
      1

theorem nb095_distinct_681 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_799 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_799, nb095_alpha_dummy_800] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_682 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_801 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_801] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv)
      0

theorem nb095_fresh_683 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_802 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_802] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv)
      1

theorem nb095_distinct_684 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_801 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) := by
  simpa only [nb095_alpha_dummy_801, nb095_alpha_dummy_802] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_685 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_807 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_807] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) 0

theorem nb095_fresh_686 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_808 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_808] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) 1

theorem nb095_distinct_687 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_807 D R S_cls E) ≠ (nb095_alpha_dummy_808 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_807, nb095_alpha_dummy_808] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_688 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_809 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_809] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) 0

theorem nb095_fresh_689 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_810 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_810] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) 1

theorem nb095_distinct_690 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_809 u S_cls E) ≠ (nb095_alpha_dummy_810 u S_cls E) := by
  simpa only [nb095_alpha_dummy_809, nb095_alpha_dummy_810] using
    (freshVar_injective (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_fresh_691 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_813 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_813] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 0

theorem nb095_fresh_692 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_814] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 1

theorem nb095_fresh_693 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_815 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_815] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) 2

theorem nb095_distinct_694 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_813 D R S_cls E) ≠ (nb095_alpha_dummy_814 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_813, nb095_alpha_dummy_814] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_695 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_813 D R S_cls E) ≠ (nb095_alpha_dummy_815 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_813, nb095_alpha_dummy_815] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_696 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_815 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_814, nb095_alpha_dummy_815] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_697 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_816 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_816] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
      0

theorem nb095_fresh_698 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_817] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
      1

theorem nb095_fresh_699 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_818 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb095_alpha_dummy_818] using
    freshVar_not_mem (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
      2

theorem nb095_distinct_700 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_816 u S_cls E) ≠ (nb095_alpha_dummy_817 u S_cls E) := by
  simpa only [nb095_alpha_dummy_816, nb095_alpha_dummy_817] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_distinct_701 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_816 u S_cls E) ≠ (nb095_alpha_dummy_818 u S_cls E) := by
  simpa only [nb095_alpha_dummy_816, nb095_alpha_dummy_818] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb095_distinct_702 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_818 u S_cls E) := by
  simpa only [nb095_alpha_dummy_817, nb095_alpha_dummy_818] using
    (freshVar_injective
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb095_fresh_703 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_825 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_825] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv)
      0

theorem nb095_fresh_704 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_821 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_821] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv)
      0

theorem nb095_fresh_705 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_827 D R S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_827] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv)
      0

theorem nb095_fresh_706 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_826 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_826] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv)
      0

theorem nb095_fresh_707 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_822 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_822] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv)
      0

theorem nb095_fresh_708 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_828 u S_cls E) ∉
      (((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_828] using
    freshVar_not_mem
      (((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv)
      0

theorem nb095_fresh_709 (f : Var) : (nb095_alpha_dummy_093 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb095_alpha_dummy_093] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb095_fresh_710 (f : Var) : (nb095_alpha_dummy_094 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb095_alpha_dummy_094] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb095_distinct_711 (f : Var) :
    (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_094 f) := by
  simpa only [nb095_alpha_dummy_093, nb095_alpha_dummy_094] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_712 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_670 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_670] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_713 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_740 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_740] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) 0

theorem nb095_fresh_714 (f : Var) :
    (nb095_alpha_dummy_014 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb095_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb095_fresh_715 (f : Var) :
    (nb095_alpha_dummy_015 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb095_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb095_fresh_716 (f : Var) :
    (nb095_alpha_dummy_016 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb095_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb095_distinct_717 (f : Var) :
    (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_015 f) := by
  simpa only [nb095_alpha_dummy_014, nb095_alpha_dummy_015] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb095_distinct_718 (f : Var) :
    (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_016 f) := by
  simpa only [nb095_alpha_dummy_014, nb095_alpha_dummy_016] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb095_distinct_719 (f : Var) :
    (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_016 f) := by
  simpa only [nb095_alpha_dummy_015, nb095_alpha_dummy_016] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb095_fresh_720 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      0

theorem nb095_fresh_721 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      1

theorem nb095_distinct_722 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
      (nb095_alpha_dummy_006 x u D R S_cls f E) :=
  by
  simpa only [nb095_alpha_dummy_005, nb095_alpha_dummy_006] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_723 (f : Var) :
    (nb095_alpha_dummy_297 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb095_alpha_dummy_297] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb095_fresh_724 (f : Var) :
    (nb095_alpha_dummy_298 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb095_alpha_dummy_298] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb095_distinct_725 (f : Var) :
    (nb095_alpha_dummy_297 f) ≠ (nb095_alpha_dummy_298 f) := by
  simpa only [nb095_alpha_dummy_297, nb095_alpha_dummy_298] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_726 (u : Var) : (nb095_alpha_dummy_344 u) ∉ (((Class.cv u)).fv) := by
  simpa only [nb095_alpha_dummy_344] using freshVar_not_mem (((Class.cv u)).fv) 0

theorem nb095_fresh_727 (x : Var) : (nb095_alpha_dummy_254 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb095_alpha_dummy_254] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb095_fresh_728 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_031 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_031] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_027 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_027 D R S_cls E))).fv)
      0

theorem nb095_fresh_729 (f : Var) :
    (nb095_alpha_dummy_032 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_029 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_029 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_029 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_032] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_029 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_029 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_029 f))).fv)
      0

theorem nb095_fresh_730 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_067 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_067] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_063 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_063 D R S_cls E))).fv)
      0

theorem nb095_fresh_731 (f : Var) :
    (nb095_alpha_dummy_068 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_065 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_065 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_065 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_068] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_065 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_065 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_065 f))).fv)
      0

theorem nb095_fresh_732 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_109 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_109] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_105 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv)
      0

theorem nb095_fresh_733 (f : Var) :
    (nb095_alpha_dummy_110 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_107 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_107 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_107 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_110] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_107 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_107 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_107 f))).fv)
      0

theorem nb095_fresh_734 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_145 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_145] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_141 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv)
      0

theorem nb095_fresh_735 (f : Var) :
    (nb095_alpha_dummy_146 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_143 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_143 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_143 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_146] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_143 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_143 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_143 f))).fv)
      0

theorem nb095_fresh_736 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_181 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_181] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_177 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_177 D R S_cls E))).fv)
      0

theorem nb095_fresh_737 (f : Var) :
    (nb095_alpha_dummy_182 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_179 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_182] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_179 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_179 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_179 f))).fv)
      0

theorem nb095_fresh_738 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_221 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_221] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_217 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_217 D R S_cls E))).fv)
      0

theorem nb095_fresh_739 (f : Var) :
    (nb095_alpha_dummy_222 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_219 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_219 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_219 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_222] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_219 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_219 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_219 f))).fv)
      0

theorem nb095_fresh_740 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_267 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_267] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_263 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_263 D R S_cls E))).fv)
      0

theorem nb095_fresh_741 (x : Var) (R : Class) :
    (nb095_alpha_dummy_268 x R) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_265 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_265 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_265 x R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_268] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_265 x R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_265 x R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_265 x R))).fv)
      0

theorem nb095_fresh_742 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_311 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_311] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_307 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_307 D R S_cls E))).fv)
      0

theorem nb095_fresh_743 (f : Var) :
    (nb095_alpha_dummy_312 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_309 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_309 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_309 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_312] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_309 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_309 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_309 f))).fv)
      0

theorem nb095_fresh_744 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_357 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_357] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_353 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv)
      0

theorem nb095_fresh_745 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_358 u S_cls) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv) :=
  by
  simpa only [nb095_alpha_dummy_358] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_355 u S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv)
      0

theorem nb095_fresh_746 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_405 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_405] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_401 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_401 D R S_cls E))).fv)
      0

theorem nb095_fresh_747 (f : Var) :
    (nb095_alpha_dummy_406 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_403 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_403 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_403 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_406] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_403 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_403 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_403 f))).fv)
      0

theorem nb095_fresh_748 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_441 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_441] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_437 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_437 D R S_cls E))).fv)
      0

theorem nb095_fresh_749 (f : Var) :
    (nb095_alpha_dummy_442 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_439 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_439 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_439 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_442] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_439 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_439 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_439 f))).fv)
      0

theorem nb095_fresh_750 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_483 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_483] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_479 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv)
      0

theorem nb095_fresh_751 (f : Var) :
    (nb095_alpha_dummy_484 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_481 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_481 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_481 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_484] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_481 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_481 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_481 f))).fv)
      0

theorem nb095_fresh_752 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_519 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_519] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_515 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv)
      0

theorem nb095_fresh_753 (f : Var) :
    (nb095_alpha_dummy_520 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_517 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_517 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_517 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_520] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_517 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_517 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_517 f))).fv)
      0

theorem nb095_fresh_754 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_555 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_555] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_551 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_551 D R S_cls E))).fv)
      0

theorem nb095_fresh_755 (f : Var) :
    (nb095_alpha_dummy_556 f) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_553 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_553 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_553 f))).fv) :=
  by
  simpa only [nb095_alpha_dummy_556] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_553 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_553 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_553 f))).fv)
      0

theorem nb095_fresh_756 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_591 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_591] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_587 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_587 D R S_cls E))).fv)
      0

theorem nb095_fresh_757 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_592 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_592] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_758 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_637 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_637] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_633 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv)
      0

theorem nb095_fresh_759 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_638 x D R) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_635 x D R))).fv) :=
  by
  simpa only [nb095_alpha_dummy_638] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_635 x D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_635 x D R))).fv)
      0

theorem nb095_fresh_760 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_689 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_689] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_685 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv)
      0

theorem nb095_fresh_761 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_690 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_690] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_762 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_719 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_719] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv)
      0

theorem nb095_fresh_763 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_720 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_720] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_764 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_759 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_759] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv)
      0

theorem nb095_fresh_765 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_760 x u D R S_cls f E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_760] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_766 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_811 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_811] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv)
      0

theorem nb095_fresh_767 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_812 u S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv) :=
  by
  simpa only [nb095_alpha_dummy_812] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv)
      0

theorem nb095_fresh_768 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_465] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 0

theorem nb095_fresh_769 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_466 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_466] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv) 1

theorem nb095_distinct_770 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_465 D R S_cls E) ≠ (nb095_alpha_dummy_466 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_465, nb095_alpha_dummy_466] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_771 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_385] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      0

theorem nb095_fresh_772 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_386] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      1

theorem nb095_fresh_773 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_387 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv) :=
  by
  simpa only [nb095_alpha_dummy_387] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      2

theorem nb095_distinct_774 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_386 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_385, nb095_alpha_dummy_386] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_775 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_385 D R S_cls E) ≠ (nb095_alpha_dummy_387 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_385, nb095_alpha_dummy_387] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_776 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_387 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_386, nb095_alpha_dummy_387] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_777 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_205 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb095_alpha_dummy_205] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb095_fresh_778 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_206 D R S_cls E) ∉
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb095_alpha_dummy_206] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb095_distinct_779 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_206 D R S_cls E) := by
  simpa only [nb095_alpha_dummy_205, nb095_alpha_dummy_206] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cvv)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_780 (f : Var) :
    (nb095_alpha_dummy_467 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb095_alpha_dummy_467] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 0

theorem nb095_fresh_781 (f : Var) :
    (nb095_alpha_dummy_468 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb095_alpha_dummy_468] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 1

theorem nb095_distinct_782 (f : Var) :
    (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_468 f) := by
  simpa only [nb095_alpha_dummy_467, nb095_alpha_dummy_468] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_783 (f : Var) :
    (nb095_alpha_dummy_388 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_388] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0

theorem nb095_fresh_784 (f : Var) :
    (nb095_alpha_dummy_389 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_389] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1

theorem nb095_fresh_785 (f : Var) :
    (nb095_alpha_dummy_390 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb095_alpha_dummy_390] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2

theorem nb095_distinct_786 (f : Var) :
    (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_389 f) := by
  simpa only [nb095_alpha_dummy_388, nb095_alpha_dummy_389] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_787 (f : Var) :
    (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_390 f) := by
  simpa only [nb095_alpha_dummy_388, nb095_alpha_dummy_390] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_788 (f : Var) :
    (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_390 f) := by
  simpa only [nb095_alpha_dummy_389, nb095_alpha_dummy_390] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 1)
      (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
