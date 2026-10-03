/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part010`. -/


section

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

theorem nb090_distinct_392 (u : Var) :
    (nb090_alpha_dummy_308 u) ≠ (nb090_alpha_dummy_310 u) := by
  simpa only [nb090_alpha_dummy_308, nb090_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_393 (u : Var) :
    (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_310 u) := by
  simpa only [nb090_alpha_dummy_309, nb090_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_394 (A : Class) :
    (nb090_alpha_dummy_317 A) ∉
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_317] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv)
      0

theorem nb090_fresh_395 (A : Class) :
    (nb090_alpha_dummy_313 A) ∉
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_313] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv)
      0

theorem nb090_fresh_396 (A : Class) :
    (nb090_alpha_dummy_319 A) ∉
      (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_319] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv)
      0

theorem nb090_fresh_397 (u : Var) :
    (nb090_alpha_dummy_318 u) ∉
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_318] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv)
      0

theorem nb090_fresh_398 (u : Var) :
    (nb090_alpha_dummy_314 u) ∉
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_314] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv)
      0

theorem nb090_fresh_399 (u : Var) :
    (nb090_alpha_dummy_320 u) ∉
      (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_320] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv)
      0

theorem nb090_fresh_400 (A : Class) :
    (nb090_alpha_dummy_337 A) ∉
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_337] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv)
      0

theorem nb090_fresh_401 (A : Class) :
    (nb090_alpha_dummy_338 A) ∉
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_338] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv)
      1

theorem nb090_distinct_402 (A : Class) :
    (nb090_alpha_dummy_337 A) ≠ (nb090_alpha_dummy_338 A) := by
  simpa only [nb090_alpha_dummy_337, nb090_alpha_dummy_338] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_333 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_403 (h : Var) :
    (nb090_alpha_dummy_339 h) ∉
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_339] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
      0

theorem nb090_fresh_404 (h : Var) :
    (nb090_alpha_dummy_340 h) ∉
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_340] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
      1

theorem nb090_distinct_405 (h : Var) :
    (nb090_alpha_dummy_339 h) ≠ (nb090_alpha_dummy_340 h) := by
  simpa only [nb090_alpha_dummy_339, nb090_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_335 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_406 (A : Class) :
    (nb090_alpha_dummy_345 A) ∉ (((Class.cv (nb090_alpha_dummy_338 A))).fv) := by
  simpa only [nb090_alpha_dummy_345] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_338 A))).fv) 0

theorem nb090_fresh_407 (A : Class) :
    (nb090_alpha_dummy_346 A) ∉ (((Class.cv (nb090_alpha_dummy_338 A))).fv) := by
  simpa only [nb090_alpha_dummy_346] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_338 A))).fv) 1

theorem nb090_distinct_408 (A : Class) :
    (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_346 A) := by
  simpa only [nb090_alpha_dummy_345, nb090_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_409 (h : Var) :
    (nb090_alpha_dummy_347 h) ∉ (((Class.cv (nb090_alpha_dummy_340 h))).fv) := by
  simpa only [nb090_alpha_dummy_347] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_340 h))).fv) 0

theorem nb090_fresh_410 (h : Var) :
    (nb090_alpha_dummy_348 h) ∉ (((Class.cv (nb090_alpha_dummy_340 h))).fv) := by
  simpa only [nb090_alpha_dummy_348] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_340 h))).fv) 1

theorem nb090_distinct_411 (h : Var) :
    (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_348 h) := by
  simpa only [nb090_alpha_dummy_347, nb090_alpha_dummy_348] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_412 (A : Class) :
    (nb090_alpha_dummy_351 A) ∉
      (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_351] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_413 (A : Class) :
    (nb090_alpha_dummy_352 A) ∉
      (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_352] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_414 (A : Class) :
    (nb090_alpha_dummy_353 A) ∉
      (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_353] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_415 (A : Class) :
    (nb090_alpha_dummy_351 A) ≠ (nb090_alpha_dummy_352 A) := by
  simpa only [nb090_alpha_dummy_351, nb090_alpha_dummy_352] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_416 (A : Class) :
    (nb090_alpha_dummy_351 A) ≠ (nb090_alpha_dummy_353 A) := by
  simpa only [nb090_alpha_dummy_351, nb090_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_417 (A : Class) :
    (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_353 A) := by
  simpa only [nb090_alpha_dummy_352, nb090_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_418 (h : Var) :
    (nb090_alpha_dummy_354 h) ∉
      (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_354] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_419 (h : Var) :
    (nb090_alpha_dummy_355 h) ∉
      (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_355] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_420 (h : Var) :
    (nb090_alpha_dummy_356 h) ∉
      (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_356] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_421 (h : Var) :
    (nb090_alpha_dummy_354 h) ≠ (nb090_alpha_dummy_355 h) := by
  simpa only [nb090_alpha_dummy_354, nb090_alpha_dummy_355] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_422 (h : Var) :
    (nb090_alpha_dummy_354 h) ≠ (nb090_alpha_dummy_356 h) := by
  simpa only [nb090_alpha_dummy_354, nb090_alpha_dummy_356] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_423 (h : Var) :
    (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_356 h) := by
  simpa only [nb090_alpha_dummy_355, nb090_alpha_dummy_356] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_424 (A : Class) :
    (nb090_alpha_dummy_363 A) ∉
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_363] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv)
      0

theorem nb090_fresh_425 (A : Class) :
    (nb090_alpha_dummy_359 A) ∉
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_359] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv)
      0

theorem nb090_fresh_426 (A : Class) :
    (nb090_alpha_dummy_365 A) ∉
      (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_365] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv)
      0

theorem nb090_fresh_427 (h : Var) :
    (nb090_alpha_dummy_364 h) ∉
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_364] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv)
      0

theorem nb090_fresh_428 (h : Var) :
    (nb090_alpha_dummy_360 h) ∉
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_360] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv)
      0

theorem nb090_fresh_429 (h : Var) :
    (nb090_alpha_dummy_366 h) ∉
      (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_366] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv)
      0

theorem nb090_fresh_430 (A : Class) :
    (nb090_alpha_dummy_417 A) ∉ (((Class.cv (nb090_alpha_dummy_375 A))).fv) := by
  simpa only [nb090_alpha_dummy_417] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_375 A))).fv) 0

theorem nb090_fresh_431 (v : Var) :
    (nb090_alpha_dummy_418 v) ∉ (((Class.cv (nb090_alpha_dummy_376 v))).fv) := by
  simpa only [nb090_alpha_dummy_418] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_376 v))).fv) 0

theorem nb090_fresh_432 (A : Class) :
    (nb090_alpha_dummy_389 A) ∉ (((Class.cv (nb090_alpha_dummy_382 A))).fv) := by
  simpa only [nb090_alpha_dummy_389] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_382 A))).fv) 0

theorem nb090_fresh_433 (A : Class) :
    (nb090_alpha_dummy_390 A) ∉ (((Class.cv (nb090_alpha_dummy_382 A))).fv) := by
  simpa only [nb090_alpha_dummy_390] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_382 A))).fv) 1

theorem nb090_distinct_434 (A : Class) :
    (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_390 A) := by
  simpa only [nb090_alpha_dummy_389, nb090_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_382 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_435 (v : Var) :
    (nb090_alpha_dummy_391 v) ∉ (((Class.cv (nb090_alpha_dummy_384 v))).fv) := by
  simpa only [nb090_alpha_dummy_391] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_384 v))).fv) 0

theorem nb090_fresh_436 (v : Var) :
    (nb090_alpha_dummy_392 v) ∉ (((Class.cv (nb090_alpha_dummy_384 v))).fv) := by
  simpa only [nb090_alpha_dummy_392] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_384 v))).fv) 1

theorem nb090_distinct_437 (v : Var) :
    (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_392 v) := by
  simpa only [nb090_alpha_dummy_391, nb090_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_384 v))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_438 (A : Class) :
    (nb090_alpha_dummy_395 A) ∉
      (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_395] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_439 (A : Class) :
    (nb090_alpha_dummy_396 A) ∉
      (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_396] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_440 (A : Class) :
    (nb090_alpha_dummy_397 A) ∉
      (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_397] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_441 (A : Class) :
    (nb090_alpha_dummy_395 A) ≠ (nb090_alpha_dummy_396 A) := by
  simpa only [nb090_alpha_dummy_395, nb090_alpha_dummy_396] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_442 (A : Class) :
    (nb090_alpha_dummy_395 A) ≠ (nb090_alpha_dummy_397 A) := by
  simpa only [nb090_alpha_dummy_395, nb090_alpha_dummy_397] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_443 (A : Class) :
    (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_397 A) := by
  simpa only [nb090_alpha_dummy_396, nb090_alpha_dummy_397] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_444 (v : Var) :
    (nb090_alpha_dummy_398 v) ∉
      (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_398] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_445 (v : Var) :
    (nb090_alpha_dummy_399 v) ∉
      (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_399] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_446 (v : Var) :
    (nb090_alpha_dummy_400 v) ∉
      (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_400] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_447 (v : Var) :
    (nb090_alpha_dummy_398 v) ≠ (nb090_alpha_dummy_399 v) := by
  simpa only [nb090_alpha_dummy_398, nb090_alpha_dummy_399] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_448 (v : Var) :
    (nb090_alpha_dummy_398 v) ≠ (nb090_alpha_dummy_400 v) := by
  simpa only [nb090_alpha_dummy_398, nb090_alpha_dummy_400] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_449 (v : Var) :
    (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_400 v) := by
  simpa only [nb090_alpha_dummy_399, nb090_alpha_dummy_400] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_450 (A : Class) :
    (nb090_alpha_dummy_407 A) ∉
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_407] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv)
      0

theorem nb090_fresh_451 (A : Class) :
    (nb090_alpha_dummy_403 A) ∉
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_403] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv)
      0

theorem nb090_fresh_452 (A : Class) :
    (nb090_alpha_dummy_409 A) ∉
      (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_409] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv)
      0

theorem nb090_fresh_453 (v : Var) :
    (nb090_alpha_dummy_408 v) ∉
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_408] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv)
      0

theorem nb090_fresh_454 (v : Var) :
    (nb090_alpha_dummy_404 v) ∉
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_404] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv)
      0

theorem nb090_fresh_455 (v : Var) :
    (nb090_alpha_dummy_410 v) ∉
      (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_410] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv)
      0

theorem nb090_fresh_456 (A : Class) :
    (nb090_alpha_dummy_431 A) ∉
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_431] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
      0

theorem nb090_fresh_457 (A : Class) :
    (nb090_alpha_dummy_432 A) ∉
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_432] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
      1

theorem nb090_distinct_458 (A : Class) :
    (nb090_alpha_dummy_431 A) ≠ (nb090_alpha_dummy_432 A) := by
  simpa only [nb090_alpha_dummy_431, nb090_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_459 (A : Class) :
    (nb090_alpha_dummy_467 A) ∉
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_467] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv)
      0

theorem nb090_fresh_460 (A : Class) :
    (nb090_alpha_dummy_468 A) ∉
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_468] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv)
      1

theorem nb090_distinct_461 (A : Class) :
    (nb090_alpha_dummy_467 A) ≠ (nb090_alpha_dummy_468 A) := by
  simpa only [nb090_alpha_dummy_467, nb090_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_425 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_462 (A : Class) :
    (nb090_alpha_dummy_581 A) ∉
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_581] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
      0

theorem nb090_fresh_463 (A : Class) :
    (nb090_alpha_dummy_582 A) ∉
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_582] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
      1

theorem nb090_distinct_464 (A : Class) :
    (nb090_alpha_dummy_581 A) ≠ (nb090_alpha_dummy_582 A) := by
  simpa only [nb090_alpha_dummy_581, nb090_alpha_dummy_582] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_465 (h : Var) :
    (nb090_alpha_dummy_433 h) ∉
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_433] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv)
      0

theorem nb090_fresh_466 (h : Var) :
    (nb090_alpha_dummy_434 h) ∉
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_434] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv)
      1

theorem nb090_distinct_467 (h : Var) :
    (nb090_alpha_dummy_433 h) ≠ (nb090_alpha_dummy_434 h) := by
  simpa only [nb090_alpha_dummy_433, nb090_alpha_dummy_434] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_468 (h : Var) :
    (nb090_alpha_dummy_469 h) ∉
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_469] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv)
      0

theorem nb090_fresh_469 (h : Var) :
    (nb090_alpha_dummy_470 h) ∉
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_470] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv)
      1

theorem nb090_distinct_470 (h : Var) :
    (nb090_alpha_dummy_469 h) ≠ (nb090_alpha_dummy_470 h) := by
  simpa only [nb090_alpha_dummy_469, nb090_alpha_dummy_470] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_428 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_471 (h : Var) :
    (nb090_alpha_dummy_583 h) ∉
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_583] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv)
      0

theorem nb090_fresh_472 (h : Var) :
    (nb090_alpha_dummy_584 h) ∉
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_584] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv)
      1

theorem nb090_distinct_473 (h : Var) :
    (nb090_alpha_dummy_583 h) ≠ (nb090_alpha_dummy_584 h) := by
  simpa only [nb090_alpha_dummy_583, nb090_alpha_dummy_584] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_474 (A : Class) :
    (nb090_alpha_dummy_439 A) ∉ (((Class.cv (nb090_alpha_dummy_432 A))).fv) := by
  simpa only [nb090_alpha_dummy_439] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_432 A))).fv) 0

theorem nb090_fresh_475 (A : Class) :
    (nb090_alpha_dummy_440 A) ∉ (((Class.cv (nb090_alpha_dummy_432 A))).fv) := by
  simpa only [nb090_alpha_dummy_440] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_432 A))).fv) 1

theorem nb090_distinct_476 (A : Class) :
    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_440 A) := by
  simpa only [nb090_alpha_dummy_439, nb090_alpha_dummy_440] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_477 (h : Var) :
    (nb090_alpha_dummy_441 h) ∉ (((Class.cv (nb090_alpha_dummy_434 h))).fv) := by
  simpa only [nb090_alpha_dummy_441] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_434 h))).fv) 0

theorem nb090_fresh_478 (h : Var) :
    (nb090_alpha_dummy_442 h) ∉ (((Class.cv (nb090_alpha_dummy_434 h))).fv) := by
  simpa only [nb090_alpha_dummy_442] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_434 h))).fv) 1

theorem nb090_distinct_479 (h : Var) :
    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_442 h) := by
  simpa only [nb090_alpha_dummy_441, nb090_alpha_dummy_442] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_480 (A : Class) :
    (nb090_alpha_dummy_445 A) ∉
      (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_445] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_481 (A : Class) :
    (nb090_alpha_dummy_446 A) ∉
      (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_446] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_482 (A : Class) :
    (nb090_alpha_dummy_447 A) ∉
      (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_447] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_483 (A : Class) :
    (nb090_alpha_dummy_445 A) ≠ (nb090_alpha_dummy_446 A) := by
  simpa only [nb090_alpha_dummy_445, nb090_alpha_dummy_446] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_484 (A : Class) :
    (nb090_alpha_dummy_445 A) ≠ (nb090_alpha_dummy_447 A) := by
  simpa only [nb090_alpha_dummy_445, nb090_alpha_dummy_447] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_485 (A : Class) :
    (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_447 A) := by
  simpa only [nb090_alpha_dummy_446, nb090_alpha_dummy_447] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_486 (h : Var) :
    (nb090_alpha_dummy_448 h) ∉
      (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_448] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_487 (h : Var) :
    (nb090_alpha_dummy_449 h) ∉
      (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_449] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_488 (h : Var) :
    (nb090_alpha_dummy_450 h) ∉
      (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_450] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_489 (h : Var) :
    (nb090_alpha_dummy_448 h) ≠ (nb090_alpha_dummy_449 h) := by
  simpa only [nb090_alpha_dummy_448, nb090_alpha_dummy_449] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_490 (h : Var) :
    (nb090_alpha_dummy_448 h) ≠ (nb090_alpha_dummy_450 h) := by
  simpa only [nb090_alpha_dummy_448, nb090_alpha_dummy_450] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_491 (h : Var) :
    (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_450 h) := by
  simpa only [nb090_alpha_dummy_449, nb090_alpha_dummy_450] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_492 (A : Class) :
    (nb090_alpha_dummy_457 A) ∉
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_457] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv)
      0

theorem nb090_fresh_493 (A : Class) :
    (nb090_alpha_dummy_453 A) ∉
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_453] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv)
      0

theorem nb090_fresh_494 (A : Class) :
    (nb090_alpha_dummy_459 A) ∉
      (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_459] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv)
      0

theorem nb090_fresh_495 (h : Var) :
    (nb090_alpha_dummy_458 h) ∉
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_458] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv)
      0

theorem nb090_fresh_496 (h : Var) :
    (nb090_alpha_dummy_454 h) ∉
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_454] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv)
      0

theorem nb090_fresh_497 (h : Var) :
    (nb090_alpha_dummy_460 h) ∉
      (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_460] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv)
      0

theorem nb090_fresh_498 (A : Class) :
    (nb090_alpha_dummy_475 A) ∉ (((Class.cv (nb090_alpha_dummy_468 A))).fv) := by
  simpa only [nb090_alpha_dummy_475] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_468 A))).fv) 0

theorem nb090_fresh_499 (A : Class) :
    (nb090_alpha_dummy_476 A) ∉ (((Class.cv (nb090_alpha_dummy_468 A))).fv) := by
  simpa only [nb090_alpha_dummy_476] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_468 A))).fv) 1

theorem nb090_distinct_500 (A : Class) :
    (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_476 A) := by
  simpa only [nb090_alpha_dummy_475, nb090_alpha_dummy_476] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_468 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_501 (h : Var) :
    (nb090_alpha_dummy_477 h) ∉ (((Class.cv (nb090_alpha_dummy_470 h))).fv) := by
  simpa only [nb090_alpha_dummy_477] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_470 h))).fv) 0

theorem nb090_fresh_502 (h : Var) :
    (nb090_alpha_dummy_478 h) ∉ (((Class.cv (nb090_alpha_dummy_470 h))).fv) := by
  simpa only [nb090_alpha_dummy_478] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_470 h))).fv) 1

theorem nb090_distinct_503 (h : Var) :
    (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_478 h) := by
  simpa only [nb090_alpha_dummy_477, nb090_alpha_dummy_478] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_470 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_504 (A : Class) :
    (nb090_alpha_dummy_481 A) ∉
      (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_481] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_505 (A : Class) :
    (nb090_alpha_dummy_482 A) ∉
      (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_482] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_506 (A : Class) :
    (nb090_alpha_dummy_483 A) ∉
      (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_483] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_507 (A : Class) :
    (nb090_alpha_dummy_481 A) ≠ (nb090_alpha_dummy_482 A) := by
  simpa only [nb090_alpha_dummy_481, nb090_alpha_dummy_482] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_508 (A : Class) :
    (nb090_alpha_dummy_481 A) ≠ (nb090_alpha_dummy_483 A) := by
  simpa only [nb090_alpha_dummy_481, nb090_alpha_dummy_483] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_509 (A : Class) :
    (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_483 A) := by
  simpa only [nb090_alpha_dummy_482, nb090_alpha_dummy_483] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_510 (h : Var) :
    (nb090_alpha_dummy_484 h) ∉
      (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_484] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_511 (h : Var) :
    (nb090_alpha_dummy_485 h) ∉
      (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_485] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_512 (h : Var) :
    (nb090_alpha_dummy_486 h) ∉
      (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_486] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_513 (h : Var) :
    (nb090_alpha_dummy_484 h) ≠ (nb090_alpha_dummy_485 h) := by
  simpa only [nb090_alpha_dummy_484, nb090_alpha_dummy_485] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_514 (h : Var) :
    (nb090_alpha_dummy_484 h) ≠ (nb090_alpha_dummy_486 h) := by
  simpa only [nb090_alpha_dummy_484, nb090_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_515 (h : Var) :
    (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_486 h) := by
  simpa only [nb090_alpha_dummy_485, nb090_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_516 (A : Class) :
    (nb090_alpha_dummy_493 A) ∉
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_493] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv)
      0

theorem nb090_fresh_517 (A : Class) :
    (nb090_alpha_dummy_489 A) ∉
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_489] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv)
      0

theorem nb090_fresh_518 (A : Class) :
    (nb090_alpha_dummy_495 A) ∉
      (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_495] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv)
      0

theorem nb090_fresh_519 (h : Var) :
    (nb090_alpha_dummy_494 h) ∉
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_494] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv)
      0

theorem nb090_fresh_520 (h : Var) :
    (nb090_alpha_dummy_490 h) ∉
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_490] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv)
      0

theorem nb090_fresh_521 (h : Var) :
    (nb090_alpha_dummy_496 h) ∉
      (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_496] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv)
      0

theorem nb090_fresh_522 (A : Class) :
    (nb090_alpha_dummy_509 A) ∉
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_509] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv)
      0

theorem nb090_fresh_523 (A : Class) :
    (nb090_alpha_dummy_510 A) ∉
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_510] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv)
      1

theorem nb090_distinct_524 (A : Class) :
    (nb090_alpha_dummy_509 A) ≠ (nb090_alpha_dummy_510 A) := by
  simpa only [nb090_alpha_dummy_509, nb090_alpha_dummy_510] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_504 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_525 (A : Class) :
    (nb090_alpha_dummy_545 A) ∉
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_545] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv)
      0

theorem nb090_fresh_526 (A : Class) :
    (nb090_alpha_dummy_546 A) ∉
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_546] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv)
      1

theorem nb090_distinct_527 (A : Class) :
    (nb090_alpha_dummy_545 A) ≠ (nb090_alpha_dummy_546 A) := by
  simpa only [nb090_alpha_dummy_545, nb090_alpha_dummy_546] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_503 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_528 (h : Var) :
    (nb090_alpha_dummy_511 h) ∉
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_511] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv)
      0

theorem nb090_fresh_529 (h : Var) :
    (nb090_alpha_dummy_512 h) ∉
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_512] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv)
      1

theorem nb090_distinct_530 (h : Var) :
    (nb090_alpha_dummy_511 h) ≠ (nb090_alpha_dummy_512 h) := by
  simpa only [nb090_alpha_dummy_511, nb090_alpha_dummy_512] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_506 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_531 (h : Var) :
    (nb090_alpha_dummy_547 h) ∉
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_547] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv)
      0

theorem nb090_fresh_532 (h : Var) :
    (nb090_alpha_dummy_548 h) ∉
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_548] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv)
      1

theorem nb090_distinct_533 (h : Var) :
    (nb090_alpha_dummy_547 h) ≠ (nb090_alpha_dummy_548 h) := by
  simpa only [nb090_alpha_dummy_547, nb090_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_505 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_534 (A : Class) :
    (nb090_alpha_dummy_517 A) ∉ (((Class.cv (nb090_alpha_dummy_510 A))).fv) := by
  simpa only [nb090_alpha_dummy_517] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_510 A))).fv) 0

theorem nb090_fresh_535 (A : Class) :
    (nb090_alpha_dummy_518 A) ∉ (((Class.cv (nb090_alpha_dummy_510 A))).fv) := by
  simpa only [nb090_alpha_dummy_518] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_510 A))).fv) 1

theorem nb090_distinct_536 (A : Class) :
    (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_518 A) := by
  simpa only [nb090_alpha_dummy_517, nb090_alpha_dummy_518] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_537 (h : Var) :
    (nb090_alpha_dummy_519 h) ∉ (((Class.cv (nb090_alpha_dummy_512 h))).fv) := by
  simpa only [nb090_alpha_dummy_519] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_512 h))).fv) 0

theorem nb090_fresh_538 (h : Var) :
    (nb090_alpha_dummy_520 h) ∉ (((Class.cv (nb090_alpha_dummy_512 h))).fv) := by
  simpa only [nb090_alpha_dummy_520] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_512 h))).fv) 1

theorem nb090_distinct_539 (h : Var) :
    (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_520 h) := by
  simpa only [nb090_alpha_dummy_519, nb090_alpha_dummy_520] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_540 (A : Class) :
    (nb090_alpha_dummy_523 A) ∉
      (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_523] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_541 (A : Class) :
    (nb090_alpha_dummy_524 A) ∉
      (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_524] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part011`. -/


section

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

theorem nb090_fresh_542 (A : Class) :
    (nb090_alpha_dummy_525 A) ∉
      (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_525] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_543 (A : Class) :
    (nb090_alpha_dummy_523 A) ≠ (nb090_alpha_dummy_524 A) := by
  simpa only [nb090_alpha_dummy_523, nb090_alpha_dummy_524] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_544 (A : Class) :
    (nb090_alpha_dummy_523 A) ≠ (nb090_alpha_dummy_525 A) := by
  simpa only [nb090_alpha_dummy_523, nb090_alpha_dummy_525] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_545 (A : Class) :
    (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_525 A) := by
  simpa only [nb090_alpha_dummy_524, nb090_alpha_dummy_525] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_546 (h : Var) :
    (nb090_alpha_dummy_526 h) ∉
      (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_526] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_547 (h : Var) :
    (nb090_alpha_dummy_527 h) ∉
      (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_527] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_548 (h : Var) :
    (nb090_alpha_dummy_528 h) ∉
      (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_528] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_549 (h : Var) :
    (nb090_alpha_dummy_526 h) ≠ (nb090_alpha_dummy_527 h) := by
  simpa only [nb090_alpha_dummy_526, nb090_alpha_dummy_527] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_550 (h : Var) :
    (nb090_alpha_dummy_526 h) ≠ (nb090_alpha_dummy_528 h) := by
  simpa only [nb090_alpha_dummy_526, nb090_alpha_dummy_528] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_551 (h : Var) :
    (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_528 h) := by
  simpa only [nb090_alpha_dummy_527, nb090_alpha_dummy_528] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_552 (A : Class) :
    (nb090_alpha_dummy_535 A) ∉
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_535] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv)
      0

theorem nb090_fresh_553 (A : Class) :
    (nb090_alpha_dummy_531 A) ∉
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_531] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv)
      0

theorem nb090_fresh_554 (A : Class) :
    (nb090_alpha_dummy_537 A) ∉
      (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_537] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv)
      0

theorem nb090_fresh_555 (h : Var) :
    (nb090_alpha_dummy_536 h) ∉
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_536] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv)
      0

theorem nb090_fresh_556 (h : Var) :
    (nb090_alpha_dummy_532 h) ∉
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_532] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv)
      0

theorem nb090_fresh_557 (h : Var) :
    (nb090_alpha_dummy_538 h) ∉
      (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_538] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv)
      0

theorem nb090_fresh_558 (A : Class) :
    (nb090_alpha_dummy_553 A) ∉ (((Class.cv (nb090_alpha_dummy_546 A))).fv) := by
  simpa only [nb090_alpha_dummy_553] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_546 A))).fv) 0

theorem nb090_fresh_559 (A : Class) :
    (nb090_alpha_dummy_554 A) ∉ (((Class.cv (nb090_alpha_dummy_546 A))).fv) := by
  simpa only [nb090_alpha_dummy_554] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_546 A))).fv) 1

theorem nb090_distinct_560 (A : Class) :
    (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_554 A) := by
  simpa only [nb090_alpha_dummy_553, nb090_alpha_dummy_554] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_546 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_561 (h : Var) :
    (nb090_alpha_dummy_555 h) ∉ (((Class.cv (nb090_alpha_dummy_548 h))).fv) := by
  simpa only [nb090_alpha_dummy_555] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_548 h))).fv) 0

theorem nb090_fresh_562 (h : Var) :
    (nb090_alpha_dummy_556 h) ∉ (((Class.cv (nb090_alpha_dummy_548 h))).fv) := by
  simpa only [nb090_alpha_dummy_556] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_548 h))).fv) 1

theorem nb090_distinct_563 (h : Var) :
    (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_556 h) := by
  simpa only [nb090_alpha_dummy_555, nb090_alpha_dummy_556] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_548 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_564 (A : Class) :
    (nb090_alpha_dummy_559 A) ∉
      (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_559] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_565 (A : Class) :
    (nb090_alpha_dummy_560 A) ∉
      (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_560] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_566 (A : Class) :
    (nb090_alpha_dummy_561 A) ∉
      (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_561] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_567 (A : Class) :
    (nb090_alpha_dummy_559 A) ≠ (nb090_alpha_dummy_560 A) := by
  simpa only [nb090_alpha_dummy_559, nb090_alpha_dummy_560] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_568 (A : Class) :
    (nb090_alpha_dummy_559 A) ≠ (nb090_alpha_dummy_561 A) := by
  simpa only [nb090_alpha_dummy_559, nb090_alpha_dummy_561] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_569 (A : Class) :
    (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_561 A) := by
  simpa only [nb090_alpha_dummy_560, nb090_alpha_dummy_561] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_570 (h : Var) :
    (nb090_alpha_dummy_562 h) ∉
      (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_562] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_571 (h : Var) :
    (nb090_alpha_dummy_563 h) ∉
      (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_563] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_572 (h : Var) :
    (nb090_alpha_dummy_564 h) ∉
      (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_564] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_573 (h : Var) :
    (nb090_alpha_dummy_562 h) ≠ (nb090_alpha_dummy_563 h) := by
  simpa only [nb090_alpha_dummy_562, nb090_alpha_dummy_563] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_574 (h : Var) :
    (nb090_alpha_dummy_562 h) ≠ (nb090_alpha_dummy_564 h) := by
  simpa only [nb090_alpha_dummy_562, nb090_alpha_dummy_564] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_575 (h : Var) :
    (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_564 h) := by
  simpa only [nb090_alpha_dummy_563, nb090_alpha_dummy_564] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_576 (A : Class) :
    (nb090_alpha_dummy_571 A) ∉
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_571] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv)
      0

theorem nb090_fresh_577 (A : Class) :
    (nb090_alpha_dummy_567 A) ∉
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_567] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv)
      0

theorem nb090_fresh_578 (A : Class) :
    (nb090_alpha_dummy_573 A) ∉
      (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_573] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv)
      0

theorem nb090_fresh_579 (h : Var) :
    (nb090_alpha_dummy_572 h) ∉
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_572] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv)
      0

theorem nb090_fresh_580 (h : Var) :
    (nb090_alpha_dummy_568 h) ∉
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_568] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv)
      0

theorem nb090_fresh_581 (h : Var) :
    (nb090_alpha_dummy_574 h) ∉
      (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_574] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv)
      0

theorem nb090_fresh_582 (A : Class) :
    (nb090_alpha_dummy_589 A) ∉ (((Class.cv (nb090_alpha_dummy_582 A))).fv) := by
  simpa only [nb090_alpha_dummy_589] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_582 A))).fv) 0

theorem nb090_fresh_583 (A : Class) :
    (nb090_alpha_dummy_590 A) ∉ (((Class.cv (nb090_alpha_dummy_582 A))).fv) := by
  simpa only [nb090_alpha_dummy_590] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_582 A))).fv) 1

theorem nb090_distinct_584 (A : Class) :
    (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_590 A) := by
  simpa only [nb090_alpha_dummy_589, nb090_alpha_dummy_590] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_582 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_585 (h : Var) :
    (nb090_alpha_dummy_591 h) ∉ (((Class.cv (nb090_alpha_dummy_584 h))).fv) := by
  simpa only [nb090_alpha_dummy_591] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_584 h))).fv) 0

theorem nb090_fresh_586 (h : Var) :
    (nb090_alpha_dummy_592 h) ∉ (((Class.cv (nb090_alpha_dummy_584 h))).fv) := by
  simpa only [nb090_alpha_dummy_592] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_584 h))).fv) 1

theorem nb090_distinct_587 (h : Var) :
    (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_592 h) := by
  simpa only [nb090_alpha_dummy_591, nb090_alpha_dummy_592] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_584 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_588 (A : Class) :
    (nb090_alpha_dummy_595 A) ∉
      (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_595] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_589 (A : Class) :
    (nb090_alpha_dummy_596 A) ∉
      (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_596] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_590 (A : Class) :
    (nb090_alpha_dummy_597 A) ∉
      (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_597] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_591 (A : Class) :
    (nb090_alpha_dummy_595 A) ≠ (nb090_alpha_dummy_596 A) := by
  simpa only [nb090_alpha_dummy_595, nb090_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_592 (A : Class) :
    (nb090_alpha_dummy_595 A) ≠ (nb090_alpha_dummy_597 A) := by
  simpa only [nb090_alpha_dummy_595, nb090_alpha_dummy_597] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_593 (A : Class) :
    (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_597 A) := by
  simpa only [nb090_alpha_dummy_596, nb090_alpha_dummy_597] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_594 (h : Var) :
    (nb090_alpha_dummy_598 h) ∉
      (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_598] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_595 (h : Var) :
    (nb090_alpha_dummy_599 h) ∉
      (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_599] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_596 (h : Var) :
    (nb090_alpha_dummy_600 h) ∉
      (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_600] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_597 (h : Var) :
    (nb090_alpha_dummy_598 h) ≠ (nb090_alpha_dummy_599 h) := by
  simpa only [nb090_alpha_dummy_598, nb090_alpha_dummy_599] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_598 (h : Var) :
    (nb090_alpha_dummy_598 h) ≠ (nb090_alpha_dummy_600 h) := by
  simpa only [nb090_alpha_dummy_598, nb090_alpha_dummy_600] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_599 (h : Var) :
    (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_600 h) := by
  simpa only [nb090_alpha_dummy_599, nb090_alpha_dummy_600] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_600 (A : Class) :
    (nb090_alpha_dummy_607 A) ∉
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_607] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv)
      0

theorem nb090_fresh_601 (A : Class) :
    (nb090_alpha_dummy_603 A) ∉
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_603] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv)
      0

theorem nb090_fresh_602 (A : Class) :
    (nb090_alpha_dummy_609 A) ∉
      (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_609] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv)
      0

theorem nb090_fresh_603 (h : Var) :
    (nb090_alpha_dummy_608 h) ∉
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_608] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv)
      0

theorem nb090_fresh_604 (h : Var) :
    (nb090_alpha_dummy_604 h) ∉
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_604] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv)
      0

theorem nb090_fresh_605 (h : Var) :
    (nb090_alpha_dummy_610 h) ∉
      (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_610] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv)
      0

theorem nb090_fresh_606 (A : Class) :
    (nb090_alpha_dummy_625 A) ∉ (((Class.cv (nb090_alpha_dummy_618 A))).fv) := by
  simpa only [nb090_alpha_dummy_625] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_618 A))).fv) 0

theorem nb090_fresh_607 (A : Class) :
    (nb090_alpha_dummy_626 A) ∉ (((Class.cv (nb090_alpha_dummy_618 A))).fv) := by
  simpa only [nb090_alpha_dummy_626] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_618 A))).fv) 1

theorem nb090_distinct_608 (A : Class) :
    (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_626 A) := by
  simpa only [nb090_alpha_dummy_625, nb090_alpha_dummy_626] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_618 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_609 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_627 v u h) ∉ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_627] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 0

theorem nb090_fresh_610 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_628 v u h) ∉ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_628] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 1

theorem nb090_distinct_611 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_628 v u h) := by
  simpa only [nb090_alpha_dummy_627, nb090_alpha_dummy_628] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_612 (A : Class) :
    (nb090_alpha_dummy_631 A) ∉
      (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_631] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_613 (A : Class) :
    (nb090_alpha_dummy_632 A) ∉
      (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_632] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_614 (A : Class) :
    (nb090_alpha_dummy_633 A) ∉
      (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_633] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_615 (A : Class) :
    (nb090_alpha_dummy_631 A) ≠ (nb090_alpha_dummy_632 A) := by
  simpa only [nb090_alpha_dummy_631, nb090_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_616 (A : Class) :
    (nb090_alpha_dummy_631 A) ≠ (nb090_alpha_dummy_633 A) := by
  simpa only [nb090_alpha_dummy_631, nb090_alpha_dummy_633] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_617 (A : Class) :
    (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_633 A) := by
  simpa only [nb090_alpha_dummy_632, nb090_alpha_dummy_633] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_618 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_634 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_634] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_619 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_635] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_620 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_636 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_636] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_621 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_634 v u h) ≠ (nb090_alpha_dummy_635 v u h) := by
  simpa only [nb090_alpha_dummy_634, nb090_alpha_dummy_635] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_622 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_634 v u h) ≠ (nb090_alpha_dummy_636 v u h) := by
  simpa only [nb090_alpha_dummy_634, nb090_alpha_dummy_636] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_623 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_636 v u h) := by
  simpa only [nb090_alpha_dummy_635, nb090_alpha_dummy_636] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_624 (A : Class) :
    (nb090_alpha_dummy_643 A) ∉
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_643] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv)
      0

theorem nb090_fresh_625 (A : Class) :
    (nb090_alpha_dummy_639 A) ∉
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_639] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv)
      0

theorem nb090_fresh_626 (A : Class) :
    (nb090_alpha_dummy_645 A) ∉
      (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_645] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv)
      0

theorem nb090_fresh_627 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_644 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_644] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_635 v u h))).fv)
      0

theorem nb090_fresh_628 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_640 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_640] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv)
      0

theorem nb090_fresh_629 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_646 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_646] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv)
      0

theorem nb090_fresh_630 (A : Class) :
    (nb090_alpha_dummy_697 A) ∉ (((Class.cv (nb090_alpha_dummy_655 A))).fv) := by
  simpa only [nb090_alpha_dummy_697] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_655 A))).fv) 0

theorem nb090_fresh_631 (u : Var) :
    (nb090_alpha_dummy_698 u) ∉ (((Class.cv (nb090_alpha_dummy_656 u))).fv) := by
  simpa only [nb090_alpha_dummy_698] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_656 u))).fv) 0

theorem nb090_fresh_632 (A : Class) :
    (nb090_alpha_dummy_669 A) ∉ (((Class.cv (nb090_alpha_dummy_662 A))).fv) := by
  simpa only [nb090_alpha_dummy_669] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_662 A))).fv) 0

theorem nb090_fresh_633 (A : Class) :
    (nb090_alpha_dummy_670 A) ∉ (((Class.cv (nb090_alpha_dummy_662 A))).fv) := by
  simpa only [nb090_alpha_dummy_670] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_662 A))).fv) 1

theorem nb090_distinct_634 (A : Class) :
    (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_670 A) := by
  simpa only [nb090_alpha_dummy_669, nb090_alpha_dummy_670] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_635 (u : Var) :
    (nb090_alpha_dummy_671 u) ∉ (((Class.cv (nb090_alpha_dummy_664 u))).fv) := by
  simpa only [nb090_alpha_dummy_671] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_664 u))).fv) 0

theorem nb090_fresh_636 (u : Var) :
    (nb090_alpha_dummy_672 u) ∉ (((Class.cv (nb090_alpha_dummy_664 u))).fv) := by
  simpa only [nb090_alpha_dummy_672] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_664 u))).fv) 1

theorem nb090_distinct_637 (u : Var) :
    (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_672 u) := by
  simpa only [nb090_alpha_dummy_671, nb090_alpha_dummy_672] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_638 (A : Class) :
    (nb090_alpha_dummy_675 A) ∉
      (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_675] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_639 (A : Class) :
    (nb090_alpha_dummy_676 A) ∉
      (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_676] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_640 (A : Class) :
    (nb090_alpha_dummy_677 A) ∉
      (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_677] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_641 (A : Class) :
    (nb090_alpha_dummy_675 A) ≠ (nb090_alpha_dummy_676 A) := by
  simpa only [nb090_alpha_dummy_675, nb090_alpha_dummy_676] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_642 (A : Class) :
    (nb090_alpha_dummy_675 A) ≠ (nb090_alpha_dummy_677 A) := by
  simpa only [nb090_alpha_dummy_675, nb090_alpha_dummy_677] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_643 (A : Class) :
    (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_677 A) := by
  simpa only [nb090_alpha_dummy_676, nb090_alpha_dummy_677] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_644 (u : Var) :
    (nb090_alpha_dummy_678 u) ∉
      (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_678] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_645 (u : Var) :
    (nb090_alpha_dummy_679 u) ∉
      (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_679] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_646 (u : Var) :
    (nb090_alpha_dummy_680 u) ∉
      (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_680] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_647 (u : Var) :
    (nb090_alpha_dummy_678 u) ≠ (nb090_alpha_dummy_679 u) := by
  simpa only [nb090_alpha_dummy_678, nb090_alpha_dummy_679] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_648 (u : Var) :
    (nb090_alpha_dummy_678 u) ≠ (nb090_alpha_dummy_680 u) := by
  simpa only [nb090_alpha_dummy_678, nb090_alpha_dummy_680] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_649 (u : Var) :
    (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_680 u) := by
  simpa only [nb090_alpha_dummy_679, nb090_alpha_dummy_680] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_650 (A : Class) :
    (nb090_alpha_dummy_687 A) ∉
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_687] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv)
      0

theorem nb090_fresh_651 (A : Class) :
    (nb090_alpha_dummy_683 A) ∉
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_683] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv)
      0

theorem nb090_fresh_652 (A : Class) :
    (nb090_alpha_dummy_689 A) ∉
      (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_689] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv)
      0

theorem nb090_fresh_653 (u : Var) :
    (nb090_alpha_dummy_688 u) ∉
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_688] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv)
      0

theorem nb090_fresh_654 (u : Var) :
    (nb090_alpha_dummy_684 u) ∉
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_684] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv)
      0

theorem nb090_fresh_655 (u : Var) :
    (nb090_alpha_dummy_690 u) ∉
      (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_690] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv)
      0

theorem nb090_fresh_656 (A : Class) :
    (nb090_alpha_dummy_753 A) ∉ (((Class.cv (nb090_alpha_dummy_700 A))).fv) := by
  simpa only [nb090_alpha_dummy_753] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_700 A))).fv) 0

theorem nb090_fresh_657 (A : Class) :
    (nb090_alpha_dummy_754 A) ∉ (((Class.cv (nb090_alpha_dummy_700 A))).fv) := by
  simpa only [nb090_alpha_dummy_754] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_700 A))).fv) 1

theorem nb090_distinct_658 (A : Class) :
    (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_754 A) := by
  simpa only [nb090_alpha_dummy_753, nb090_alpha_dummy_754] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_700 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_659 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_755 v u h) ∉ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_755] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 0

theorem nb090_fresh_660 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_756 v u h) ∉ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_756] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 1

theorem nb090_distinct_661 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_756 v u h) := by
  simpa only [nb090_alpha_dummy_755, nb090_alpha_dummy_756] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_662 (A : Class) :
    (nb090_alpha_dummy_751 A) ∉ (((Class.cv (nb090_alpha_dummy_709 A))).fv) := by
  simpa only [nb090_alpha_dummy_751] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_709 A))).fv) 0

theorem nb090_fresh_663 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_752 v u h) ∉ (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_752] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) 0

theorem nb090_fresh_664 (A : Class) :
    (nb090_alpha_dummy_723 A) ∉ (((Class.cv (nb090_alpha_dummy_716 A))).fv) := by
  simpa only [nb090_alpha_dummy_723] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_716 A))).fv) 0

theorem nb090_fresh_665 (A : Class) :
    (nb090_alpha_dummy_724 A) ∉ (((Class.cv (nb090_alpha_dummy_716 A))).fv) := by
  simpa only [nb090_alpha_dummy_724] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_716 A))).fv) 1

theorem nb090_distinct_666 (A : Class) :
    (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_724 A) := by
  simpa only [nb090_alpha_dummy_723, nb090_alpha_dummy_724] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_716 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_667 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_725 v u h) ∉ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_725] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 0

theorem nb090_fresh_668 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_726 v u h) ∉ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_726] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 1

theorem nb090_distinct_669 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_726 v u h) := by
  simpa only [nb090_alpha_dummy_725, nb090_alpha_dummy_726] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_670 (A : Class) :
    (nb090_alpha_dummy_729 A) ∉
      (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_729] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_671 (A : Class) :
    (nb090_alpha_dummy_730 A) ∉
      (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_730] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_672 (A : Class) :
    (nb090_alpha_dummy_731 A) ∉
      (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_731] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_673 (A : Class) :
    (nb090_alpha_dummy_729 A) ≠ (nb090_alpha_dummy_730 A) := by
  simpa only [nb090_alpha_dummy_729, nb090_alpha_dummy_730] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_674 (A : Class) :
    (nb090_alpha_dummy_729 A) ≠ (nb090_alpha_dummy_731 A) := by
  simpa only [nb090_alpha_dummy_729, nb090_alpha_dummy_731] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_675 (A : Class) :
    (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_731 A) := by
  simpa only [nb090_alpha_dummy_730, nb090_alpha_dummy_731] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_676 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_732 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_732] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_677 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_733] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_678 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_734 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_734] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_679 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_732 v u h) ≠ (nb090_alpha_dummy_733 v u h) := by
  simpa only [nb090_alpha_dummy_732, nb090_alpha_dummy_733] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_680 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_732 v u h) ≠ (nb090_alpha_dummy_734 v u h) := by
  simpa only [nb090_alpha_dummy_732, nb090_alpha_dummy_734] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_681 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_734 v u h) := by
  simpa only [nb090_alpha_dummy_733, nb090_alpha_dummy_734] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_682 (A : Class) :
    (nb090_alpha_dummy_741 A) ∉
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_741] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv)
      0

theorem nb090_fresh_683 (A : Class) :
    (nb090_alpha_dummy_737 A) ∉
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_737] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv)
      0

theorem nb090_fresh_684 (A : Class) :
    (nb090_alpha_dummy_743 A) ∉
      (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_743] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv)
      0

theorem nb090_fresh_685 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_742 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_742] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_733 v u h))).fv)
      0

theorem nb090_fresh_686 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_738 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_738] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv)
      0

theorem nb090_fresh_687 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_744 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_744] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv)
      0

theorem nb090_fresh_688 (A : Class) :
    (nb090_alpha_dummy_759 A) ∉
      (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_759] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_689 (A : Class) :
    (nb090_alpha_dummy_760 A) ∉
      (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_760] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_690 (A : Class) :
    (nb090_alpha_dummy_761 A) ∉
      (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_761] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_691 (A : Class) :
    (nb090_alpha_dummy_759 A) ≠ (nb090_alpha_dummy_760 A) := by
  simpa only [nb090_alpha_dummy_759, nb090_alpha_dummy_760] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part012`. -/


section

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

theorem nb090_distinct_692 (A : Class) :
    (nb090_alpha_dummy_759 A) ≠ (nb090_alpha_dummy_761 A) := by
  simpa only [nb090_alpha_dummy_759, nb090_alpha_dummy_761] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_693 (A : Class) :
    (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_761 A) := by
  simpa only [nb090_alpha_dummy_760, nb090_alpha_dummy_761] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_694 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_762 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_762] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_695 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_763] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_696 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_764 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_764] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_697 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_762 v u h) ≠ (nb090_alpha_dummy_763 v u h) := by
  simpa only [nb090_alpha_dummy_762, nb090_alpha_dummy_763] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_698 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_762 v u h) ≠ (nb090_alpha_dummy_764 v u h) := by
  simpa only [nb090_alpha_dummy_762, nb090_alpha_dummy_764] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_699 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_764 v u h) := by
  simpa only [nb090_alpha_dummy_763, nb090_alpha_dummy_764] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_700 (A : Class) :
    (nb090_alpha_dummy_771 A) ∉
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_771] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv)
      0

theorem nb090_fresh_701 (A : Class) :
    (nb090_alpha_dummy_767 A) ∉
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_767] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv)
      0

theorem nb090_fresh_702 (A : Class) :
    (nb090_alpha_dummy_773 A) ∉
      (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_773] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv)
      0

theorem nb090_fresh_703 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_772 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_772] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_763 v u h))).fv)
      0

theorem nb090_fresh_704 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_768 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_768] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv)
      0

theorem nb090_fresh_705 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_774 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_774] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv)
      0

theorem nb090_fresh_706 (A : Class) :
    (nb090_alpha_dummy_821 A) ∉ (((Class.cv (nb090_alpha_dummy_779 A))).fv) := by
  simpa only [nb090_alpha_dummy_821] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_779 A))).fv) 0

theorem nb090_fresh_707 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_822 v u h) ∉ (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_822] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) 0

theorem nb090_fresh_708 (A : Class) :
    (nb090_alpha_dummy_793 A) ∉ (((Class.cv (nb090_alpha_dummy_786 A))).fv) := by
  simpa only [nb090_alpha_dummy_793] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_786 A))).fv) 0

theorem nb090_fresh_709 (A : Class) :
    (nb090_alpha_dummy_794 A) ∉ (((Class.cv (nb090_alpha_dummy_786 A))).fv) := by
  simpa only [nb090_alpha_dummy_794] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_786 A))).fv) 1

theorem nb090_distinct_710 (A : Class) :
    (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_794 A) := by
  simpa only [nb090_alpha_dummy_793, nb090_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_786 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_711 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_795 v u h) ∉ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_795] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 0

theorem nb090_fresh_712 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_796 v u h) ∉ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_796] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 1

theorem nb090_distinct_713 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_796 v u h) := by
  simpa only [nb090_alpha_dummy_795, nb090_alpha_dummy_796] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_714 (A : Class) :
    (nb090_alpha_dummy_799 A) ∉
      (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_799] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_715 (A : Class) :
    (nb090_alpha_dummy_800 A) ∉
      (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_800] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_716 (A : Class) :
    (nb090_alpha_dummy_801 A) ∉
      (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_801] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_717 (A : Class) :
    (nb090_alpha_dummy_799 A) ≠ (nb090_alpha_dummy_800 A) := by
  simpa only [nb090_alpha_dummy_799, nb090_alpha_dummy_800] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_718 (A : Class) :
    (nb090_alpha_dummy_799 A) ≠ (nb090_alpha_dummy_801 A) := by
  simpa only [nb090_alpha_dummy_799, nb090_alpha_dummy_801] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_719 (A : Class) :
    (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_801 A) := by
  simpa only [nb090_alpha_dummy_800, nb090_alpha_dummy_801] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_720 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_802 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_802] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_721 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_803] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_722 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_804 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_804] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_723 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_802 v u h) ≠ (nb090_alpha_dummy_803 v u h) := by
  simpa only [nb090_alpha_dummy_802, nb090_alpha_dummy_803] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_724 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_802 v u h) ≠ (nb090_alpha_dummy_804 v u h) := by
  simpa only [nb090_alpha_dummy_802, nb090_alpha_dummy_804] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_725 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_804 v u h) := by
  simpa only [nb090_alpha_dummy_803, nb090_alpha_dummy_804] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_726 (A : Class) :
    (nb090_alpha_dummy_811 A) ∉
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_811] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv)
      0

theorem nb090_fresh_727 (A : Class) :
    (nb090_alpha_dummy_807 A) ∉
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_807] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv)
      0

theorem nb090_fresh_728 (A : Class) :
    (nb090_alpha_dummy_813 A) ∉
      (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_813] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv)
      0

theorem nb090_fresh_729 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_812 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_812] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_803 v u h))).fv)
      0

theorem nb090_fresh_730 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_808 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_808] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv)
      0

theorem nb090_fresh_731 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_814 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_814] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv)
      0

theorem nb090_fresh_732 (A : Class) :
    (nb090_alpha_dummy_871 A) ∉ (((Class.cv (nb090_alpha_dummy_829 A))).fv) := by
  simpa only [nb090_alpha_dummy_871] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_829 A))).fv) 0

theorem nb090_fresh_733 (v : Var) :
    (nb090_alpha_dummy_872 v) ∉ (((Class.cv (nb090_alpha_dummy_830 v))).fv) := by
  simpa only [nb090_alpha_dummy_872] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_830 v))).fv) 0

theorem nb090_fresh_734 (A : Class) :
    (nb090_alpha_dummy_843 A) ∉ (((Class.cv (nb090_alpha_dummy_836 A))).fv) := by
  simpa only [nb090_alpha_dummy_843] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_836 A))).fv) 0

theorem nb090_fresh_735 (A : Class) :
    (nb090_alpha_dummy_844 A) ∉ (((Class.cv (nb090_alpha_dummy_836 A))).fv) := by
  simpa only [nb090_alpha_dummy_844] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_836 A))).fv) 1

theorem nb090_distinct_736 (A : Class) :
    (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_844 A) := by
  simpa only [nb090_alpha_dummy_843, nb090_alpha_dummy_844] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_836 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_737 (v : Var) :
    (nb090_alpha_dummy_845 v) ∉ (((Class.cv (nb090_alpha_dummy_838 v))).fv) := by
  simpa only [nb090_alpha_dummy_845] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_838 v))).fv) 0

theorem nb090_fresh_738 (v : Var) :
    (nb090_alpha_dummy_846 v) ∉ (((Class.cv (nb090_alpha_dummy_838 v))).fv) := by
  simpa only [nb090_alpha_dummy_846] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_838 v))).fv) 1

theorem nb090_distinct_739 (v : Var) :
    (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_846 v) := by
  simpa only [nb090_alpha_dummy_845, nb090_alpha_dummy_846] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_838 v))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_740 (A : Class) :
    (nb090_alpha_dummy_849 A) ∉
      (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_849] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_741 (A : Class) :
    (nb090_alpha_dummy_850 A) ∉
      (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_850] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_742 (A : Class) :
    (nb090_alpha_dummy_851 A) ∉
      (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_851] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_743 (A : Class) :
    (nb090_alpha_dummy_849 A) ≠ (nb090_alpha_dummy_850 A) := by
  simpa only [nb090_alpha_dummy_849, nb090_alpha_dummy_850] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_744 (A : Class) :
    (nb090_alpha_dummy_849 A) ≠ (nb090_alpha_dummy_851 A) := by
  simpa only [nb090_alpha_dummy_849, nb090_alpha_dummy_851] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_745 (A : Class) :
    (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_851 A) := by
  simpa only [nb090_alpha_dummy_850, nb090_alpha_dummy_851] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_746 (v : Var) :
    (nb090_alpha_dummy_852 v) ∉
      (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_852] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_747 (v : Var) :
    (nb090_alpha_dummy_853 v) ∉
      (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_853] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_748 (v : Var) :
    (nb090_alpha_dummy_854 v) ∉
      (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_854] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_749 (v : Var) :
    (nb090_alpha_dummy_852 v) ≠ (nb090_alpha_dummy_853 v) := by
  simpa only [nb090_alpha_dummy_852, nb090_alpha_dummy_853] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_750 (v : Var) :
    (nb090_alpha_dummy_852 v) ≠ (nb090_alpha_dummy_854 v) := by
  simpa only [nb090_alpha_dummy_852, nb090_alpha_dummy_854] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_751 (v : Var) :
    (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_854 v) := by
  simpa only [nb090_alpha_dummy_853, nb090_alpha_dummy_854] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_752 (A : Class) :
    (nb090_alpha_dummy_861 A) ∉
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_861] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv)
      0

theorem nb090_fresh_753 (A : Class) :
    (nb090_alpha_dummy_857 A) ∉
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_857] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv)
      0

theorem nb090_fresh_754 (A : Class) :
    (nb090_alpha_dummy_863 A) ∉
      (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_863] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv)
      0

theorem nb090_fresh_755 (v : Var) :
    (nb090_alpha_dummy_862 v) ∉
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_862] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv)
      0

theorem nb090_fresh_756 (v : Var) :
    (nb090_alpha_dummy_858 v) ∉
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_858] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv)
      0

theorem nb090_fresh_757 (v : Var) :
    (nb090_alpha_dummy_864 v) ∉
      (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_864] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv)
      0

theorem nb090_fresh_758 (h : Var) : (nb090_alpha_dummy_131 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090_alpha_dummy_131] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb090_fresh_759 (h : Var) : (nb090_alpha_dummy_132 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090_alpha_dummy_132] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb090_distinct_760 (h : Var) :
    (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_132 h) := by
  simpa only [nb090_alpha_dummy_131, nb090_alpha_dummy_132] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_761 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_708 v u h) ∉
      (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_708] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) 0

theorem nb090_fresh_762 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_778 v u h) ∉
      (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_778] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0

theorem nb090_fresh_763 (h : Var) :
    (nb090_alpha_dummy_052 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0

theorem nb090_fresh_764 (h : Var) :
    (nb090_alpha_dummy_053 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1

theorem nb090_fresh_765 (h : Var) :
    (nb090_alpha_dummy_054 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2

theorem nb090_distinct_766 (h : Var) :
    (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_053 h) := by
  simpa only [nb090_alpha_dummy_052, nb090_alpha_dummy_053] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb090_distinct_767 (h : Var) :
    (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_054 h) := by
  simpa only [nb090_alpha_dummy_052, nb090_alpha_dummy_054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb090_distinct_768 (h : Var) :
    (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_054 h) := by
  simpa only [nb090_alpha_dummy_053, nb090_alpha_dummy_054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb090_fresh_769 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∉
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv)
      0

theorem nb090_fresh_770 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∉
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv)
      1

theorem nb090_distinct_771 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_044 v u h) := by
  simpa only [nb090_alpha_dummy_043, nb090_alpha_dummy_044] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_772 (h : Var) :
    (nb090_alpha_dummy_335 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_335] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_773 (h : Var) :
    (nb090_alpha_dummy_336 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_336] using
    freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_774 (h : Var) :
    (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_336 h) := by
  simpa only [nb090_alpha_dummy_335, nb090_alpha_dummy_336] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_775 (u : Var) :
    (nb090_alpha_dummy_293 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_293] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 0

theorem nb090_fresh_776 (u : Var) :
    (nb090_alpha_dummy_294 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_294] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 1

theorem nb090_distinct_777 (u : Var) :
    (nb090_alpha_dummy_293 u) ≠ (nb090_alpha_dummy_294 u) := by
  simpa only [nb090_alpha_dummy_293, nb090_alpha_dummy_294] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_778 (u : Var) :
    (nb090_alpha_dummy_663 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_663] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 0

theorem nb090_fresh_779 (u : Var) :
    (nb090_alpha_dummy_664 u) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_664] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 1

theorem nb090_distinct_780 (u : Var) :
    (nb090_alpha_dummy_663 u) ≠ (nb090_alpha_dummy_664 u) := by
  simpa only [nb090_alpha_dummy_663, nb090_alpha_dummy_664] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_781 (v : Var) (u : Var) :
    (nb090_alpha_dummy_007 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_782 (v : Var) (u : Var) :
    (nb090_alpha_dummy_008 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1

theorem nb090_distinct_783 (v : Var) (u : Var) :
    (nb090_alpha_dummy_007 v u) ≠ (nb090_alpha_dummy_008 v u) := by
  simpa only [nb090_alpha_dummy_007, nb090_alpha_dummy_008] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_784 (v : Var) :
    (nb090_alpha_dummy_383 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_383] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 0

theorem nb090_fresh_785 (v : Var) :
    (nb090_alpha_dummy_384 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_384] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 1

theorem nb090_distinct_786 (v : Var) :
    (nb090_alpha_dummy_383 v) ≠ (nb090_alpha_dummy_384 v) := by
  simpa only [nb090_alpha_dummy_383, nb090_alpha_dummy_384] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_787 (v : Var) :
    (nb090_alpha_dummy_837 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_837] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 0

theorem nb090_fresh_788 (v : Var) :
    (nb090_alpha_dummy_838 v) ∉
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_838] using
    freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 1

theorem nb090_distinct_789 (v : Var) :
    (nb090_alpha_dummy_837 v) ≠ (nb090_alpha_dummy_838 v) := by
  simpa only [nb090_alpha_dummy_837, nb090_alpha_dummy_838] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_790 (A : Class) :
    (nb090_alpha_dummy_017 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_013 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_013 A))).fv)
      0

theorem nb090_fresh_791 (v : Var) (u : Var) :
    (nb090_alpha_dummy_018 v u) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_015 v u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_015 v u))).fv)
      0

theorem nb090_fresh_792 (A : Class) :
    (nb090_alpha_dummy_069 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_065 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_069] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_065 A))).fv)
      0

theorem nb090_fresh_793 (h : Var) :
    (nb090_alpha_dummy_070 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_067 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_070] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_067 h))).fv)
      0

theorem nb090_fresh_794 (A : Class) :
    (nb090_alpha_dummy_105 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_101 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_105] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_101 A))).fv)
      0

theorem nb090_fresh_795 (h : Var) :
    (nb090_alpha_dummy_106 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_103 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_106] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_103 h))).fv)
      0

theorem nb090_fresh_796 (A : Class) :
    (nb090_alpha_dummy_147 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_143 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_147] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_143 A))).fv)
      0

theorem nb090_fresh_797 (h : Var) :
    (nb090_alpha_dummy_148 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_145 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_148] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_145 h))).fv)
      0

theorem nb090_fresh_798 (A : Class) :
    (nb090_alpha_dummy_183 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_179 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_183] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_179 A))).fv)
      0

theorem nb090_fresh_799 (h : Var) :
    (nb090_alpha_dummy_184 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_181 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_184] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_181 h))).fv)
      0

theorem nb090_fresh_800 (A : Class) :
    (nb090_alpha_dummy_219 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_215 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_219] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_215 A))).fv)
      0

theorem nb090_fresh_801 (h : Var) :
    (nb090_alpha_dummy_220 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_217 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_220] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_217 h))).fv)
      0

theorem nb090_fresh_802 (A : Class) :
    (nb090_alpha_dummy_259 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_255 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_259] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_255 A))).fv)
      0

theorem nb090_fresh_803 (h : Var) :
    (nb090_alpha_dummy_260 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_257 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_260] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_257 h))).fv)
      0

theorem nb090_fresh_804 (A : Class) :
    (nb090_alpha_dummy_303 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_299 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_303] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_299 A))).fv)
      0

theorem nb090_fresh_805 (u : Var) :
    (nb090_alpha_dummy_304 u) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_301 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_304] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_301 u))).fv)
      0

theorem nb090_fresh_806 (A : Class) :
    (nb090_alpha_dummy_349 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_345 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_349] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_345 A))).fv)
      0

theorem nb090_fresh_807 (h : Var) :
    (nb090_alpha_dummy_350 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_347 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_350] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_347 h))).fv)
      0

theorem nb090_fresh_808 (A : Class) :
    (nb090_alpha_dummy_393 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_389 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_393] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_389 A))).fv)
      0

theorem nb090_fresh_809 (v : Var) :
    (nb090_alpha_dummy_394 v) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_391 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_394] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_391 v))).fv)
      0

theorem nb090_fresh_810 (A : Class) :
    (nb090_alpha_dummy_443 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_439 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_443] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_439 A))).fv)
      0

theorem nb090_fresh_811 (h : Var) :
    (nb090_alpha_dummy_444 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_441 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_444] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_441 h))).fv)
      0

theorem nb090_fresh_812 (A : Class) :
    (nb090_alpha_dummy_479 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_475 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_479] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_475 A))).fv)
      0

theorem nb090_fresh_813 (h : Var) :
    (nb090_alpha_dummy_480 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_477 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_480] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_477 h))).fv)
      0

theorem nb090_fresh_814 (A : Class) :
    (nb090_alpha_dummy_521 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_517 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_521] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_517 A))).fv)
      0

theorem nb090_fresh_815 (h : Var) :
    (nb090_alpha_dummy_522 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_519 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_522] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_519 h))).fv)
      0

theorem nb090_fresh_816 (A : Class) :
    (nb090_alpha_dummy_557 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_553 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_557] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_553 A))).fv)
      0

theorem nb090_fresh_817 (h : Var) :
    (nb090_alpha_dummy_558 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_555 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_558] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_555 h))).fv)
      0

theorem nb090_fresh_818 (A : Class) :
    (nb090_alpha_dummy_593 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_589 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_593] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_589 A))).fv)
      0

theorem nb090_fresh_819 (h : Var) :
    (nb090_alpha_dummy_594 h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_591 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_594] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_591 h))).fv)
      0

theorem nb090_fresh_820 (A : Class) :
    (nb090_alpha_dummy_629 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_625 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_629] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_625 A))).fv)
      0

theorem nb090_fresh_821 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_630 v u h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_630] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_627 v u h))).fv)
      0

theorem nb090_fresh_822 (A : Class) :
    (nb090_alpha_dummy_673 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_669 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_673] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_669 A))).fv)
      0

theorem nb090_fresh_823 (u : Var) :
    (nb090_alpha_dummy_674 u) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_671 u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_674] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_671 u))).fv)
      0

theorem nb090_fresh_824 (A : Class) :
    (nb090_alpha_dummy_727 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_723 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_727] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_723 A))).fv)
      0

theorem nb090_fresh_825 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_728 v u h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_728] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_725 v u h))).fv)
      0

theorem nb090_fresh_826 (A : Class) :
    (nb090_alpha_dummy_757 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_753 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_757] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_753 A))).fv)
      0

theorem nb090_fresh_827 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_758 v u h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_758] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_755 v u h))).fv)
      0

theorem nb090_fresh_828 (A : Class) :
    (nb090_alpha_dummy_797 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_793 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_797] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_793 A))).fv)
      0

theorem nb090_fresh_829 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_798 v u h) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_798] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_795 v u h))).fv)
      0

theorem nb090_fresh_830 (A : Class) :
    (nb090_alpha_dummy_847 A) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_843 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_847] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_843 A))).fv)
      0

theorem nb090_fresh_831 (v : Var) :
    (nb090_alpha_dummy_848 v) ∉
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_845 v))).fv) :=
  by
  simpa only [nb090_alpha_dummy_848] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_845 v))).fv)
      0

theorem nb090_fresh_832 (A : Class) :
    (nb090_alpha_dummy_653 A) ∉
      (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_653] using
    freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0

theorem nb090_fresh_833 (A : Class) :
    (nb090_alpha_dummy_827 A) ∉
      (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_827] using
    freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0

theorem nb090_fresh_834 (u : Var) :
    (nb090_alpha_dummy_654 u) ∉ (((syn_c1st)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090_alpha_dummy_654] using
    freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_835 (v : Var) :
    (nb090_alpha_dummy_828 v) ∉ (((syn_c1st)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_828] using
    freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_836 (A : Class) :
    (nb090_alpha_dummy_283 A) ∉
      (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_283] using
    freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0

theorem nb090_fresh_837 (A : Class) :
    (nb090_alpha_dummy_373 A) ∉
      (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_373] using
    freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0

theorem nb090_fresh_838 (u : Var) :
    (nb090_alpha_dummy_284 u) ∉ (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090_alpha_dummy_284] using
    freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_839 (v : Var) :
    (nb090_alpha_dummy_374 v) ∉ (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_374] using
    freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_840 (A : Class) :
    (nb090_alpha_dummy_503 A) ∉ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_503] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0

theorem nb090_fresh_841 (A : Class) :
    (nb090_alpha_dummy_504 A) ∉ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_504] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part013`. -/


section

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

theorem nb090_distinct_842 (A : Class) :
    (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_504 A) := by
  simpa only [nb090_alpha_dummy_503, nb090_alpha_dummy_504] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_fresh_843 (A : Class) :
    (nb090_alpha_dummy_423 A) ∉
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_423] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      0

theorem nb090_fresh_844 (A : Class) :
    (nb090_alpha_dummy_424 A) ∉
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_424] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      1

theorem nb090_fresh_845 (A : Class) :
    (nb090_alpha_dummy_425 A) ∉
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_425] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      2

theorem nb090_distinct_846 (A : Class) :
    (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_424 A) := by
  simpa only [nb090_alpha_dummy_423, nb090_alpha_dummy_424] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_847 (A : Class) :
    (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_425 A) := by
  simpa only [nb090_alpha_dummy_423, nb090_alpha_dummy_425] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_848 (A : Class) :
    (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_425 A) := by
  simpa only [nb090_alpha_dummy_424, nb090_alpha_dummy_425] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_849 (A : Class) :
    (nb090_alpha_dummy_243 A) ∉
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb090_alpha_dummy_243] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_850 (A : Class) :
    (nb090_alpha_dummy_244 A) ∉
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb090_alpha_dummy_244] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_851 (A : Class) :
    (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_244 A) := by
  simpa only [nb090_alpha_dummy_243, nb090_alpha_dummy_244] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_fresh_852 (h : Var) :
    (nb090_alpha_dummy_505 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_505] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 0

theorem nb090_fresh_853 (h : Var) :
    (nb090_alpha_dummy_506 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_506] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 1

theorem nb090_distinct_854 (h : Var) :
    (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_506 h) := by
  simpa only [nb090_alpha_dummy_505, nb090_alpha_dummy_506] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_855 (h : Var) :
    (nb090_alpha_dummy_426 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_426] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0

theorem nb090_fresh_856 (h : Var) :
    (nb090_alpha_dummy_427 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_427] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1

theorem nb090_fresh_857 (h : Var) :
    (nb090_alpha_dummy_428 h) ∉
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_428] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2

theorem nb090_distinct_858 (h : Var) :
    (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_427 h) := by
  simpa only [nb090_alpha_dummy_426, nb090_alpha_dummy_427] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb090_distinct_859 (h : Var) :
    (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_428 h) := by
  simpa only [nb090_alpha_dummy_426, nb090_alpha_dummy_428] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb090_distinct_860 (h : Var) :
    (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_428 h) := by
  simpa only [nb090_alpha_dummy_427, nb090_alpha_dummy_428] using
    (freshVar_injective
      (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb090_fresh_861 (h : Var) :
    (nb090_alpha_dummy_245 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_245] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_862 (h : Var) :
    (nb090_alpha_dummy_246 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_246] using
    freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_863 (h : Var) :
    (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_246 h) := by
  simpa only [nb090_alpha_dummy_245, nb090_alpha_dummy_246] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_864 (A : Class) :
    (nb090_alpha_dummy_047 A) ∉
      (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb090_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb090_fresh_865 (h : Var) :
    (nb090_alpha_dummy_048 h) ∉
      (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb090_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0

theorem nb090_fresh_866 (A : Class) :
    (nb090_alpha_dummy_421 A) ∉
      (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb090_alpha_dummy_421] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb090_fresh_867 (h : Var) :
    (nb090_alpha_dummy_422 h) ∉
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb090_alpha_dummy_422] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb090_fresh_868 (A : Class) :
    (nb090_alpha_dummy_009 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_869 (v : Var) (u : Var) :
    (nb090_alpha_dummy_010 v u) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_870 (A : Class) :
    (nb090_alpha_dummy_061 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_061] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_871 (h : Var) :
    (nb090_alpha_dummy_062 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_872 (A : Class) :
    (nb090_alpha_dummy_097 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_097] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_873 (h : Var) :
    (nb090_alpha_dummy_098 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_098] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_874 (A : Class) :
    (nb090_alpha_dummy_139 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_875 (h : Var) :
    (nb090_alpha_dummy_140 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_140] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_876 (A : Class) :
    (nb090_alpha_dummy_175 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_175] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_877 (h : Var) :
    (nb090_alpha_dummy_176 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_176] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_878 (A : Class) :
    (nb090_alpha_dummy_211 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_211] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_879 (h : Var) :
    (nb090_alpha_dummy_212 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_212] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_880 (A : Class) :
    (nb090_alpha_dummy_251 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_251] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_881 (h : Var) :
    (nb090_alpha_dummy_252 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_252] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_882 (A : Class) :
    (nb090_alpha_dummy_295 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_295] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_883 (u : Var) :
    (nb090_alpha_dummy_296 u) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_296] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_884 (A : Class) :
    (nb090_alpha_dummy_341 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_341] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_885 (h : Var) :
    (nb090_alpha_dummy_342 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_342] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_886 (A : Class) :
    (nb090_alpha_dummy_385 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_385] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_887 (v : Var) :
    (nb090_alpha_dummy_386 v) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_386] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_888 (A : Class) :
    (nb090_alpha_dummy_435 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_435] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_889 (h : Var) :
    (nb090_alpha_dummy_436 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_436] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_890 (A : Class) :
    (nb090_alpha_dummy_471 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_471] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_891 (h : Var) :
    (nb090_alpha_dummy_472 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_472] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_892 (A : Class) :
    (nb090_alpha_dummy_513 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_513] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_893 (h : Var) :
    (nb090_alpha_dummy_514 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_514] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_894 (A : Class) :
    (nb090_alpha_dummy_549 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_549] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_895 (h : Var) :
    (nb090_alpha_dummy_550 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_550] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_896 (A : Class) :
    (nb090_alpha_dummy_585 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_585] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_897 (h : Var) :
    (nb090_alpha_dummy_586 h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_586] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_898 (A : Class) :
    (nb090_alpha_dummy_621 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_621] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_899 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_622 v u h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h)
              (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
                (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_622] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h)
              (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
                (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_900 (A : Class) :
    (nb090_alpha_dummy_665 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_665] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_901 (u : Var) :
    (nb090_alpha_dummy_666 u) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_666] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_902 (A : Class) :
    (nb090_alpha_dummy_703 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_041 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_042 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_703] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_041 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_042 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_903 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_704 v u h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
              (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_704] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
              (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_904 (A : Class) :
    (nb090_alpha_dummy_719 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_719] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_905 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_720 v u h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h)
              (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
                (Class.cv (nb090_alpha_dummy_708 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_720] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h)
              (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
                (Class.cv (nb090_alpha_dummy_708 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_906 (A : Class) :
    (nb090_alpha_dummy_789 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_789] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_907 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_790 v u h) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h)
              (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
                (Class.cv (nb090_alpha_dummy_778 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_790] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h)
              (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
                (Class.cv (nb090_alpha_dummy_778 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_908 (A : Class) :
    (nb090_alpha_dummy_839 A) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_839] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_909 (v : Var) :
    (nb090_alpha_dummy_840 v) ∉
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_840] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb090_fresh_910 (A : Class) :
    (nb090_alpha_dummy_029 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv)
      0

theorem nb090_fresh_911 (v : Var) (u : Var) :
    (nb090_alpha_dummy_030 v u) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv)
      0

theorem nb090_fresh_912 (A : Class) :
    (nb090_alpha_dummy_081 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_081] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv)
      0

theorem nb090_fresh_913 (h : Var) :
    (nb090_alpha_dummy_082 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_082] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv)
      0

theorem nb090_fresh_914 (A : Class) :
    (nb090_alpha_dummy_117 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_117] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv)
      0

theorem nb090_fresh_915 (h : Var) :
    (nb090_alpha_dummy_118 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_118] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv)
      0

theorem nb090_fresh_916 (A : Class) :
    (nb090_alpha_dummy_159 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_159] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv)
      0

theorem nb090_fresh_917 (h : Var) :
    (nb090_alpha_dummy_160 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_160] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv)
      0

theorem nb090_fresh_918 (A : Class) :
    (nb090_alpha_dummy_195 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_195] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv)
      0

theorem nb090_fresh_919 (h : Var) :
    (nb090_alpha_dummy_196 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_196] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv)
      0

theorem nb090_fresh_920 (A : Class) :
    (nb090_alpha_dummy_231 A) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_231] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv)
      0

theorem nb090_fresh_921 (h : Var) :
    (nb090_alpha_dummy_232 h) ∉
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_232] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
